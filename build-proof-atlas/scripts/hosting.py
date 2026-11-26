"""Read or record a paper's hosting choice, or publish its reviewed commit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from atlas import atomic


def command(args, cwd, check=True):
    return subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=check)


def exists(endpoint, root):
    result = command(["gh", "api", endpoint, "--silent"], root, check=False)
    if result.returncode == 0:
        return True
    if "HTTP 404" in result.stderr:
        return False
    raise ValueError(result.stderr.strip())


def verify_proof_inputs(root, commit, project):
    """Check the blobs that will be deployed, even while authors edit the worktree."""
    actual = {}
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=root,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as reader:
        for claim, work in project.get("work", {}).items():
            changed = []
            for path, expected in work.get("checked_inputs", {}).items():
                if any(c in path for c in "\r\n\0"):
                    raise ValueError(f"Invalid proof input path for {claim}")
                if path not in actual:
                    reader.stdin.write(f"{commit}:{path}\n".encode("utf-8"))
                    reader.stdin.flush()
                    header = reader.stdout.readline().rstrip(b"\n")
                    if header.endswith(b" missing"):
                        actual[path] = None
                    else:
                        _, kind, size = header.split()
                        data = reader.stdout.read(int(size))
                        if reader.stdout.read(1) != b"\n" or len(data) != int(size):
                            raise ValueError("Incomplete Git object while checking proof inputs")
                        actual[path] = hashlib.sha256(data).hexdigest() if kind == b"blob" else None
                if expected != actual[path]:
                    changed.append(path)
            if changed:
                detail = f"{claim} has missing or changed committed proof inputs: " + ", ".join(changed)
                if work.get("status") == "closed":
                    raise ValueError(detail)
                print(detail, file=sys.stderr)
        reader.stdin.close()


def publish(root, choice):
    url = choice.get("repository", "")
    match = re.fullmatch(r"https://github\.com/([\w.-]+/[\w.-]+)", url)
    if not match or choice.get("visibility") not in ("public", "private"):
        raise ValueError("Record the approved GitHub destination and visibility first")
    repo = match[1]
    def git(*args):
        return command(["git", *args], root).stdout.strip()
    if Path(git("rev-parse", "--show-toplevel")).resolve() != root:
        raise ValueError("Publish from the paper repository root")
    if git("branch", "--show-current") != "main":
        raise ValueError("Commit the reviewed project on main before publishing")
    commit = git("rev-parse", "HEAD")
    committed = json.loads(subprocess.check_output(["git", "show", commit + ":project.json"], cwd=root))
    if committed.get("hosting") != choice:
        raise ValueError("Commit the selected hosting destination before publishing")
    if choice.get("site"):
        git("cat-file", "-e", commit + ":.github/workflows/pages.yml")
    verify_proof_inputs(root, commit, committed)
    remotes = git("remote").splitlines()
    if "origin" in remotes:
        for name in git("remote", "get-url", "--push", "--all", "origin").splitlines():
            expected = {url.casefold(), f"git@github.com:{repo}".casefold()}
            if name.removesuffix(".git").casefold() not in expected:
                raise ValueError("The origin push URL differs from the saved hosting choice")
    endpoint = "repos/" + repo
    if exists(endpoint, root):
        visibility = command(["gh", "api", endpoint, "--jq", ".visibility"], root).stdout.strip()
        if visibility != choice["visibility"]:
            raise ValueError("Existing repository visibility differs from the saved choice")
    else:
        command(["gh", "repo", "create", repo, "--"+choice["visibility"]], root)
    if "origin" not in remotes:
        git("remote", "add", "origin", url+".git")
    git("push", "origin", commit + ":refs/heads/main")
    git("config", "branch.main.remote", "origin")
    git("config", "branch.main.merge", "refs/heads/main")
    if choice.get("site"):
        if not exists(endpoint+"/pages", root):
            command(["gh", "api", "-X", "POST", endpoint+"/pages", "-f", "build_type=workflow"], root)
        mode = command(["gh", "api", endpoint+"/pages", "--jq", ".build_type"], root).stdout.strip()
        if mode != "workflow":
            raise ValueError("Existing Pages site uses a different publishing source; review it before switching")
        command(["gh", "workflow", "run", "pages.yml", "--repo", repo, "--ref", "main"], root)
    print(url)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--github", metavar="OWNER/REPO")
    actions.add_argument("--local", action="store_true")
    actions.add_argument("--lean-ci", action="store_true", help="Record approval and install the Lean verification workflow")
    actions.add_argument("--no-lean-ci", action="store_true", help="Record a local-checks-only choice")
    actions.add_argument("--publish", action="store_true", help="Publish the committed paper project to its approved GitHub destination")
    parser.add_argument("--lean-ci-level", choices=["standard", "paranoid"],
                        help="Lean CI verification tier: standard (default) or paranoid (Challenge/Solution + Comparator / lean4checker / multi-kernel)")
    parser.add_argument("--visibility", choices=["public", "private"])
    pages = parser.add_mutually_exclusive_group()
    pages.add_argument("--pages", action="store_true")
    pages.add_argument("--no-pages", action="store_true")
    args = parser.parse_args()
    root = args.project.resolve()
    path = root/"project.json"
    project = json.loads(path.read_text(encoding="utf-8-sig"))
    choice = project.get("hosting") or {"decision":"pending"}
    if (args.visibility or args.pages or args.no_pages) and not args.github:
        parser.error("Use the GitHub options with --github")
    if args.lean_ci_level and (args.github or args.local or args.no_lean_ci or args.publish):
        parser.error("Use --lean-ci-level with --lean-ci, or alone once Lean CI is enabled")
    if args.publish:
        publish(root, choice)
        return
    if args.github:
        if not re.fullmatch(r"[A-Za-z0-9][\w.-]*/[A-Za-z0-9][\w.-]*", args.github):
            parser.error("Expected OWNER/REPO")
        if not args.visibility or not (args.pages or args.no_pages):
            parser.error("Supply the agreed --visibility and --pages or --no-pages")
        url = "https://github.com/"+args.github
        choice = dict(choice) if choice.get("repository", "").casefold() == url.casefold() else {}
        choice.update(decision="github", repository=url, visibility=args.visibility)
        if args.pages:
            owner, repo = args.github.split("/")
            choice.setdefault("site", f"https://{owner.lower()}.github.io/" +
                              ("" if repo.lower() == owner.lower()+".github.io" else repo+"/"))
        else:
            choice.pop("site", None)
            choice.pop("activity_url", None)
    if args.local:
        choice = {"decision":"local"}
    if args.lean_ci or args.no_lean_ci or args.lean_ci_level:
        if not choice.get("repository"):
            parser.error("Choose a GitHub repository first")
        workflow = root / ".github/workflows/verify-lean.yml"
        template = Path(__file__).resolve().parents[1] / "references/verify-lean.yml"
        if args.lean_ci:
            if workflow.exists() and workflow.read_text(encoding="utf-8") != template.read_text(encoding="utf-8"):
                parser.error("Existing verify-lean.yml differs. Integrate per-claim verification into that workflow and record the decision.")
            workflow.parent.mkdir(parents=True, exist_ok=True)
            atomic(workflow, template.read_bytes())
            choice["lean_ci"] = "enabled"
            choice["lean_ci_level"] = args.lean_ci_level or choice.get("lean_ci_level") or "standard"
        elif args.lean_ci_level:
            if choice.get("lean_ci") != "enabled":
                parser.error("Enable GitHub Lean verification with --lean-ci first, or pass --lean-ci --lean-ci-level")
            if not workflow.exists():
                workflow.parent.mkdir(parents=True, exist_ok=True)
                atomic(workflow, template.read_bytes())
            choice["lean_ci_level"] = args.lean_ci_level
        elif workflow.exists():
            parser.error("An existing verification workflow is installed. Review its triggers before disabling it.")
        else:
            choice["lean_ci"] = "declined"
            choice.pop("lean_ci_level", None)
    if args.github or args.local or args.lean_ci or args.no_lean_ci or args.lean_ci_level:
        project["hosting"] = choice
        atomic(path, (json.dumps(project, indent=2, ensure_ascii=False)+"\n").encode())
    print(json.dumps(choice, indent=2))
    if choice.get("decision") == "pending":
        print("Ask the author where to host this paper's explorer and dashboard. Continue local work while waiting.")
    elif choice.get("repository") and not choice.get("lean_ci"):
        print("Ask whether GitHub Actions should independently verify the Lean claims and publish per-claim evidence.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as exc:
        sys.exit((exc.stderr or "").strip() or str(exc))
    except (OSError, ValueError) as exc:
        sys.exit(str(exc))
