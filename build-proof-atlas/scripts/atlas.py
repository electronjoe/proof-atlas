"""Build a local, read-only view of an author's checkpoint records (Python 3.9+)."""
import author_review as reviews
import review_web
import manuscript_edits
import argparse
import hashlib
import html
import json
import os
import re
import shutil
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote, urlsplit

NO_EXAMPLE = "No checked example shows the hypotheses can hold"


def esc(value):
    return html.escape(str(value), quote=True)


def edition_reference(project):
    # Older projects included the PDF caption in their edition text.
    edition = project["edition"].removesuffix(" \u00b7 local manuscript and PDF")
    label = esc(edition)
    publication = project.get("publication")
    if publication:
        url = urlsplit(publication)
        if url.scheme not in ("http", "https") or not url.hostname:
            raise ValueError("project.json: publication must be an absolute HTTP(S) URL")
        label = f'<a href="{esc(publication)}">{label or "Publication"}</a>'
    return label


def edition_links(project):
    return " &middot; ".join(filter(None, (edition_reference(project), '<a href="manuscript.pdf">Manuscript PDF</a>')))


def paper_citation(project):
    authors = ", ".join(esc(author) for author in project.get("authors", []))
    title = "<cite>" + esc(project["title"]) + "</cite>"
    edition = " ".join(filter(None, (edition_reference(project), esc(project.get("citation_details", "")))))
    return ". ".join(filter(None, (authors, title, edition))) + "."


def atomic(path, data):
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as temp:
        temp.write(data)
    os.replace(temp.name, path)


def local(root, name):
    path = (root / name).resolve()
    if not path.is_relative_to(root):
        raise ValueError(f"Path outside project: {name}")
    return path


def read_source(root, record):
    data = local(root, record["path"]).read_bytes()
    if hashlib.sha256(data).hexdigest() != record["sha256"]:
        raise ValueError(f"{record['path']}: source changed; review edition, anchors and checkpoints")
    return data


def inventory(text, filename, envs):
    # Blank comments in place so offsets still point into the original source.
    clean = re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m[0]), text)
    names = "|".join(re.escape(name) for name in envs)
    opening = re.compile(r"\\begin\{(" + names + r")\}(?:\s*\[([^\]]*)\])?")
    for start in opening.finditer(clean):
        kind, title = start.groups()
        end_tag = r"\end{" + kind + "}"
        end = clean.find(end_tag, start.end())
        line = text.count("\n", 0, start.start()) + 1
        if end < 0:
            raise ValueError(f"{filename}:{line}: missing {end_tag}")
        bind = re.match(r"\s*\\label\{([^}]+)\}", clean[start.end():end])
        if not bind:
            raise ValueError(f"{filename}:{line}: assign a stable source mapping for this unlabeled claim")
        stop = end + len(end_tag)
        proof = re.match(r"\s*\\begin\{proof\}.*?\\end\{proof\}", clean[stop:], re.S)
        if proof:
            stop += proof.end()
        title = re.sub(r"\s*\\cite\{[^}]+\}", "", title or bind[1])
        yield dict(id=bind[1], kind=kind, title=title, file=filename, line=line,
                   excerpt=text[start.start():stop], adjacent_proof=bool(proof))


def claim_url(label):
    return "proofs/index.html#/claim/" + quote(label, safe="")


def masthead(project, first):
    claim = claim_url(first)
    graph = "proofs/index.html#/graph/" + quote(first, safe="")
    return (f'<header class="mast"><a class="wordmark" href="index.html">Proof Atlas<span>.</span></a>'
            f'<nav aria-label="Project"><a data-nav="home" href="index.html">Overview</a>'
            f'<a data-nav="reader" href="{claim}">Claim reader</a><a data-nav="graph" id="graph-nav" href="{graph}">Dependency graph</a>'
            '<a data-nav="progress" href="progress.html">Dashboard</a> <a href="review.html">Author review</a> <a href="edits.html">Manuscript edits</a></nav>'
            '<details id="about-atlas" class="citation"><summary>Paper &amp; citation</summary><div>'
            f'<h2>About this atlas</h2><p>{paper_citation(project)}</p>'
            f'<p>{esc(project.get("paper_overview", ""))}</p><p><a href="manuscript.pdf">Manuscript PDF</a></p>'
            f'<h3>Read a proof</h3><p><a href="{claim}?view=english">Plain English</a> gives the claim and proof idea. '
            f'<a href="{claim}?view=paper">Paper</a> opens the manuscript. <a href="{claim}?view=lamport">Lamport proof</a> '
            f'breaks the argument into steps. <a href="{claim}?view=lean">Lean</a> shows the formal sources and check records.</p>'
            f'<p>The <a href="{graph}">dependency graph</a> points from prerequisite to result. Whole paper includes isolated claims. '
            'The <a href="progress.html">progress dashboard</a> tracks active work, checked claims, and verification evidence.</p><a href="guide.html">How to use this atlas</a>'
            '</div></details></header>')


def featured_result(root, output, folio, entries):
    selected = folio.get("featured_claim")
    if selected and not any(c["id"] == selected for c in entries):
        raise ValueError("folio.featured_claim is absent from the inventory")
    if not entries:
        return "<p>No claims imported yet.</p>"
    c = next((c for c in entries if c["id"] == selected), entries[0])
    url = claim_url(c["id"])
    summary = folio.get("blurb") or c.get("summary") or c.get("sketch") or ""
    image = ""
    fig = folio.get("figure")
    if fig:
        path = local(root, fig["path"])
        if (path.suffix.lower() not in {".png", ".jpg", ".jpeg", ".webp"} or not fig.get("alt")
                or not fig.get("caption") or type(fig.get("page")) is not int or fig["page"] < 1):
            raise ValueError("folio.figure needs a raster image, alt text, caption and one-based manuscript page")
        content = path.read_bytes()
        name = "folio-" + hashlib.sha256(content).hexdigest()[:16] + path.suffix.lower()
        atomic(output / name, content)
        image = (f'<figure><a href="manuscript.pdf#page={fig["page"]}"><img src="{name}" alt="{esc(fig["alt"])}"></a>'
                 f'<figcaption>{esc(fig["caption"])} <a href="manuscript.pdf#page={fig["page"]}">Manuscript, p. {fig["page"]}</a></figcaption></figure>')
    return (f'<section class="feature"><div><small>Featured result · {esc(c["reference"])}</small>'
            f'<h2><a href="{url}">{esc(c["title"])}</a></h2><p class="feature-summary">{esc(summary)}</p>'
            f'<a class="read-proof" href="{url}">Read the claim →</a></div>{image}</section>')


def page(title, mast, body, watch=""):
    return (f'<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" '
            f'content="width=device-width,initial-scale=1"><title>{esc(title)} | Proof Atlas</title>'
            '<link rel="stylesheet" href="style.css"><body class="dashboard">'
            + mast + '<main>' + body + '</main>' + watch + '</body></html>').encode()


def proof_work_description(project, claims, *, closed_results=None):
    scope = project.get("proof_work")
    if scope is None:
        return "Proof-work authorization has not been recorded."
    mode = scope["mode"]
    if mode == "paper":
        total = sum(claim["kind"] != "conjecture" for claim in claims)
        if total and closed_results == total:
            text = "Paper-wide proof work complete. All stated results are closed."
        else:
            text = f"Paper-wide. Continue through all {total} stated results, including their prerequisites. Track conjectures separately."
    elif mode == "claim":
        selected = next((c for c in claims if c["id"] == scope.get("claim")), None)
        if selected is None:
            raise ValueError("proof_work.claim must identify a manuscript claim")
        text = f"One claim. Work through {selected['title']} ({selected['id']}) and its prerequisites, then stop for the author."
    else:
        raise ValueError("proof_work.mode must be paper or claim")
    if scope.get("paused"):
        return "Paused by the author. Saved scope: " + text
    return text


def github_verification(project, receipt_path, commit):
    if not receipt_path or project.get("hosting", {}).get("lean_ci") != "enabled":
        return None
    data = json.loads(Path(receipt_path).read_bytes())
    repository = project["hosting"]["repository"]
    if (not re.fullmatch(r"[0-9a-f]{40}", commit or "") or data.get("commit") != commit
            or not re.fullmatch(r"[\w.-]+/[\w.-]+", data.get("repository", ""))
            or repository.casefold() != ("https://github.com/" + data["repository"]).casefold()
            or not all(type(data.get(k)) is int and data[k] > 0 for k in ("run_id", "attempt"))):
        return None
    return data


def manuscript_claims(root, p):
    claims = []
    for source in p["tex"]:
        claims.extend(inventory(read_source(root, source).decode("utf-8-sig"), source["path"], p["environments"]))
    return claims


def current_audit(root, cid, w):
    """The closure's receipt, provided the audited sources are unchanged."""
    if w.get("status") != "closed":
        raise ValueError(f"{cid}: only a closed claim with a Lean audit can be approved")
    audit = json.loads(local(root, w["closure"]["audit"]).read_bytes())
    for path, digest in w.get("checked_inputs", {}).items():
        if not local(root, path).is_file() or hashlib.sha256(local(root, path).read_bytes()).hexdigest() != digest:
            raise ValueError(f"{cid}: {path} changed since the Lean check; recheck the claim first")
    closure = w["closure"]
    expected = {(Path(closure["package"])/name).as_posix(): h for name,h in audit["checked_inputs"].items()}
    if (not expected or expected != w.get("checked_inputs") or
        any(audit[k] != closure[k] for k in ("expected","declaration")) or
        set(audit["axioms"]) - {"propext","Classical.choice","Quot.sound"}):
        raise ValueError("Inconsistent audit receipt")
    return audit


def current_statement_audit(root, cid, w):
    """Return `(audit, proof_checked)` for either a closed claim or a Gate 1 statement check."""
    if w.get("status") == "closed":
        return current_audit(root, cid, w), True
    sc = w.get("statement_check")
    if not sc:
        raise ValueError(f"{cid}: only a closed claim or a drafted claim with a statement audit can be compared")
    audit = json.loads(local(root, sc["audit"]).read_bytes())
    package = Path(sc["package"])
    checked_inputs = audit.get("checked_inputs") or {}
    if (not audit.get("statement_only") or not checked_inputs or not audit.get("statements") or
            audit.get("expected") != sc.get("expected") or
            not audit.get("statement", {}).get("sha256") or
            set(audit.get("axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}):
        raise ValueError(f"{cid}: inconsistent statement audit receipt")
    for name, digest in checked_inputs.items():
        path = (package / name).as_posix()
        if not local(root, path).is_file() or hashlib.sha256(local(root, path).read_bytes()).hexdigest() != digest:
            raise ValueError(f"{cid}: {path} changed since the statement check; rerun audit_lean.py --statement-only")
    return audit, False


def statement_defaults(audit):
    """The receipt's default-value uses in the statement's definitions, each with its meaning."""
    from audit_lean import default_meaning  # audit_lean imports atlas through check_lean
    # The scanner groups uses by declaration, operation and type. Source lines may move.
    return [dict(use, meaning=default_meaning(use),
                 id=reviews.digest([use["constant"], use["construct"], use.get("type", "")]))
            for use in (audit or {}).get("defaults", [])]


def build_local(root):
    """Keep published evidence during local review when it matches the checkout."""
    import subprocess
    receipt = root/"dist/logs/lean-verification.json"
    options = {}
    if receipt.is_file():
        try:
            data = json.loads(receipt.read_bytes())
            proc = subprocess.run(["git", "-c", "safe.directory="+root.as_posix(), "rev-parse", "HEAD"],
                                  cwd=root, capture_output=True, text=True)
            if proc.returncode == 0 and proc.stdout.strip() == data.get("commit"):
                previous = reviews.read(root/"dist/checkpoint.json", {})
                artifact = previous.get("artifact_id") if previous.get("evidence_commit")==data["commit"] else None
                options = dict(ci_receipt=receipt, commit=data["commit"], artifact_id=artifact)
        except (OSError, ValueError):
            pass
    return build(root, **options)


def witness_plan(project, work, witness):
    mode = work.get("witness_search", project.get("witness_search", "available"))
    if mode not in ("available", "skip", "pursue"):
        raise ValueError("witness_search must be available, skip, or pursue")
    missing = work.get("witness_missing_result")
    if witness:
        action = "reuse checked witness"
    elif mode == "skip":
        action = "skip search"
    elif missing:
        action = "pursue missing result" if mode == "pursue" else "defer missing result"
    else:
        action = "try a concrete example or existing lemma"
    plan = {"mode": mode, "action": action}
    if missing and not witness:
        plan["missing_result"] = missing
    return plan


def review_work(root, labels=(), *, require_ci=False, ci_receipt=None):
    """List actionable review findings. Optional approvals are never obligations."""
    import subprocess
    project = reviews.read(root/"project.json", {})
    claims = {c["id"]: c for c in manuscript_claims(root, project)}
    if set(labels) - claims.keys():
        raise ValueError("Unknown review-work claim")
    selected = list(dict.fromkeys(labels or claims))
    report = {"scope": project.get("proof_work"), "agent_tasks": [], "author_questions": [],
              "uncommitted_delivery_files": [], "ci_pending": [], "witness_search": {}}
    ci = None
    if require_ci:
        if project.get("hosting", {}).get("lean_ci") != "enabled":
            raise ValueError("--require-ci requires GitHub verification enabled for this atlas")
        git = ["git","-c","safe.directory="+root.as_posix()]
        sha = subprocess.check_output([*git,"rev-parse","HEAD"],cwd=root,text=True).strip()
        paths = {"project.json","comparisons.json"}
        for cid in selected:
            work = project.get("work",{}).get(cid,{})
            if work.get("status")=="closed":
                paths.update([work["closure"]["audit"],work["run_log"]])
        changes = subprocess.check_output([*git,"status","--porcelain","--untracked-files=all","--",*sorted(paths)],
                                          cwd=root,text=True)
        report["uncommitted_delivery_files"] = changes.splitlines()
        path = Path(ci_receipt or root/"dist/logs/lean-verification.json")
        ci = github_verification(project, path, sha) if path.is_file() else None
        report["commit"] = sha
    for cid in selected:
        work = project.get("work", {}).get(cid, {})
        packet = reviews.get_packet(root,cid)
        if claims[cid]["kind"] != "conjecture":
            report["witness_search"][cid] = witness_plan(project, work, packet["witness"])
        needs_gate1_review = (work.get("status") != "closed" and packet["statement_checked"]
                              and not packet["disputed"] and "analysis" not in packet["view"])
        if packet["disputed"] or (work.get("status")=="closed" and packet["actor"]=="Proof agent") or needs_gate1_review:
            key = "author_questions" if packet["actor"]=="Author" else "agent_tasks"
            report[key].append(dict(claim=cid, issue=packet["issue"], next=packet["next"]))
        if require_ci and work.get("status")=="closed":
            evidence = (ci or {}).get("claims", {}).get(cid, {})
            digest = hashlib.sha256(local(root,work["closure"]["audit"]).read_bytes()).hexdigest()
            if not packet["checked"] or evidence.get("audit_sha256")!=digest or (
                    packet["view"]["bindings"]["statement"] and
                    evidence.get("statement_sha256")!=packet["view"]["bindings"]["statement"]):
                report["ci_pending"].append(cid)
    book, edits = manuscript_edits.inventory(root)
    for key,item in edits.items():
        if item["claim"] in selected and key not in book.get("cleared",{}) and item.get("status")=="Draft requested":
            report["agent_tasks"].append(dict(claim=item["claim"], edit=key, next="Prepare the requested manuscript draft."))
    return report


def build(root, *, ci_receipt=None, commit=None, artifact_id=None):
    p = json.loads((root / "project.json").read_text(encoding="utf-8-sig"))
    ci = github_verification(p, ci_receipt, commit)
    if p["schema_version"] != 1 or not p["environments"]:
        raise ValueError("project.json: expected schema version 1 and theorem environments")
    claims = manuscript_claims(root, p)
    comparisons = reviews.read(root/"comparisons.json", {})
    review_entries = []
    (root/"dist"/"review").mkdir(parents=True,exist_ok=True)
    by_id = {c["id"]: c for c in claims}
    work = p.get("work", {})
    if len(by_id) != len(claims):
        raise ValueError("duplicate claim label across manuscript sources")
    if "claim_order" in p:
        order = p["claim_order"]
        if len(order) != len(claims) or set(order) != set(by_id):
            raise ValueError("claim_order must list every manuscript claim exactly once")
        claims = [by_id[label] for label in order]
    if work.keys() - by_id.keys() or (p.get("focus") and p["focus"] not in by_id):
        raise ValueError("checkpoint or focus refers to an unknown claim label")
    pdf = read_source(root, p["pdf"])
    output = root / "dist"
    output.mkdir(exist_ok=True)
    materials = {}
    if p.get("reader"):
        materials = json.loads(local(root, p["reader"]).read_text(encoding="utf-8-sig"))
    notes = materials.get("claims", {})
    edges = materials.get("dependencies", [])
    if notes.keys() - by_id.keys() or any(e[k] not in by_id for e in edges for k in ("claim", "prerequisite")):
        raise ValueError("reader: claim or dependency refers to an unknown label")
    assets = Path(__file__).resolve().parents[1] / "assets"
    rows, entries, log_links = [], [], {}
    stale = {}
    unchecked = []
    no_example = []
    subproof_lists = {}
    closed_results = 0
    for c in claims:
        cid = c["id"]
        w = work.get(cid, {})
        m = notes.get(cid, {})
        status = w.get("status", "open")
        if status not in {"open", "drafted", "blocked", "attempted", "closed"}:
            raise ValueError(f"{cid}: unsupported checkpoint status {status}")
        entry = {**c, **m, **w}
        if status == "closed":
            closure = w["closure"]
            receipt = local(root, closure["audit"]).read_bytes()
            audit = json.loads(receipt)
            package = local(root, closure["package"])
            relative = package.relative_to(root)
            inputs = {(relative / name).as_posix(): digest for name, digest in audit["checked_inputs"].items()}
            if (not inputs or inputs != w.get("checked_inputs") or not w.get("run_log") or
                not w.get("scope") or not closure.get("correspondence") or
                audit["expected"] != closure["expected"] or audit["declaration"] != closure["declaration"] or
                set(audit["axioms"]) - {"propext", "Classical.choice", "Quot.sound"} or
                any(part["status"] != "checked" for part in w.get("subproofs", []))):
                raise ValueError(f"{cid}: closure requires matching audit evidence, correspondence and resolved obligations")
            if not audit.get("statements"):
                unchecked.append(cid)
            entry["hypotheses"] = audit.get("hypotheses")
            if not audit.get("hypotheses"):
                no_example.append(cid)
            (output / "logs").mkdir(exist_ok=True)
            name = hashlib.sha256(receipt).hexdigest() + ".json"
            atomic(output / "logs" / name, receipt)
            entry["audit_log"] = "logs/" + name
        changed = [path for path, digest in w.get("checked_inputs", {}).items()
                   if not local(root, path).is_file() or hashlib.sha256(local(root, path).read_bytes()).hexdigest() != digest]
        if changed:
            stale[cid] = "Lean inputs changed since the recorded check: " + ", ".join(changed)
            entry["scope"] = stale[cid] + ". The linked log is historical."
            entry["summary"] = m.get("summary", "The paper claim is awaiting a fresh Lean check.")
            status = "awaiting recheck"
        checked = status == "closed"
        statement_audit = audit if checked else None
        statement_checked = False
        if not checked and w.get("statement_check"):
            try:
                statement_audit, _ = current_statement_audit(root, cid, w)
                statement_checked = True
                entry["hypotheses"] = statement_audit.get("hypotheses")
            except ValueError:
                statement_audit = None
        active_audit = audit if checked else statement_audit
        rd = reviews.packet(root,p,c,w,active_audit,comparisons.get(cid),reviews.history(root,cid),checked,statement_checked)
        rd["page"] = entry.get("page")
        rd["sources"] = reviews.exact_sources(root,w,active_audit) if active_audit else []
        rd["witness"] = reviews.witness_source(root,w,active_audit) if active_audit else None
        entry["defaults"] = rd["defaults"]
        if rd["axiom_profile"]:
            entry["axiom_profile"] = rd["axiom_profile"]
        if rd["external_packages"]:
            entry["external_packages"] = rd["external_packages"]
        if rd["noncomputable_constants"]:
            entry["noncomputable_constants"] = rd["noncomputable_constants"]
        unfolded = [
            {k: s[k] for k in ("name", "file", "lines", "pp_no_notation", "noncomputable") if k in s}
            for s in rd["sources"] if s.get("pp_no_notation")
        ]
        if unfolded:
            entry["unfolded_signatures"] = unfolded
        review_entries.append(rd)
        atomic(output/reviews.review_url(cid),review_web.render(rd))
        entry["status"] = "correspondence under review" if rd["disputed"] else status
        if "analysis" in rd["view"]:
            entry["differences"] = reviews.differences(rd["view"]["analysis"])
        if c["kind"] != "conjecture" and checked and not rd["disputed"]:
            closed_results += 1
        entry.setdefault("reference", c["kind"].title())
        subproofs = []
        for part in w.get("subproofs", []):
            state = part["status"]
            if state not in {"open", "attempted", "checked"}:
                raise ValueError(f"{cid}: unsupported subproof status {state}")
            if state == "checked":
                if not (part.get("declaration") and w.get("run_log") and w.get("checked_inputs")):
                    raise ValueError(f"{cid}: checked subproof requires a declaration and recorded build inputs and log")
                if changed:
                    state = "awaiting recheck"
            subproofs.append(dict(part, status=state))
        entry["subproofs"] = subproofs
        checked = status == "closed"
        has_parts = any(part["status"] == "checked" for part in subproofs)
        label = ("Open conjecture" if c["kind"] == "conjecture" and status == "open" else
                 "Lean checked" if checked else "Awaiting Lean recheck" if changed else
                 "Subproofs checked" if has_parts else
                 "Statement drafted (proof in progress)" if statement_checked else "No completed Lean check")
        verification = {"label": label}
        verification["review_url"] = reviews.review_url(cid)
        for key in ("stronger_result", "author_scope"):
            if rd[key]:
                verification[key] = rd[key]
        if rd["approved"]:
            verification.update(approval=reviews.BADGE,approved=True)
        if checked and p.get("hosting", {}).get("lean_ci") == "enabled":
            verification["remote"] = "No GitHub verification for this revision"
            verification["url"] = p["hosting"]["repository"] + "/actions/workflows/verify-lean.yml"
            record = ci["claims"].get(cid) if ci else None
            if (record and record.get("audit_sha256") == hashlib.sha256(receipt).hexdigest()
                    and all(record.get(k) == audit[k] for k in ("expected", "declaration", "toolchain"))
                    and (not audit.get("statement") or record.get("statement_sha256") == audit["statement"]["sha256"])
                    and (not audit.get("hypotheses") or record.get("hypotheses") == audit["hypotheses"]["proposition"])
                    and set(record["axioms"]) == set(audit["axioms"])):
                verification.update(remote="Machine verified on GitHub",
                                    url=f'{p["hosting"]["repository"]}/actions/runs/{ci["run_id"]}/attempts/{ci["attempt"]}',
                                    commit=ci["commit"], evidence="logs/lean-verification.json")
                if artifact_id and artifact_id > 0:
                    verification["artifact"] = f'{p["hosting"]["repository"]}/actions/runs/{ci["run_id"]}/artifacts/{artifact_id}'
        entry["verification"] = verification
        if subproofs:
            items = "".join(f'<li>{esc(part["title"])} · {esc(part["status"])}</li>' for part in subproofs)
            subproof_lists[cid] = f"<h3>Subproofs</h3><ol>{items}</ol>"
        entry["sources"] = [
            {"path": filename, "text": local(root, filename).read_text(encoding="utf-8-sig")}
            for filename in dict.fromkeys(([w["lean"]] if w.get("lean") else []) + w.get("lean_sources", []))
        ]
        if m.get("lamport"):
            entry["steps"] = local(root, m["lamport"]).read_text(encoding="utf-8-sig")
        if w.get("run_log"):
            log = local(root, w["run_log"]).read_bytes()
            name = hashlib.sha256(log).hexdigest() + ".txt"
            (output / "logs").mkdir(exist_ok=True)
            atomic(output / "logs" / name, log)
            entry["log"] = "logs/" + name
            log_links[cid] = f'<p><a href="logs/{name}">Read the recorded Lean run</a></p>'
        entries.append(entry)
        url = "proofs/index.html#/claim/" + quote(cid, safe="")
        target = ' <strong class="proof-target">Current proof target</strong>' if cid == p.get("focus") else ''
        badge = f' · <a href="{url}?view=lean">{esc(label)}</a>'
        if checked and not entry.get("hypotheses"):
            badge += f' · {NO_EXAMPLE}'
        badge += f' · <a href="{reviews.review_url(cid)}">Review this claim</a>'
        if rd["disputed"]:
            badge += f' · {esc(rd["issue"])} · {esc(rd["actor"])}: {esc(rd["next"])}'
        if entry.get("differences") is not None:
            count = len(entry["differences"])
            badge += (f' · <a href="{url}?view=paper">{count or "No"} difference{"" if count == 1 else "s"} from the paper</a>')
        if "approval" in verification:
            badge += f' · <a class="approval approved" href="{reviews.review_url(cid)}">{esc(verification["approval"])}</a>'
        elif rd.get("preapproved"):
            badge += f' · <a href="{reviews.review_url(cid)}">Statement approved (proof in progress)</a>'
        if rd["stronger_result"]:
            badge += f' · <a href="{reviews.review_url(cid)}#scope-note">Lean proves more</a>'
        if rd["author_scope"]:
            badge += f' · <a href="{reviews.review_url(cid)}#author-scope">Author’s scope note</a>'
        if "evidence" in verification:
            badge += f' <a class="verified-badge" href="{esc(verification["url"])}">&#10003; {esc(verification["remote"])}</a>'
            badge += f' · <a href="{esc(verification["evidence"])}">Verification record</a>'
            if "artifact" in verification:
                badge += (f' · <a href="{esc(verification["artifact"])}" data-artifact-record="{esc(verification["evidence"])}">'
                          'GitHub artifact (sign-in required)</a>')
        elif "remote" in verification:
            badge += f' · <a href="{esc(verification["url"])}">{esc(verification["remote"])}</a>'
        rows.append(f'<li data-claim="{esc(cid)}"><a href="{url}">{esc(entry["reference"])} · {esc(c["title"])}</a> · {esc(entry["status"])}{badge}{target}<span class="claim-activity"></span></li>')
    if ci:
        (output / "logs").mkdir(exist_ok=True)
        atomic(output / "logs/lean-verification.json", Path(ci_receipt).read_bytes())
    sources = edition_links(p)
    folio = p.get("folio", {})
    short_title = folio.get("short_title") or p["title"]
    byline = " &middot; ".join(filter(None, (", ".join(map(esc, p.get("authors", []))), sources)))
    heading = f'<header class="paper"><small>{esc(short_title)}</small><h1>Progress dashboard</h1><p>{byline}</p></header>'
    focus = p.get("focus")
    active = ""
    if focus and focus in work:
        w = work[focus]
        active = (f'<section><small>Latest saved proof checkpoint</small><h2><a href="proofs/index.html#/claim/{quote(focus, safe="")}">{esc(by_id[focus]["title"])}</a></h2>'
                  f'<p>{esc(stale.get(focus, w["step"]))}</p><p><strong>Next step</strong><br>{esc(w["next"])}</p>'
                  f'{subproof_lists.get(focus, "")}<time>Last checkpoint · {esc(w["updated"])}</time>{log_links.get(focus, "")}</section>')
    feed = p.get("hosting", {}).get("activity_url", "")
    total_results = sum(c["kind"] != "conjecture" for c in claims)
    scope = proof_work_description(p, claims, closed_results=closed_results)
    results = [e for e in entries if e["kind"] != "conjecture"]
    machine = sum("evidence" in e["verification"] for e in results)
    reviewed = sum(bool(e["verification"].get("approved")) for e in results)
    pending = f" · {machine}/{total_results} machine verified · {reviewed}/{total_results} author reviewed"
    atomic(output/"review.html",review_web.queue(review_entries))
    atomic(output/"edits.html",manuscript_edits.render(root))
    shutil.copyfile(assets/"review.css",output/"review.css")
    guide = (assets.parent/"references"/"author-guide.md").read_text(encoding="utf-8")
    sections = []
    for paragraph in guide.strip().split("\n\n"):
        tag = "h1" if paragraph.startswith("# ") else "h2" if paragraph.startswith("## ") else "p"
        content = esc(paragraph.lstrip("# ").strip())
        sections.append(f"<{tag}>" + re.sub(r"`([^`]+)`", r"<code>\1</code>", content) + f"</{tag}>")
    atomic(output/"guide.html", review_web.document("How to use this atlas","".join(sections),"./"))
    dashboard = heading + f'<section id="claim-inventory" data-feed="{esc(feed)}"><h2>Claim inventory</h2><p><strong>Authorized proof work</strong><br>{esc(scope)}</p><p><a href="guide.html">How to use this atlas</a> · <a href="review.html">Review queue</a></p><p>{closed_results} of {total_results} stated results closed{pending}</p><ol>' + "".join(rows) + '</ol></section>' + active
    payload = dict(title=p["title"], focus=focus, claims=entries, dependencies=edges, macros=materials.get("macros", {}))
    template = (assets / "explorer.html").read_text(encoding="utf-8-sig")
    packed = json.dumps(payload, ensure_ascii=False)
    first = focus or folio.get("featured_claim") or (entries[0]["id"] if entries else "")
    mast = masthead(p, first)
    feature = featured_result(root, output, folio, entries)
    contents = []
    for entry in entries:
        link = claim_url(entry["id"])
        v = entry["verification"]
        mark = (f'<a class="verified-badge" href="{esc(v["url"])}">✓ {esc(v["remote"])}</a>'
                if v.get("evidence") else f'<a class="status" href="{link}?view=lean">{esc(v["label"])}</a>')
        if "approval" in v:
            mark = f'<span class="marks">{mark}<a class="status approval approved" href="{esc(v["review_url"])}">{esc(v["approval"])}</a></span>'
        contents.append(f'<li><a class="toc-claim" href="{link}"><small>{esc(entry["reference"])}</small>'
                        f'<strong>{esc(entry["title"])}</strong></a>{mark}</li>')
    explorer = (template.replace("__MAST__", mast).replace("__TITLE__", esc(p["title"]))
                .replace("__SHORT_TITLE__", esc(short_title)).replace("__BYLINE__", byline)
                .replace("__FEATURE__", feature).replace("__COUNT__", str(len(entries)))
                .replace("__CONTENTS__", "".join(contents)))
    digest = hashlib.sha256((packed + dashboard + explorer).encode())
    for name in ("explorer.js", "explorer.css", "graph.js", "graph.css", "style.css", "live.js", "activity.js", "artifact.js"):
        digest.update((assets / name).read_bytes())
        atomic(output / name, (assets / name).read_bytes())
    version = digest.hexdigest()
    payload["revision"] = version
    packed = json.dumps(payload, ensure_ascii=False).replace("<", r"\u003c")
    for directory, base, home in ((output, "./", True), (output / "proofs", "../", False)):
        directory.mkdir(exist_ok=True)
        shell = (explorer.replace("__ENTRY__", "home" if home else "reader")
                 .replace("__HOME_HIDDEN__", "" if home else "hidden")
                 .replace("__READER_HIDDEN__", "hidden" if home else "")
                 .replace("__REVISION__", version).replace("__BASE__", base))
        atomic(directory / "index.html", shell.replace("__DATA__", packed).encode())
    shutil.copytree(assets / "dagre", output / "dagre", dirs_exist_ok=True)
    shutil.copytree(assets / "katex", output / "katex", dirs_exist_ok=True)
    watch = f'<script src="live.js" data-revision="{version}" defer></script>'
    atomic(output / "preview-status.json", b'{}')
    if not (output / "activity.json").exists():
        atomic(output / "activity.json", b'{"runs":[]}')
    atomic(output / "progress.html", page("Proof progress", mast, dashboard, watch + '<script src="activity.js" defer></script><script src="artifact.js" defer></script>'))
    atomic(output / "manuscript.pdf", pdf)
    shutil.copyfile(Path(__file__).resolve().parents[1] / "assets/style.css", output / "style.css")
    atomic(output / "inventory.json", json.dumps(claims, ensure_ascii=False, indent=2).encode())
    atomic(output / "checkpoint.json", json.dumps(dict(revision=version,evidence_commit=ci["commit"] if ci else None,artifact_id=artifact_id)).encode())
    print(f"{len(claims)} claims | {output / 'progress.html'}")
    print(f"Authorized proof work: {scope}")
    if unchecked:
        print("Warning: these closures were audited without --statements, so their statements may depend on "
              f"proof modules: {', '.join(unchecked)}. See 'Separate statements from proofs' in SKILL.md.")
    if no_example:
        print(f"Warning: {NO_EXAMPLE.lower()} for these closures: {', '.join(no_example)}. "
              "See 'Show the hypotheses can hold' in SKILL.md.")
    hosting = p.get("hosting") or {}
    if not hosting.get("repository") and hosting.get("decision") != "local":
        print("Hosting decision pending. Ask where the author wants this paper's explorer and dashboard hosted.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["build", "approve", "review", "review-inputs","compare","review-work"])
    parser.add_argument("project", type=Path)
    parser.add_argument("claims", nargs="*", help="approve: claim labels (default: every closed claim awaiting approval)")
    parser.add_argument("--by", help="approve: the author approving the statements. Only the author runs approve")
    parser.add_argument("--ci-receipt", type=Path, help="Evidence downloaded from the trusted Lean workflow")
    parser.add_argument("--commit", help="Git revision being rendered")
    parser.add_argument("--artifact-id", type=int, help="ID of the GitHub artifact containing the supplied CI receipt")
    parser.add_argument("--no-open", action="store_true")
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--side",choices=["paper","lean"],help="Limit the independent reader to one source")
    parser.add_argument("--readings",type=Path,help="Agent comparison record for one claim")
    parser.add_argument("--check",action="store_true",help="review-work: exit nonzero for pending agent tasks or requested CI evidence")
    parser.add_argument("--require-ci",action="store_true",help="review-work: verify receipt coverage for the current checkout commit")
    args = parser.parse_args()
    try:
        if args.operation == "review-work":
            report = review_work(args.project.resolve(),args.claims,require_ci=args.require_ci,ci_receipt=args.ci_receipt)
            print(json.dumps(report,ensure_ascii=False,indent=2))
            if args.check and (report["agent_tasks"] or report["uncommitted_delivery_files"] or report["ci_pending"]):
                sys.exit(1)
        elif args.operation == "approve":
            reviews.terminal(args.project.resolve(), args.claims, args.by or "")
            build_local(args.project.resolve())
        elif args.operation == "review":
            review_web.serve(args.project.resolve(),not args.no_open,args.port)
        elif args.operation == "review-inputs":
            if len(args.claims) != 1:
                raise ValueError("Choose one claim for independent readings")
            data = reviews.get_packet(args.project.resolve(),args.claims[0])
            packet = {"bindings":data["view"]["bindings"]}
            if args.side != "lean":
                packet["paper"] = data["view"]["excerpt"]
            if args.side != "paper":
                packet["lean"] = data["sources"]
                packet["defaults"] = data["defaults"]
                if data.get("witness"):
                    packet["witness"] = data["witness"]
                if data.get("axiom_profile"):
                    packet["axiom_profile"] = data["axiom_profile"]
                if data.get("noncomputable_constants"):
                    packet["noncomputable_constants"] = data["noncomputable_constants"]
                if data.get("external_packages"):
                    packet["external_packages"] = data["external_packages"]
            if not args.side:
                packet["reported_differences"] = [e["id"] for e in data["events"] if e["decision"]=="difference"]
            # This JSON is piped to independent readers, including on Windows legacy code pages.
            print(json.dumps(packet, indent=2))
        elif args.operation == "compare":
            if len(args.claims) != 1 or not args.readings:
                raise ValueError("Supply one claim label and --readings FILE")
            reviews.save_comparison(args.project.resolve(),args.claims[0],json.loads(args.readings.read_bytes()))
            build_local(args.project.resolve())
        else:
            build(args.project.resolve(), ci_receipt=args.ci_receipt, commit=args.commit, artifact_id=args.artifact_id)
    except (ValueError, KeyError, OSError) as exc:
        sys.exit(f"Proof Atlas: {exc}")
