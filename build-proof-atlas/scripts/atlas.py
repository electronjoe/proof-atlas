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


def proof_work_profile(project):
    scope = project.get("proof_work") or {}
    profile = scope.get("profile", "thorough")
    if profile not in ("thorough", "quick"):
        raise ValueError("proof_work.profile must be thorough or quick")
    return profile


def proof_work_description(project, claims, *, closed_results=None):
    scope = project.get("proof_work")
    if scope is None:
        return "Proof-work authorization has not been recorded."
    profile = proof_work_profile(project)
    mode = scope["mode"]
    is_complete = False
    if mode == "paper":
        total = sum(claim["kind"] != "conjecture" for claim in claims)
        if total and closed_results == total:
            is_complete = True
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
    if profile == "quick" and not is_complete:
        text = "Quick triage profile (hands-off). " + text + " Deferred checks and conditional assumptions stay explicitly badged."
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


def current_audit(root, cid, w, *, allow_conditional=False):
    """The closure's receipt, provided the audited sources are unchanged."""
    status = w.get("status")
    allowed = ("closed", "conditional") if allow_conditional else ("closed",)
    if status not in allowed:
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
    if status == "closed" and (audit.get("assumes") or w.get("assumes")):
        raise ValueError(f"{cid}: closed claim cannot carry unresolved assumptions; use status 'conditional'")
    if status == "conditional" and not audit.get("assumes"):
        raise ValueError(f"{cid}: conditional claim requires non-empty assumes in its audit receipt")
    return audit


def current_statement_audit(root, cid, w):
    """Return `(audit, proof_checked)` for a closed, conditional, or Gate 1 statement check."""
    if w.get("status") == "closed":
        return current_audit(root, cid, w), True
    if w.get("status") == "conditional":
        return current_audit(root, cid, w, allow_conditional=True), False
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
    default_mode = "skip" if proof_work_profile(project) == "quick" else "available"
    mode = work.get("witness_search", project.get("witness_search", default_mode))
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
    report = {"scope": project.get("proof_work"), "profile": proof_work_profile(project),
              "agent_tasks": [], "author_questions": [],
              "conditional_claims": [],
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
        if packet.get("conditional"):
            report["conditional_claims"].append(dict(claim=cid, assumes=work.get("assumes") or packet["assumes"]))
        proof_checked = work.get("status") in ("closed", "conditional")
        needs_gate1_review = (not proof_checked and packet["statement_checked"]
                              and not packet["disputed"] and "analysis" not in packet["view"])
        if (packet["disputed"] or (proof_checked and packet["actor"]=="Proof agent")
                or needs_gate1_review or packet.get("needs_author_confirmation")):
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


_LEAN_KEYWORDS = {
    "theorem", "lemma", "def", "structure", "class", "inductive", "axiom", "opaque",
    "namespace", "section", "end", "import", "open", "where", "let", "in", "by", "fun",
    "match", "with", "if", "then", "else", "do", "return", "for", "type", "Prop", "Type", "Sort",
}


def _lean_ident(label, used=()):
    ident = re.sub(r"[^A-Za-z0-9_]", "_", str(label)).strip("_")
    if not ident or ident[0].isdigit() or ident in _LEAN_KEYWORDS:
        ident = "claim_" + (ident or "item")
    candidate = ident
    suffix = 2
    while candidate in used:
        candidate = f"{ident}_{suffix}"
        suffix += 1
    return candidate


def _claim_ref_label(cid, by_id, notes):
    note_ref = (notes.get(cid) or {}).get("reference")
    if note_ref:
        return note_ref
    claim = by_id.get(cid)
    if not claim:
        return cid
    if claim.get("title") and claim["title"] != cid:
        return f"{claim['kind'].title()} ({claim['title']})"
    return f"{claim['kind'].title()} {cid}"


def _resolve_assumes_items(audit_assumes, work_assumes, by_id, work, notes):
    expected_to_cid = {}
    for other_cid, other_w in work.items():
        for container in (other_w.get("assembly"), other_w.get("closure"), other_w.get("statement_check")):
            if isinstance(container, dict) and container.get("expected"):
                expected_to_cid.setdefault(container["expected"], other_cid)
    items = []
    seen = set()
    for idx, prop in enumerate(audit_assumes or ()):
        hint = work_assumes[idx] if idx < len(work_assumes) and work_assumes[idx] in by_id else None
        dep_cid = hint or expected_to_cid.get(prop) or (prop if prop in by_id else None)
        key = dep_cid or prop
        if key in seen:
            continue
        seen.add(key)
        ref = _claim_ref_label(dep_cid, by_id, notes) if dep_cid else prop
        items.append(dict(id=dep_cid, reference=ref, expected=prop))
    return items


def assemble(root, *, package=None, run_audit=False):
    """Generate Assembly.lean composing separable per-claim proofs in topological order.

    Claims whose upstream prerequisites are proved compose unconditionally; any
    unproved prerequisite remains an explicit `Statements.*` hypothesis binder on
    `Assembly.<name>` and is reported in `assumes_claims` / `assumes_expected`.
    """
    from types import SimpleNamespace
    import audit_lean

    p = json.loads((root / "project.json").read_text(encoding="utf-8-sig"))
    claims = manuscript_claims(root, p)
    by_id = {c["id"]: c for c in claims}
    order = p.get("claim_order") or [c["id"] for c in claims]
    work = p.get("work", {})

    expected_by_cid = {}
    stmt_modules_by_cid = {}
    pkg_specs = {}

    for cid in order:
        w = work.get(cid, {})
        asm = w.get("assembly")
        closure = w.get("closure")
        sc = w.get("statement_check")
        exp = ((asm or {}).get("expected") or (closure or {}).get("expected")
               or (sc or {}).get("expected"))
        if exp:
            expected_by_cid[cid] = exp
        stmt_mods = list((asm or {}).get("statement_modules") or [])
        for audit_holder in (closure, sc):
            if audit_holder and audit_holder.get("audit") and not stmt_mods:
                try:
                    rec = json.loads(local(root, audit_holder["audit"]).read_bytes())
                    for const in rec.get("statement", {}).get("constants", []):
                        if const.get("name") == exp and const.get("file", "").endswith(".lean"):
                            stmt_mods.append(const["file"][:-5].replace("/", "."))
                except (OSError, ValueError):
                    pass
        if stmt_mods:
            stmt_modules_by_cid[cid] = stmt_mods

        if asm:
            pkg = asm.get("package") or (closure or {}).get("package") or (sc or {}).get("package")
            if not pkg:
                raise ValueError(f"{cid}: assembly requires a package path")
            if package and pkg != package:
                continue
            if not exp or not asm.get("module") or not asm.get("declaration"):
                raise ValueError(f"{cid}: assembly requires expected, module, and declaration")
            pkg_specs.setdefault(pkg, {})[cid] = dict(
                cid=cid, package=pkg, expected=exp, module=asm["module"],
                declaration=asm["declaration"], assumes=list(asm.get("assumes") or []),
                name=asm.get("name"), statements=list(asm.get("statements") or ["Statements"]),
                routine=list(asm.get("routine") or []), witness=asm.get("witness"),
                statement_modules=stmt_mods,
            )
        elif w.get("status") == "closed" and closure and closure.get("package"):
            pkg = closure["package"]
            if package and pkg != package:
                continue
            if closure.get("declaration", "").startswith("Assembly."):
                continue
            targets = []
            try:
                rec = json.loads(local(root, closure["audit"]).read_bytes())
                targets = list(rec.get("targets") or [])
            except (OSError, ValueError):
                pass
            if targets:
                pkg_specs.setdefault(pkg, {})[cid] = dict(
                    cid=cid, package=pkg, expected=closure["expected"], module=targets[0],
                    declaration=closure["declaration"], assumes=[], name=None,
                    statements=list(rec.get("statements") or ["Statements"]),
                    routine=list(rec.get("routine") or []),
                    witness=(rec.get("hypotheses") or {}).get("declaration"),
                    statement_modules=stmt_mods,
                )

    if not pkg_specs:
        raise ValueError("No separable assembly specifications found in project.json")

    expected_to_cid = {exp: cid for cid, exp in expected_by_cid.items()}
    report = {"packages": {}}
    project_changed = False

    for pkg, specs in sorted(pkg_specs.items()):
        pkg_root = local(root, pkg)
        used_names = set()
        ident_by_cid = {}
        for cid in order:
            if cid in specs:
                chosen = specs[cid]["name"] or _lean_ident(cid, used_names)
                if chosen in used_names:
                    raise ValueError(f"{cid}: duplicate assembly theorem name {chosen}")
                used_names.add(chosen)
                ident_by_cid[cid] = chosen

        # Normalize each claim's proof assumptions to (dep_cid_or_none, dep_expected).
        deps_by_cid = {}
        for cid, spec in specs.items():
            resolved_deps = []
            for dep in spec["assumes"]:
                if dep in by_id:
                    dep_exp = expected_by_cid.get(dep)
                    if not dep_exp:
                        raise ValueError(f"{cid}: assumed claim {dep} has no recorded expected Lean proposition")
                    resolved_deps.append((dep, dep_exp))
                elif dep in expected_to_cid:
                    dep_cid = expected_to_cid[dep]
                    resolved_deps.append((dep_cid, dep))
                else:
                    if not re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", dep):
                        raise ValueError(f"{cid}: unknown assumed claim or Lean identifier {dep}")
                    resolved_deps.append((None, dep))
            deps_by_cid[cid] = resolved_deps

        # Topological sort over assembled claims in this package.
        indegree = {cid: 0 for cid in specs}
        dependents = {cid: [] for cid in specs}
        for cid, deps in deps_by_cid.items():
            for dep_cid, _ in deps:
                if dep_cid in specs:
                    indegree[cid] += 1
                    dependents[dep_cid].append(cid)
        ready = [cid for cid in order if cid in specs and indegree[cid] == 0]
        topo = []
        while ready:
            cur = ready.pop(0)
            topo.append(cur)
            for nxt in dependents[cur]:
                indegree[nxt] -= 1
                if indegree[nxt] == 0:
                    ready.append(nxt)
            ready.sort(key=lambda c: order.index(c) if c in order else len(order))
        if len(topo) != len(specs):
            stuck = sorted(set(specs) - set(topo))
            raise ValueError("Cyclic assembly dependency involving: " + ", ".join(stuck))

        imports = set()
        decls_lean = []
        unresolved_by_cid = {}
        claim_reports = []

        for cid in topo:
            spec = specs[cid]
            imports.add(spec["module"])
            imports.update(spec["statement_modules"])
            unresolved = []
            unresolved_keys = set()

            def add_unresolved(dep_cid, dep_exp):
                key = dep_cid or dep_exp
                if key not in unresolved_keys:
                    unresolved_keys.add(key)
                    unresolved.append((dep_cid, dep_exp))
                    if dep_cid and dep_cid in stmt_modules_by_cid:
                        imports.update(stmt_modules_by_cid[dep_cid])

            arg_exprs = []
            for dep_cid, dep_exp in deps_by_cid[cid]:
                if dep_cid in unresolved_by_cid:
                    dep_unresolved = unresolved_by_cid[dep_cid]
                    for u_cid, u_exp in dep_unresolved:
                        add_unresolved(u_cid, u_exp)
                    if dep_unresolved:
                        u_args = " ".join("h_" + _lean_ident(u_cid or u_exp) for u_cid, u_exp in dep_unresolved)
                        arg_exprs.append(f"({ident_by_cid[dep_cid]} {u_args})")
                    else:
                        arg_exprs.append(ident_by_cid[dep_cid])
                else:
                    add_unresolved(dep_cid, dep_exp)
                    arg_exprs.append("h_" + _lean_ident(dep_cid or dep_exp))

            unresolved_by_cid[cid] = unresolved
            name = ident_by_cid[cid]
            binders = "".join(f" (h_{_lean_ident(u_cid or u_exp)} : _root_.{u_exp})" for u_cid, u_exp in unresolved)
            rhs = f"_root_.{spec['declaration']}" + ("" if not arg_exprs else " " + " ".join(arg_exprs))
            decls_lean.append(f"theorem {name}{binders} : _root_.{spec['expected']} :=\n  {rhs}")

            assumes_claims = [u_cid or u_exp for u_cid, u_exp in unresolved]
            assumes_expected = [u_exp for _, u_exp in unresolved]
            claim_reports.append(dict(
                claim=cid,
                declaration=f"Assembly.{name}",
                expected=spec["expected"],
                assumes_claims=assumes_claims,
                assumes_expected=assumes_expected,
                unconditional=not unresolved,
            ))

        if (pkg_root / "Statements.lean").is_file() and not any(m == "Statements" or m.startswith("Statements.") for m in imports):
            imports.add("Statements")

        header = "/- Generated by `atlas.py assemble`. Do not edit by hand. -/\n"
        import_block = "\n".join(f"import {mod}" for mod in sorted(imports))
        assembly_source = header + import_block + "\n\nnamespace Assembly\n\n" + "\n\n".join(decls_lean) + "\n\nend Assembly\n"
        assembly_path = pkg_root / "Assembly.lean"
        atomic(assembly_path, assembly_source.encode("utf-8"))

        if run_audit:
            contract_rel = "AssemblyContract.lean"
            contract_imports = ["Assembly"]
            if (pkg_root / "Examples.lean").is_file():
                contract_imports.append("Examples")
            for cid in topo:
                spec = specs[cid]
                if spec.get("witness") and "." in spec["witness"]:
                    mod_guess = spec["witness"].rsplit(".", 1)[0]
                    if (pkg_root / ("/".join(mod_guess.split(".")) + ".lean")).is_file():
                        contract_imports.append(mod_guess)
            contract_text = "\n".join(f"import {m}" for m in sorted(set(contract_imports))) + "\n"
            atomic(pkg_root / contract_rel, contract_text.encode("utf-8"))
            ev_dir = root / "evidence"
            ev_dir.mkdir(exist_ok=True)
            for item in claim_reports:
                cid = item["claim"]
                spec = specs[cid]
                audit_data = audit_lean.audit(SimpleNamespace(
                    package=pkg_root,
                    contract=contract_rel,
                    expected=item["expected"],
                    declaration=item["declaration"],
                    target=["Assembly"],
                    statements=spec["statements"],
                    routine=spec["routine"],
                    assumes=item["assumes_expected"],
                    witness=spec["witness"],
                    statement_only=False,
                ))
                ev_rel = f"evidence/assembly-{ident_by_cid[cid]}.json"
                atomic(root / ev_rel, (json.dumps(audit_data, indent=2) + "\n").encode("utf-8"))
                w = p.setdefault("work", {}).setdefault(cid, {})
                existing_closure = w.get("closure") or {}
                w["closure"] = dict(
                    package=pkg,
                    expected=item["expected"],
                    declaration=item["declaration"],
                    audit=ev_rel,
                    correspondence=existing_closure.get("correspondence") or w.get("scope") or f"Assembled proof for {cid}.",
                )
                w["checked_inputs"] = {(Path(pkg) / k).as_posix(): v for k, v in audit_data["checked_inputs"].items()}
                w.setdefault("scope", w["closure"]["correspondence"])
                if not w.get("run_log"):
                    log_rel = f"evidence/assembly-{ident_by_cid[cid]}.log"
                    atomic(root / log_rel, (audit_data.get("lean_output", "") + "\n").encode("utf-8"))
                    w["run_log"] = log_rel
                has_open_subproofs = any(part.get("status") != "checked" for part in w.get("subproofs", []))
                if item["unconditional"]:
                    w.pop("assumes", None)
                    if not has_open_subproofs:
                        w["status"] = "closed"
                else:
                    w["assumes"] = item["assumes_claims"]
                    w["status"] = "conditional"
                w["updated"] = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
                project_changed = True

        report["packages"][pkg] = dict(
            assembly_file=(Path(pkg) / "Assembly.lean").as_posix(),
            claims=claim_reports,
        )

    if project_changed:
        atomic(root / "project.json", (json.dumps(p, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
        build_local(root)
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
    conditional_results = 0
    prereqs_by_cid = {c["id"]: set() for c in claims}
    for edge in edges:
        prereqs_by_cid[edge["claim"]].add(edge["prerequisite"])
    built_records = []
    for c in claims:
        cid = c["id"]
        w = work.get(cid, {})
        m = notes.get(cid, {})
        status = w.get("status", "open")
        if status not in {"open", "drafted", "blocked", "attempted", "conditional", "closed"}:
            raise ValueError(f"{cid}: unsupported checkpoint status {status}")
        entry = {**c, **m, **w}
        audit = None
        receipt = None
        assumed_items = []
        if status in ("closed", "conditional"):
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
                (status == "closed" and any(part["status"] != "checked" for part in w.get("subproofs", [])))):
                raise ValueError(f"{cid}: closure requires matching audit evidence, correspondence and resolved obligations")
            if status == "closed" and (audit.get("assumes") or w.get("assumes")):
                raise ValueError(f"{cid}: closed claim cannot have unresolved assumptions; use status 'conditional' until prerequisites close")
            if status == "conditional" and not audit.get("assumes"):
                raise ValueError(f"{cid}: conditional claim requires non-empty assumes in its audit receipt; upgrade to closed if unconditional")
            if not audit.get("statements"):
                unchecked.append(cid)
            entry["hypotheses"] = audit.get("hypotheses")
            if status == "closed" and not audit.get("hypotheses"):
                no_example.append(cid)
            (output / "logs").mkdir(exist_ok=True)
            name = hashlib.sha256(receipt).hexdigest() + ".json"
            atomic(output / "logs" / name, receipt)
            entry["audit_log"] = "logs/" + name
            if status == "conditional":
                assumed_items = _resolve_assumes_items(audit.get("assumes", []), w.get("assumes", []), by_id, work, notes)
                for item in assumed_items:
                    if item["id"] in by_id:
                        prereqs_by_cid[cid].add(item["id"])
        for dep in w.get("assumes", []):
            if dep in by_id:
                prereqs_by_cid[cid].add(dep)
        changed = [path for path, digest in w.get("checked_inputs", {}).items()
                   if not local(root, path).is_file() or hashlib.sha256(local(root, path).read_bytes()).hexdigest() != digest]
        if changed:
            stale[cid] = "Lean inputs changed since the recorded check: " + ", ".join(changed)
            entry["scope"] = stale[cid] + ". The linked log is historical."
            entry["summary"] = m.get("summary", "The paper claim is awaiting a fresh Lean check.")
            status = "awaiting recheck"
        checked = status == "closed"
        is_conditional = status == "conditional"
        statement_audit = audit if (checked or is_conditional) else None
        statement_checked = False
        if not checked and not is_conditional and w.get("statement_check"):
            try:
                statement_audit, _ = current_statement_audit(root, cid, w)
                statement_checked = True
                entry["hypotheses"] = statement_audit.get("hypotheses")
            except (ValueError, OSError):
                statement_audit = None
        active_audit = audit if (checked or is_conditional) else statement_audit
        rd = reviews.packet(root,p,c,w,active_audit,comparisons.get(cid),reviews.history(root,cid),
                            checked,statement_checked,
                            conditional=is_conditional,
                            assumes=[item["reference"] for item in assumed_items] if is_conditional else ())
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
        entry["status"] = "correspondence under review" if rd["disputed"] else status
        if "analysis" in rd["view"]:
            entry["differences"] = reviews.differences(rd["view"]["analysis"])
        if c["kind"] != "conjecture" and checked and not rd["disputed"]:
            closed_results += 1
        elif c["kind"] != "conjecture" and is_conditional and not rd["disputed"]:
            conditional_results += 1
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
        cond_label = f"Conditional (assumes {', '.join(item['reference'] for item in assumed_items)})"
        label = ("Open conjecture" if c["kind"] == "conjecture" and status == "open" else
                 "Lean checked" if checked else "Awaiting Lean recheck" if changed else
                 cond_label if is_conditional else
                 "Subproofs checked" if has_parts else
                 "Statement drafted (proof in progress)" if statement_checked else "No completed Lean check")
        verification = {"label": label}
        if is_conditional:
            verification["conditional"] = True
            verification["assumes"] = assumed_items
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
        built_records.append((c, entry, rd, checked, is_conditional, label))

    # Propagate Needs author confirmation from unattended quick-mode readings to transitive dependents.
    direct_confirm = {rd["id"] for rd in review_entries if rd.get("needs_author_confirmation")}
    for c, entry, rd, checked, is_conditional, label in built_records:
        cid = c["id"]
        visited = set()
        stack = list(prereqs_by_cid.get(cid, ()))
        while stack:
            cur = stack.pop()
            if cur in visited or cur == cid:
                continue
            visited.add(cur)
            stack.extend(prereqs_by_cid.get(cur, ()))
        via_ids = [u for u in (e["id"] for e in entries) if u in visited and u in direct_confirm]
        via_items = [dict(id=u, reference=_claim_ref_label(u, by_id, notes), review_url=reviews.review_url(u))
                     for u in via_ids]
        rd["needs_author_confirmation_via"] = via_items
        verification = entry["verification"]
        if rd.get("needs_author_confirmation"):
            verification["needs_author_confirmation"] = True
        if via_items:
            verification["needs_author_confirmation_via"] = via_items
        atomic(output/reviews.review_url(cid), review_web.render(rd))

        url = "proofs/index.html#/claim/" + quote(cid, safe="")
        target = ' <strong class="proof-target">Current proof target</strong>' if cid == p.get("focus") else ''
        badge = f' · <a href="{url}?view=lean">{esc(label)}</a>'
        if (checked or is_conditional) and not entry.get("hypotheses"):
            badge += f' · {NO_EXAMPLE}'
        if rd.get("needs_author_confirmation"):
            badge += f' · <a href="{reviews.review_url(cid)}"><strong>Needs author confirmation</strong></a>'
        elif via_items:
            via_refs = ", ".join(item["reference"] for item in via_items)
            badge += f' · <a href="{reviews.review_url(cid)}"><strong>Needs author confirmation</strong> (depends on {esc(via_refs)})</a>'
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
    cond_part = f" · {conditional_results} conditional" if conditional_results else ""
    pending = f"{cond_part} · {machine}/{total_results} machine verified · {reviewed}/{total_results} author reviewed"
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
        extras = []
        if v.get("needs_author_confirmation"):
            extras.append(f'<a class="status" href="{esc(v["review_url"])}">Needs author confirmation</a>')
        elif v.get("needs_author_confirmation_via"):
            extras.append(f'<a class="status" href="{esc(v["review_url"])}">Needs author confirmation</a>')
        if "approval" in v:
            extras.append(f'<a class="status approval approved" href="{esc(v["review_url"])}">{esc(v["approval"])}</a>')
        if extras:
            mark = f'<span class="marks">{mark}{"".join(extras)}</span>'
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
    parser.add_argument("operation", choices=["build", "assemble", "approve", "review", "review-inputs","compare","review-work"])
    parser.add_argument("project", type=Path)
    parser.add_argument("claims", nargs="*", help="approve: claim labels (default: every closed claim awaiting approval)")
    parser.add_argument("--by", help="approve: the author approving the statements. Only the author runs approve")
    parser.add_argument("--package", help="assemble: limit Assembly.lean generation to one project-relative Lean package")
    parser.add_argument("--audit", action="store_true", help="assemble: audit each assembled claim and update project.json")
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
        if args.operation == "assemble":
            report = assemble(args.project.resolve(), package=args.package, run_audit=args.audit)
            print(json.dumps(report, ensure_ascii=False, indent=2))
        elif args.operation == "review-work":
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
