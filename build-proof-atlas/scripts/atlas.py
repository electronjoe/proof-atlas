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
HEADLINE_KINDS = frozenset({"theorem", "corollary", "proposition"})
MANIFEST_EDIT_KEY = "manifest-verification-scope"
PROOF_BASES = frozenset({"paper", "lean", "aligned", "supplied"})
LEAN_CI_LEVELS = frozenset({"standard", "paranoid"})
BASIS_LABELS = {
    "paper": "Follows paper proof",
    "lean": "Lean-only proof route",
    "aligned": "Aligned paper & Lean proof",
    "supplied": "Proof supplied outside manuscript",
}
SUPPLIED_BADGE = "Lean checked (proof supplied outside manuscript)"
STEP_VERIFIED_PAPER_BADGE = "Step-verified (paper)"
STEP_VERIFIED_SUPPLIED_BADGE = "Step-verified (with supplied steps)"
EDGE_GROUNDING_LABELS = {
    "both": "Used in both paper & Lean proof",
    "paper_only": "Paper-only dependency",
    "lean_only": "Lean-only prerequisite",
    "paper": "Paper dependency",
}


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


def lean_ci_level(project):
    """Return the configured Lean CI verification level ('standard' default or 'paranoid')."""
    level = (project.get("hosting") or {}).get("lean_ci_level", "standard")
    if not isinstance(level, str) or level not in LEAN_CI_LEVELS:
        raise ValueError("hosting.lean_ci_level must be 'standard' or 'paranoid'")
    return level


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
    if "ci_level" in data and data["ci_level"] not in LEAN_CI_LEVELS:
        return None
    if "kernels_checked" in data:
        kc = data["kernels_checked"]
        if not isinstance(kc, list) or not all(isinstance(k, str) and k.strip() for k in kc):
            return None
    return data


def _ci_claim_status(audit, receipt_bytes, ci, cid):
    """Validate a claim's CI receipt entry and return (verified, paranoid_verified, kernels, ci_level)."""
    if not ci or not audit or receipt_bytes is None:
        return False, False, [], None
    record = ci.get("claims", {}).get(cid)
    if not isinstance(record, dict):
        return False, False, [], None
    if not (record.get("audit_sha256") == hashlib.sha256(receipt_bytes).hexdigest()
            and all(record.get(k) == audit.get(k) for k in ("expected", "declaration", "toolchain"))
            and (not audit.get("statement") or record.get("statement_sha256") == audit["statement"]["sha256"])
            and (not audit.get("hypotheses") or record.get("hypotheses") == audit["hypotheses"]["proposition"])
            and (not audit.get("step_audit") or record.get("step_map_sha256") == audit["step_audit"].get("step_map_sha256"))
            and set(record.get("axioms", [])) == set(audit.get("axioms", []))
            and record.get("theorem_info") is not False
            and not record.get("assumes")):
        return False, False, [], None
    kernels = list(record.get("kernels_checked") or ci.get("kernels_checked") or ["lean-kernel"])
    level = ci.get("ci_level", "standard")
    paranoid_verified = (level == "paranoid" and any(k != "lean-kernel" for k in kernels))
    return True, paranoid_verified, kernels, level


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


def claim_tier(claim, note=None, work=None):
    """Classify a manuscript claim as headline, supporting, or conjecture."""
    if claim["kind"].casefold() == "conjecture":
        return "conjecture"
    explicit = None
    if isinstance(work, dict) and "headline" in work:
        explicit = work["headline"]
    elif isinstance(note, dict) and "headline" in note:
        explicit = note["headline"]
    if explicit is not None:
        if type(explicit) is not bool:
            raise ValueError(f"{claim['id']}: headline must be a boolean")
        return "headline" if explicit else "supporting"
    return "headline" if claim["kind"].casefold() in HEADLINE_KINDS else "supporting"


def claim_resolution(checked, is_conditional, disputed, has_parts):
    """Return the multi-resolution verification state of a claim."""
    if checked and not disputed:
        return "unconditionally_closed"
    if is_conditional and not disputed:
        return "conditional"
    if has_parts:
        return "subproofs_checked"
    return "open"


def unresolved_defaults(rd):
    """Default-value findings that are marked 'needs attention' or not yet assessed."""
    assessments = rd["view"].get("analysis", {}).get("default_assessments", {})
    items = []
    for finding in rd.get("defaults", []):
        assessment = assessments.get(finding["id"], {})
        status = assessment.get("status", "not assessed")
        if status != "justified":
            items.append(dict(
                id=finding["id"],
                constant=finding["constant"],
                construct=finding["construct"],
                type=finding.get("type", ""),
                file=finding.get("file", ""),
                lines=finding.get("lines"),
                meaning=finding.get("meaning", ""),
                status=status,
                explanation=assessment.get("explanation", ""),
            ))
    return items


def _deferred_bridging_lemmas(cid, work):
    raw = work.get("deferred_bridging_lemmas")
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise ValueError(f"{cid}: deferred_bridging_lemmas must be a list")
    items = []
    for item in raw:
        if isinstance(item, str) and item.strip():
            items.append(item.strip())
        elif isinstance(item, dict):
            text = (item.get("title") or item.get("name") or item.get("description") or "").strip()
            if text:
                items.append(text)
            else:
                raise ValueError(f"{cid}: deferred_bridging_lemmas entries must be non-empty")
        else:
            raise ValueError(f"{cid}: deferred_bridging_lemmas entries must be strings or objects")
    return items


def _is_undistilled(cid, work, profile, checked, is_conditional):
    if "distilled" in work and type(work["distilled"]) is not bool:
        raise ValueError(f"{cid}: distilled must be a boolean")
    if not (checked or is_conditional):
        return False
    if work.get("distilled") is False:
        return True
    return profile == "quick" and work.get("distilled") is not True


def claim_basis(cid, note=None, work=None):
    """Return validated TINA Two Homes proof basis ('paper', 'lean', 'aligned', 'supplied') or None."""
    raw = None
    if isinstance(work, dict) and "basis" in work:
        raw = work["basis"]
    elif isinstance(note, dict) and "basis" in note:
        raw = note["basis"]
    if raw is None:
        return None
    if not isinstance(raw, str) or raw not in PROOF_BASES:
        allowed = ", ".join(sorted(PROOF_BASES))
        raise ValueError(f"{cid}: basis must be one of {allowed}")
    return raw


def extract_proof_metrics(audit):
    """Extract kernel-recorded proof size metrics from an audit receipt, if present."""
    if not isinstance(audit, dict):
        return None
    metrics = {}
    for key in ("reachable_local_defs", "reachable_local_theorems", "checked_lean_loc"):
        val = audit.get(key)
        if type(val) is int and val >= 0:
            metrics[key] = val
    return metrics or None


def supplement_anchor(cid):
    """Deterministic HTML/Markdown anchor slug for a claim in dist/supplement.md."""
    slug = re.sub(r"[^a-z0-9]+", "-", str(cid).casefold()).strip("-")
    return slug or "claim"


def load_bound_tex_sources(root, project):
    """Load SHA-256-verified manuscript TeX sources with normalized LF newlines."""
    sources = []
    for source in project.get("tex", []):
        text = read_source(root, source).decode("utf-8-sig").replace("\r\n", "\n")
        sources.append((source["path"], text))
    return sources


def collect_other_claim_declarations(project, exclude_cid):
    """Return sorted Lean declarations belonging to other claims in project.json."""
    decls = set()
    for other_cid, other_w in (project.get("work") or {}).items():
        if other_cid == exclude_cid or not isinstance(other_w, dict):
            continue
        for holder in (other_w.get("closure"), other_w.get("assembly")):
            if isinstance(holder, dict) and isinstance(holder.get("declaration"), str) and holder["declaration"].strip():
                decls.add(holder["declaration"].strip())
    return sorted(decls)


def resolve_claim_step_map(root, cid, work, note, tex_sources, *, default_main=None):
    """Load, normalize, and verify structured Lamport step provenance against bound TeX sources."""
    import audit_lean

    raw = None
    if isinstance(work, dict) and work.get("step_map") is not None:
        raw = work["step_map"]
    elif isinstance(work, dict) and isinstance(work.get("assembly"), dict) and work["assembly"].get("step_map") is not None:
        raw = work["assembly"]["step_map"]
    elif isinstance(note, dict) and note.get("step_map") is not None:
        raw = note["step_map"]
    if raw is None:
        return None

    source_rel = None
    if isinstance(raw, str):
        source_rel = raw
        path = local(root, raw)
        try:
            data = json.loads(path.read_text(encoding="utf-8-sig"))
        except (OSError, ValueError) as exc:
            raise ValueError(f"{cid}: could not load step_map '{raw}': {exc}") from exc
    elif isinstance(raw, (dict, list)):
        data = raw
    else:
        raise ValueError(f"{cid}: step_map must be a project-relative JSON path, object, or list")

    try:
        normalized = audit_lean.normalize_step_map(data, declaration=default_main, root=root)
    except ValueError as exc:
        raise ValueError(f"{cid}: {exc}") from exc

    tex_by_path = dict(tex_sources)
    paper_count = 0
    supplied_count = 0
    enriched_steps = []
    for step in normalized["steps"]:
        sid = step["id"]
        origin = step.get("origin")
        if origin not in audit_lean.STEP_ORIGINS:
            raise ValueError(
                f"{cid}: step '{sid}' must declare origin 'paper' or 'supplied' for Lamport step provenance"
            )
        enriched = dict(step)
        if origin == "paper":
            tex_excerpt = step.get("tex")
            if not isinstance(tex_excerpt, str) or not tex_excerpt.strip():
                raise ValueError(
                    f"{cid}: step '{sid}' has origin 'paper' and must supply a non-empty verbatim 'tex' substring"
                )
            needle = tex_excerpt.replace("\r\n", "\n")
            req_file = step.get("tex_file")
            matched_file = None
            matched_line = None
            if req_file:
                if req_file not in tex_by_path:
                    raise ValueError(
                        f"{cid}: step '{sid}' tex_file '{req_file}' is not a bound TeX source in project.json"
                    )
                pos = tex_by_path[req_file].find(needle)
                if pos >= 0:
                    matched_file = req_file
                    matched_line = tex_by_path[req_file].count("\n", 0, pos) + 1
            else:
                for path_str, content in tex_sources:
                    pos = content.find(needle)
                    if pos >= 0:
                        matched_file = path_str
                        matched_line = content.count("\n", 0, pos) + 1
                        break
            if matched_file is None:
                raise ValueError(
                    f"{cid}: step '{sid}' has origin 'paper' but its 'tex' excerpt is not a verbatim "
                    "substring of the bound TeX sources"
                )
            enriched["tex"] = needle
            enriched["tex_file"] = matched_file
            enriched["tex_line"] = matched_line
            enriched["tex_verified"] = True
            paper_count += 1
        else:
            enriched["tex_verified"] = False
            supplied_count += 1
        enriched_steps.append(enriched)

    return dict(
        source=source_rel,
        main_declaration=normalized["main_declaration"],
        main_deps=normalized["main_deps"],
        forbidden_mains=normalized["forbidden_mains"],
        step_map_sha256=normalized["step_map_sha256"],
        steps=enriched_steps,
        paper_step_count=paper_count,
        supplied_step_count=supplied_count,
    )


def evaluate_step_verification(cid, step_map, audit, *, proof_checked=False, changed=False):
    """Combine verified step_map provenance with the audit receipt's compiled-Expr step_audit."""
    step_audit = (audit or {}).get("step_audit")
    if step_map is None and not step_audit:
        return None

    if step_audit is not None:
        if step_audit.get("verified") is not True:
            raise ValueError(f"{cid}: audit receipt contains an unverified step_audit record")
        if step_map is None:
            raw_steps = step_audit.get("steps") or []
            if not raw_steps or any(s.get("origin") != "supplied" for s in raw_steps):
                raise ValueError(
                    f"{cid}: audit receipt has step_audit, but no step_map is configured on work[{cid}] "
                    "or reader.json to verify verbatim TeX provenance of paper steps"
                )
            is_verified = bool(proof_checked and not changed)
            steps = [
                dict(
                    id=s["id"],
                    lemma=s["lemma"],
                    step_deps=list(s.get("declared_deps") or []),
                    used_deps=list(s.get("used_deps") or []),
                    used_statements=list(s.get("used_statements") or []),
                    origin="supplied",
                    tex_verified=False,
                    module=s.get("module"),
                    file=s.get("file"),
                    lines=s.get("lines"),
                    axioms=list(s.get("axioms") or []),
                    theorem_info=bool(s.get("theorem_info", True)),
                )
                for s in raw_steps
            ]
            return dict(
                verified=is_verified,
                badge=STEP_VERIFIED_SUPPLIED_BADGE if is_verified else None,
                mode="with_supplied" if is_verified else None,
                step_count=len(steps),
                paper_steps=0,
                supplied_steps=len(steps),
                declaration=step_audit.get("declaration"),
                main_declaration=step_audit.get("main_declaration"),
                main_steps=list(step_audit.get("main_steps") or []),
                main_statements=list(step_audit.get("main_statements") or []),
                step_map_sha256=step_audit.get("step_map_sha256"),
                steps=steps,
            )

        if step_audit.get("step_map_sha256") != step_map["step_map_sha256"]:
            raise ValueError(
                f"{cid}: step_map changed since the recorded Lean step audit; rerun audit_lean.py --step-map"
            )
        audit_by_id = {s["id"]: s for s in (step_audit.get("steps") or [])}
        merged_steps = []
        for s in step_map["steps"]:
            aud = audit_by_id.get(s["id"], {})
            merged = dict(s)
            merged["used_deps"] = list(aud.get("used_deps") or [])
            merged["used_statements"] = list(aud.get("used_statements") or [])
            merged["axioms"] = list(aud.get("axioms") or [])
            merged["theorem_info"] = bool(aud.get("theorem_info", False))
            if aud.get("module"):
                merged["module"] = aud["module"]
            if aud.get("file"):
                merged["file"] = aud["file"]
            if aud.get("lines"):
                merged["lines"] = aud["lines"]
            merged_steps.append(merged)

        is_verified = bool(proof_checked and not changed)
        supplied_count = step_map["supplied_step_count"]
        mode = ("with_supplied" if supplied_count > 0 else "paper") if is_verified else None
        badge = ((STEP_VERIFIED_SUPPLIED_BADGE if supplied_count > 0 else STEP_VERIFIED_PAPER_BADGE)
                 if is_verified else None)
        return dict(
            verified=is_verified,
            badge=badge,
            mode=mode,
            step_count=len(merged_steps),
            paper_steps=step_map["paper_step_count"],
            supplied_steps=supplied_count,
            declaration=step_audit.get("declaration"),
            main_declaration=step_audit.get("main_declaration"),
            main_steps=list(step_audit.get("main_steps") or []),
            main_statements=list(step_audit.get("main_statements") or []),
            step_map_sha256=step_map["step_map_sha256"],
            steps=merged_steps,
        )

    return dict(
        verified=False,
        badge=None,
        mode=None,
        step_count=len(step_map["steps"]),
        paper_steps=step_map["paper_step_count"],
        supplied_steps=step_map["supplied_step_count"],
        main_declaration=step_map["main_declaration"],
        step_map_sha256=step_map["step_map_sha256"],
        steps=list(step_map["steps"]),
    )


def ground_claim_dependencies(claims, records, paper_edges):
    """Cross-reference kernel-extracted Lean constant closures against reader.json dependencies.

    Classifies each claim-to-claim edge as:
      - 'both': Used in both paper & Lean proof
      - 'paper_only': Paper-only dependency (Lean proved independently)
      - 'lean_only': Lean-only prerequisite (not listed in reader.json, transitively reduced)
      - 'paper': Paper dependency whose target claim has no kernel-extracted proof closure yet
    """
    by_id = {c["id"]: c for c in claims}
    rec_by_id = {rec["claim"]["id"]: rec for rec in records}
    order = [c["id"] for c in claims]
    order_idx = {cid: i for i, cid in enumerate(order)}

    expected_to_cid = {}
    decl_to_cid = {}
    for rec in records:
        cid = rec["claim"]["id"]
        w = rec["work"]
        audit = rec.get("audit") or {}
        for holder in (w.get("closure"), w.get("assembly"), w.get("statement_check")):
            if isinstance(holder, dict):
                if holder.get("expected"):
                    expected_to_cid.setdefault(holder["expected"], cid)
                if holder.get("declaration"):
                    decl_to_cid.setdefault(holder["declaration"], cid)
        if audit.get("expected"):
            expected_to_cid.setdefault(audit["expected"], cid)
        if (audit.get("statement") or {}).get("expected"):
            expected_to_cid.setdefault(audit["statement"]["expected"], cid)
        if audit.get("declaration"):
            decl_to_cid.setdefault(audit["declaration"], cid)
        for part in w.get("subproofs", []):
            if part.get("status") == "checked" and part.get("declaration"):
                decl_to_cid.setdefault(part["declaration"], cid)

    has_kernel_dag = {}
    lean_prereqs = {cid: {} for cid in by_id}
    for rec in records:
        cid = rec["claim"]["id"]
        audit = rec.get("audit") or {}
        w = rec["work"]
        is_proof_audited = bool(rec.get("checked") or rec.get("is_conditional"))
        has_closure_fields = is_proof_audited and (
            "used_local_theorems" in audit or "used_local_statements" in audit
        )
        has_kernel_dag[cid] = has_closure_fields
        refs_by_prereq = {}

        def add_ref(dep_cid, lean_name):
            if not dep_cid or dep_cid == cid or dep_cid not in by_id:
                return
            refs_by_prereq.setdefault(dep_cid, set()).add(lean_name)

        if is_proof_audited:
            for thm in audit.get("used_local_theorems") or []:
                add_ref(decl_to_cid.get(thm), thm)
            for stmt in audit.get("used_local_statements") or []:
                add_ref(expected_to_cid.get(stmt), stmt)
            for assumed in audit.get("assumes") or []:
                add_ref(expected_to_cid.get(assumed), assumed)
            for assumed_cid in w.get("assumes") or []:
                if assumed_cid in by_id and assumed_cid != cid:
                    exp_name = None
                    other_w = rec_by_id[assumed_cid]["work"]
                    for holder in (other_w.get("closure"), other_w.get("assembly"), other_w.get("statement_check")):
                        if isinstance(holder, dict) and holder.get("expected"):
                            exp_name = holder["expected"]
                            break
                    add_ref(assumed_cid, exp_name or assumed_cid)
        lean_prereqs[cid] = {k: sorted(v) for k, v in refs_by_prereq.items()}

    def lean_reaches(start, target, forbidden):
        visited = set()
        stack = [start]
        while stack:
            cur = stack.pop()
            if cur in visited or cur == forbidden:
                continue
            visited.add(cur)
            for nxt in lean_prereqs.get(cur, ()):
                if nxt == target:
                    return True
                if nxt not in visited:
                    stack.append(nxt)
        return False

    grounded_edges = []
    paper_pairs = set()
    per_claim_edges = {cid: {"both": [], "paper_only": [], "lean_only": []} for cid in by_id}
    counts = {"both": 0, "paper_only": 0, "lean_only": 0, "paper": 0}

    for edge in paper_edges:
        cid = edge["claim"]
        prereq = edge["prerequisite"]
        if cid not in by_id or prereq not in by_id:
            continue
        paper_pairs.add((cid, prereq))
        refs = lean_prereqs.get(cid, {}).get(prereq)
        if refs:
            grounding = "both"
            item = dict(edge, grounding="both", grounding_label=EDGE_GROUNDING_LABELS["both"], lean_refs=refs)
            per_claim_edges[cid]["both"].append(dict(
                id=prereq, reference=rec_by_id[prereq]["entry"]["reference"], lean_refs=refs,
            ))
        elif has_kernel_dag.get(cid):
            grounding = "paper_only"
            item = dict(edge, grounding="paper_only", grounding_label=EDGE_GROUNDING_LABELS["paper_only"])
            per_claim_edges[cid]["paper_only"].append(dict(
                id=prereq, reference=rec_by_id[prereq]["entry"]["reference"],
            ))
        else:
            grounding = "paper"
            item = dict(edge, grounding="paper", grounding_label=EDGE_GROUNDING_LABELS["paper"])
        counts[grounding] += 1
        grounded_edges.append(item)

    # Emit transitively reduced Lean-only prerequisite edges not already in reader.json.
    for cid in order:
        prereq_map = lean_prereqs.get(cid, {})
        extras = [p for p in prereq_map if (cid, p) not in paper_pairs]
        extras.sort(key=lambda p: order_idx.get(p, len(order)))
        for prereq in extras:
            if any(mid != prereq and lean_reaches(mid, prereq, cid) for mid in prereq_map):
                continue
            refs = prereq_map[prereq]
            reason = "Referenced in Lean proof via " + ", ".join(refs)
            item = dict(
                claim=cid,
                prerequisite=prereq,
                reason=reason,
                grounding="lean_only",
                grounding_label=EDGE_GROUNDING_LABELS["lean_only"],
                lean_refs=refs,
            )
            counts["lean_only"] += 1
            grounded_edges.append(item)
            per_claim_edges[cid]["lean_only"].append(dict(
                id=prereq, reference=rec_by_id[prereq]["entry"]["reference"], lean_refs=refs,
            ))

    per_claim = {}
    for rec in records:
        cid = rec["claim"]["id"]
        audit = rec.get("audit") or {}
        if has_kernel_dag.get(cid) or lean_prereqs.get(cid):
            per_claim[cid] = dict(
                used_local_theorems=list(audit.get("used_local_theorems") or []),
                used_local_statements=list(audit.get("used_local_statements") or []),
                both=per_claim_edges[cid]["both"],
                paper_only=per_claim_edges[cid]["paper_only"],
                lean_only=per_claim_edges[cid]["lean_only"],
            )
    return grounded_edges, per_claim, counts


def _has_supplied_steps(rec):
    sv = rec.get("step_verification")
    return bool(sv and sv.get("supplied_steps", 0) > 0)


def render_supplement_markdown(project, records):
    """Generate dist/supplement.md for claims with basis='supplied' or Lean-supplied proof steps."""
    supplied = [rec for rec in records if rec.get("basis") == "supplied" or _has_supplied_steps(rec)]
    if not supplied:
        return None
    lines = [
        f"# Supplied Proofs Supplement — {project['title']}",
        "",
        f"- **Edition:** {project.get('edition', 'unspecified')}",
    ]
    if project.get("authors"):
        lines.append(f"- **Authors:** {', '.join(project['authors'])}")
    lines.extend([
        "",
        "> **Two Homes Provenance Note:** The claims and intermediate steps collected in this supplement are stated in "
        "the manuscript without a complete written proof (for example, unproved remarks, skipped steps, or Lean-supplied "
        "intermediate steps in a step-verified proof). Their proofs were supplied and checked in Lean outside the "
        "manuscript PDF so readers never mistake a Lean-supplied argument for text present in the paper.",
        "",
        "## Summary of Supplied Proofs",
        "",
        "| Claim | Tier | Status | Lean declaration | Axiom profile | Statement SHA-256 |",
        "| :--- | :--- | :--- | :--- | :--- | :--- |",
    ])
    res_labels = {
        "unconditionally_closed": SUPPLIED_BADGE,
        "conditional": "Conditional (proof supplied outside manuscript)",
        "subproofs_checked": "Subproofs checked (proof supplied outside manuscript)",
        "open": "Open (proof supplied outside manuscript)",
    }
    for rec in supplied:
        cid = rec["claim"]["id"]
        anchor = supplement_anchor(cid)
        ref = f"[{rec['entry']['reference']}](#{anchor}) (`{cid}`)"
        decl = ((rec.get("audit") or {}).get("declaration")
                or (rec["work"].get("closure") or {}).get("declaration")
                or "—")
        decl_cell = f"`{decl}`" if decl != "—" else "—"
        ax = rec["rd"].get("axiom_profile") or "—"
        sha = ((rec.get("audit") or {}).get("statement") or {}).get("sha256")
        sha_cell = f"`{sha[:12]}`" if sha else "—"
        sv = rec.get("step_verification")
        if rec.get("basis") == "supplied":
            status_cell = res_labels[rec["resolution"]]
            if sv and sv.get("verified") and sv.get("badge"):
                status_cell += f" · {sv['badge']}"
        elif sv and sv.get("verified") and sv.get("badge"):
            status_cell = f"{sv['badge']} ({sv['supplied_steps']}/{sv['step_count']} supplied steps)"
        else:
            count = (sv or {}).get("supplied_steps", 0)
            status_cell = f"Supplied proof steps ({count})"
        lines.append(f"| {ref} | {rec['tier']} | {status_cell} | {decl_cell} | {ax} | {sha_cell} |")

    for rec in supplied:
        c = rec["claim"]
        cid = c["id"]
        entry = rec["entry"]
        audit = rec.get("audit") or {}
        sv = rec.get("step_verification")
        is_full_supplied = rec.get("basis") == "supplied"
        anchor = supplement_anchor(cid)
        heading_text = (f"{entry['reference']} — {c['title']} (`{cid}`)"
                        if c.get("title") and c["title"] != cid
                        else f"{entry['reference']} (`{cid}`)")
        if is_full_supplied:
            badge_line = res_labels[rec["resolution"]]
            if sv and sv.get("verified") and sv.get("badge"):
                badge_line += f" · {sv['badge']}"
        elif sv and sv.get("verified") and sv.get("badge"):
            badge_line = sv["badge"]
        else:
            badge_line = "Supplied proof steps (awaiting Lean step audit)"
        lines.extend([
            "",
            f'<a id="{anchor}"></a>',
            f"## {heading_text}",
            "",
            f"- **Manuscript source:** `{c['file']}`, line {c['line']}"
            + (f" (PDF page {entry['page']})" if entry.get("page") else ""),
            f"- **Verification badge:** {badge_line}",
        ])
        if is_full_supplied:
            lines.append(f"- **Proof basis:** `supplied` ({BASIS_LABELS['supplied']})")
        elif rec.get("basis"):
            lines.append(f"- **Proof basis:** `{rec['basis']}` ({BASIS_LABELS.get(rec['basis'], rec['basis'])})")
        if sv and sv.get("supplied_steps"):
            lines.append(
                f"- **Structured step provenance:** {sv['paper_steps']} verbatim paper step(s), "
                f"{sv['supplied_steps']} supplied step(s)"
            )
        decl = audit.get("declaration") or (rec["work"].get("closure") or {}).get("declaration")
        exp = audit.get("expected") or (rec["work"].get("closure") or {}).get("expected")
        if decl:
            lines.append(f"- **Lean declaration:** `{decl}`" + (f" (`{exp}`)" if exp else ""))
        if rec["rd"].get("axiom_profile"):
            lines.append(f"- **Axiom profile:** {rec['rd']['axiom_profile']}")
        metrics = rec.get("proof_metrics")
        if metrics:
            bits = []
            if "checked_lean_loc" in metrics:
                bits.append(f"{metrics['checked_lean_loc']} checked Lean LoC")
            if "reachable_local_defs" in metrics:
                bits.append(f"{metrics['reachable_local_defs']} reachable local defs")
            if "reachable_local_theorems" in metrics:
                bits.append(f"{metrics['reachable_local_theorems']} reachable local theorems")
            if bits:
                lines.append(f"- **Proof size metrics:** {', '.join(bits)}")
        if entry.get("scope"):
            lines.append(f"- **Scope note:** {entry['scope']}")
        lines.extend([
            "",
            "### Manuscript Passage",
            "",
            "```tex",
            c["excerpt"].rstrip("\n"),
            "```",
            "",
        ])
        if is_full_supplied:
            lines.extend(["### Supplied Proof", ""])
            has_written = False
            if entry.get("summary"):
                lines.append(f"**Summary:** {entry['summary']}")
                lines.append("")
                has_written = True
            if entry.get("sketch"):
                lines.append(f"**Proof idea:** {entry['sketch']}")
                lines.append("")
                has_written = True
            if entry.get("steps"):
                lines.append(entry["steps"].rstrip("\n"))
                lines.append("")
                has_written = True
            elif entry.get("structured"):
                lines.append(entry["structured"].rstrip("\n"))
                lines.append("")
                has_written = True
            if not has_written and not (sv and sv.get("supplied_steps")):
                lines.append("_No prose or Lamport proof steps have been written yet; inspect the checked Lean proof declaration in the atlas._")
                lines.append("")
        if sv and sv.get("supplied_steps"):
            lines.extend(["### Supplied Proof Steps (Outside Manuscript)", ""])
            for step in sv["steps"]:
                if step.get("origin") != "supplied":
                    continue
                heading = f"**Step `{step['id']}`**" + (f" — {step['title']}" if step.get("title") else "")
                deps = ", ".join(f"`{d}`" for d in step.get("step_deps") or []) or "none"
                loc = f" (`{step['file']}` L{step['lines'][0]})" if step.get("file") and step.get("lines") else ""
                lines.append(f"- {heading} · Lean lemma `{step['lemma']}`{loc} · `step_deps`: {deps}")
                if step.get("text"):
                    lines.append(f"  {step['text'].strip()}")
            lines.append("")
    return "\n".join(lines).rstrip("\n") + "\n"


def _empty_bucket():
    return dict(
        total=0,
        unconditionally_closed=0,
        conditional=0,
        subproofs_checked=0,
        open=0,
        with_witness=0,
        needs_confirmation=0,
        needs_confirmation_direct=0,
        machine_verified=0,
        author_reviewed=0,
        supplied_proof=0,
        step_verified_paper=0,
        step_verified_with_supplied=0,
    )


def summarize_records(records):
    """Compute multi-resolution counts for headline, supporting, all results, and conjectures."""
    buckets = {
        "headline": _empty_bucket(),
        "supporting": _empty_bucket(),
        "all_results": _empty_bucket(),
        "conjectures": _empty_bucket(),
    }
    for rec in records:
        tier = rec["tier"]
        res = rec["resolution"]
        rd = rec["rd"]
        has_witness = bool(rec["entry"].get("hypotheses"))
        direct_confirm = bool(rd.get("needs_author_confirmation"))
        any_confirm = direct_confirm or bool(rd.get("needs_author_confirmation_via"))
        machine_ok = bool(rec["machine_verified"])
        approved = bool(rd.get("approved"))
        supplied = bool(res == "unconditionally_closed" and rec["entry"].get("basis") == "supplied")
        sv = rec.get("step_verification")
        step_mode = sv.get("mode") if (sv and sv.get("verified")) else None
        targets = (buckets["conjectures"],) if tier == "conjecture" else (buckets[tier], buckets["all_results"])
        for b in targets:
            b["total"] += 1
            b[res] += 1
            if has_witness:
                b["with_witness"] += 1
            if any_confirm:
                b["needs_confirmation"] += 1
            if direct_confirm:
                b["needs_confirmation_direct"] += 1
            if machine_ok:
                b["machine_verified"] += 1
            if approved:
                b["author_reviewed"] += 1
            if supplied:
                b["supplied_proof"] += 1
            if step_mode == "paper":
                b["step_verified_paper"] += 1
            elif step_mode == "with_supplied":
                b["step_verified_with_supplied"] += 1
    return buckets


def _cap_first(text):
    """Uppercase only the leading character so names like Mathlib and Routine/ keep their casing."""
    return text[:1].upper() + text[1:] if text else text


def build_refinement_backlog(project, records):
    """Build the prioritized P1-P5 Open Shortcomings & Refinement Backlog."""
    profile = proof_work_profile(project)
    dependents_of = {}
    for rec in records:
        for via in rec["rd"].get("needs_author_confirmation_via", []):
            dependents_of.setdefault(via["id"], []).append(dict(
                id=rec["claim"]["id"],
                reference=rec["entry"]["reference"],
            ))

    p1, p2, p3, p4, p5 = [], [], [], [], []
    for rec in records:
        cid = rec["claim"]["id"]
        ref = rec["entry"]["reference"]
        tier = rec["tier"]
        rd = rec["rd"]
        w = rec["work"]
        analysis = rd["view"].get("analysis", {})
        cases = analysis.get("cases", [])

        # Priority 1: Needs author confirmation (unattended chosen reading / added hypothesis / restriction).
        if rd.get("needs_author_confirmation"):
            confirm_cases = [
                dict(case=row["case"], kind=row.get("kind", ""), why=row["why"])
                for row in cases
                if row.get("needs_author_confirmation") or row.get("kind") in reviews.CONFIRMATION_KINDS
            ]
            p1.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                cases=confirm_cases,
                dependents=dependents_of.get(cid, []),
                action="Confirm the unattended reading(s) in author review or report a difference.",
            ))

        # Priority 2: Conditional claims waiting on unproved prerequisites.
        if rec["is_conditional"]:
            p2.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                assumes=rec["assumed_items"],
                action="Prove the assumed prerequisite(s) and re-run atlas.py assemble --audit.",
            ))

        # Priority 3: Open weaker conclusion, unapproved noncomputable obligations, and open discrepancies.
        weaker = [
            dict(case=row["case"], paper=row["paper"], lean=row["lean"], why=row["why"])
            for row in cases if row.get("kind") == "weaker conclusion"
        ]
        noncomp = list(rd.get("noncomputable_constants") or [])
        include_noncomp = bool(noncomp and (weaker or not rd.get("approved")))
        open_subs = [part["title"] for part in rec["entry"].get("subproofs", []) if part.get("status") != "checked"]
        open_discrepancy = (rd.get("issue") or "") if (rd.get("disputed") and not weaker) else ""
        if weaker or include_noncomp or open_discrepancy:
            if weaker and include_noncomp:
                action = "Prove the omitted weaker-conclusion clause(s) and verify whether noncomputable definitions affect algorithmic/explicitness claims."
            elif weaker:
                action = "Prove the omitted weaker-conclusion clause(s) and close the remaining open subproof(s)."
            elif open_discrepancy and include_noncomp:
                action = "Resolve the open paper-to-Lean discrepancy and verify whether noncomputable definitions affect algorithmic/explicitness claims."
            elif open_discrepancy:
                action = rd.get("next") or "Resolve the open paper-to-Lean discrepancy and repeat the correspondence comparison."
            else:
                action = "Verify whether noncomputable definitions affect any algorithmic or explicitness claim and record author review."
            p3.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                weaker_conclusions=weaker,
                noncomputable_constants=noncomp if include_noncomp else [],
                open_subproofs=open_subs if (weaker or open_discrepancy) else [],
                **({"open_discrepancy": open_discrepancy} if open_discrepancy else {}),
                action=action,
            ))

        # Priority 4: Missing --witness examples and unresolved default-value flags.
        missing_witness = bool(
            tier != "conjecture"
            and (rec["checked"] or rec["is_conditional"] or rd.get("statement_checked"))
            and not rec["entry"].get("hypotheses")
        )
        unres_defaults = rec["unresolved_defaults"]
        if missing_witness or unres_defaults:
            parts = []
            if missing_witness:
                parts.append("add a non-degenerate --witness example")
            if unres_defaults:
                parts.append(f"resolve {len(unres_defaults)} default-value flag(s)")
            p4.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                missing_witness=missing_witness,
                witness_plan=rec["witness_plan"] if missing_witness else None,
                unresolved_defaults=unres_defaults,
                action=_cap_first(" and ".join(parts)) + ".",
            ))

        # Priority 5: Deferred Mathlib bridging lemmas and undistilled exploratory proofs.
        bridging = rec["deferred_bridging_lemmas"]
        undistilled = rec["undistilled"]
        if bridging or undistilled:
            parts = []
            if bridging:
                parts.append(f"prove {len(bridging)} deferred Mathlib bridging lemma(s)")
            if undistilled:
                parts.append("distill exploratory proof into Routine/ and mark distilled: true")
            p5.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                deferred_bridging_lemmas=bridging,
                undistilled=undistilled,
                action=_cap_first(" and ".join(parts)) + ".",
            ))

    groups = [
        dict(priority=1, key="needs_author_confirmation", title="Needs author confirmation", items=p1),
        dict(priority=2, key="conditional_claims", title="Conditional claims waiting on unproved prerequisites", items=p2),
        dict(priority=3, key="weaker_or_noncomputable", title="Open weaker-conclusion and noncomputable obligations", items=p3),
        dict(priority=4, key="witnesses_and_defaults", title="Missing hypothesis witnesses and unresolved default-value flags", items=p4),
        dict(priority=5, key="bridging_and_distillation", title="Deferred Mathlib bridging lemmas and undistilled proofs", items=p5),
    ]
    return dict(
        profile=profile,
        total_items=sum(len(g["items"]) for g in groups),
        priorities=groups,
    )


def render_summary_table(summary, *, compact=False):
    """Render the headline vs. supporting vs. conjectures multi-resolution table."""
    show_supplied = any(b["supplied_proof"] for b in summary.values())

    def row(label, b, extra_cls=""):
        cls = f' class="{extra_cls}"' if extra_cls else ""
        supplied_td = f"<td>{b['supplied_proof']}</td>" if show_supplied else ""
        return (
            f"<tr{cls}><th scope=\"row\">{esc(label)}</th>"
            f"<td>{b['total']}</td>"
            f"<td>{b['unconditionally_closed']}</td>"
            f"{supplied_td}"
            f"<td>{b['conditional']}</td>"
            f"<td>{b['subproofs_checked']}</td>"
            f"<td>{b['open']}</td>"
            f"<td>{b['with_witness']}/{b['total']}</td>"
            f"<td>{b['needs_confirmation']}</td>"
            f"<td>{b['machine_verified']}/{b['total']}</td>"
            f"<td>{b['author_reviewed']}/{b['total']}</td></tr>"
        )

    rows = [
        row("Headline results", summary["headline"]),
        row("Supporting results", summary["supporting"]),
        row("All stated results", summary["all_results"], "summary-total"),
    ]
    if summary["conjectures"]["total"]:
        rows.append(row("Conjectures (separate)", summary["conjectures"], "summary-conjecture"))
    caption = ("Verification breakdown by claim tier" if not compact
               else "Headline vs. supporting verification summary")
    supplied_th = "<th>Supplied proof</th>" if show_supplied else ""
    return (
        '<div class="summary-table">'
        f'<table><caption>{esc(caption)}</caption>'
        '<thead><tr><th>Category</th><th>Total</th><th>Unconditionally closed</th>'
        f'{supplied_th}<th>Conditional</th><th>Subproofs checked</th><th>Open</th>'
        '<th>Witness</th><th>Needs confirmation</th><th>CI verified</th><th>Author reviewed</th></tr></thead>'
        '<tbody>' + "".join(rows) + '</tbody></table></div>'
    )


def render_backlog_section(backlog):
    """Render the prioritized Open Shortcomings & Refinement Backlog for progress.html."""
    if not backlog["total_items"]:
        return ""
    intro = (
        "This atlas currently uses the <strong>quick</strong> triage profile; every deferred check is itemized below "
        "and can be refined iteratively without redoing <code>Statements/</code>."
        if backlog["profile"] == "quick" else
        "Open shortcomings and deferred refinement obligations are ordered by priority below."
    )
    blocks = []
    for group in backlog["priorities"]:
        if not group["items"]:
            continue
        items_html = []
        for item in group["items"]:
            cid = item["claim"]
            url = claim_url(cid)
            rurl = reviews.review_url(cid)
            head = f'<a href="{url}?view=lean"><strong>{esc(item["reference"])}</strong></a> (<a href="{rurl}">Review</a>)'
            details = []
            if group["key"] == "needs_author_confirmation":
                if item["cases"]:
                    details.append("; ".join(f'{c["kind"]}: {c["case"]}' for c in item["cases"]))
                if item["dependents"]:
                    details.append("affects dependents: " + ", ".join(d["reference"] for d in item["dependents"]))
            elif group["key"] == "conditional_claims":
                deps = ", ".join(a["reference"] for a in item["assumes"])
                details.append(f"assumes unproved prerequisite(s): {deps}")
            elif group["key"] == "weaker_or_noncomputable":
                if item["weaker_conclusions"]:
                    details.append("weaker conclusion: " + "; ".join(w["case"] for w in item["weaker_conclusions"]))
                if item.get("open_discrepancy"):
                    details.append("open discrepancy: " + item["open_discrepancy"])
                if item["noncomputable_constants"]:
                    details.append("noncomputable: " + ", ".join(item["noncomputable_constants"]))
                if item["open_subproofs"]:
                    details.append("open subproofs: " + ", ".join(item["open_subproofs"]))
            elif group["key"] == "witnesses_and_defaults":
                if item["missing_witness"]:
                    plan = item["witness_plan"] or {}
                    extra = f' ({plan.get("mode", "available")}: {plan.get("action", "")})' if plan else ""
                    if plan.get("missing_result"):
                        extra += f' — needs: {plan["missing_result"]}'
                    details.append(NO_EXAMPLE + extra)
                if item["unresolved_defaults"]:
                    flags = ", ".join(f'{d["construct"]} in {d["constant"]} [{d["status"]}]' for d in item["unresolved_defaults"])
                    details.append(f'unresolved default-value flag(s) ({len(item["unresolved_defaults"])}): {flags}')
            elif group["key"] == "bridging_and_distillation":
                if item["deferred_bridging_lemmas"]:
                    details.append("deferred bridging lemma(s): " + "; ".join(item["deferred_bridging_lemmas"]))
                if item["undistilled"]:
                    details.append("Exploratory proof (undistilled)")
            detail_text = " · ".join(details)
            items_html.append(
                f'<li>{head}' + (f' — {esc(detail_text)}' if detail_text else '')
                + f'<br><span class="backlog-action">{esc(item["action"])}</span></li>'
            )
        blocks.append(
            f'<div class="backlog-group" data-priority="{group["priority"]}">'
            f'<h3>P{group["priority"]} · {esc(group["title"])} ({len(group["items"])})</h3>'
            f'<ul>{"".join(items_html)}</ul></div>'
        )
    return (
        '<section id="refinement-backlog" class="shortcoming-banner">'
        f'<h2>Open Shortcomings &amp; Refinement Backlog ({backlog["total_items"]})</h2>'
        f'<p>{intro}</p>'
        + "".join(blocks)
        + '</section>'
    )


def _collect_claim_states(root, project, claims, *, ci=None):
    """Collect read-only claim states, resolutions, and propagated confirmations."""
    by_id = {c["id"]: c for c in claims}
    work = project.get("work", {})
    materials = json.loads(local(root, project["reader"]).read_text(encoding="utf-8-sig")) if project.get("reader") else {}
    notes = materials.get("claims", {})
    edges = materials.get("dependencies", [])
    comparisons = reviews.read(root / "comparisons.json", {})
    profile = proof_work_profile(project)
    tex_sources = load_bound_tex_sources(root, project)

    prereqs_by_cid = {c["id"]: set() for c in claims}
    for edge in edges:
        if edge["claim"] in prereqs_by_cid and edge["prerequisite"] in by_id:
            prereqs_by_cid[edge["claim"]].add(edge["prerequisite"])

    records = []
    for c in claims:
        cid = c["id"]
        w = work.get(cid, {})
        m = notes.get(cid, {})
        tier = claim_tier(c, m, w)
        basis = claim_basis(cid, m, w)
        entry = {**c, **m, **w}
        entry.setdefault("reference", c["kind"].title())
        entry["tier"] = tier
        entry["headline"] = tier == "headline"
        if basis is not None:
            entry["basis"] = basis
        if m.get("lamport"):
            entry["steps"] = local(root, m["lamport"]).read_text(encoding="utf-8-sig")

        audit = None
        receipt_bytes = None
        checked = False
        is_conditional = False
        statement_checked = False
        changed = False
        assumed_items = []
        status = w.get("status", "open")

        if status in ("closed", "conditional") or w.get("statement_check"):
            try:
                audit, checked = current_statement_audit(root, cid, w)
                statement_checked = True
                if status == "conditional":
                    is_conditional = True
                    assumed_items = _resolve_assumes_items(audit.get("assumes", []), w.get("assumes", []), by_id, work, notes)
                    for item in assumed_items:
                        if item["id"] in by_id:
                            prereqs_by_cid[cid].add(item["id"])
                if status in ("closed", "conditional") and w.get("closure", {}).get("audit"):
                    receipt_bytes = local(root, w["closure"]["audit"]).read_bytes()
            except (ValueError, OSError):
                if w.get("checked_inputs"):
                    changed = any(
                        not local(root, path).is_file() or hashlib.sha256(local(root, path).read_bytes()).hexdigest() != digest
                        for path, digest in w.get("checked_inputs", {}).items()
                    )
        for dep in w.get("assumes", []):
            if dep in by_id:
                prereqs_by_cid[cid].add(dep)

        entry["hypotheses"] = (audit or {}).get("hypotheses")
        metrics = extract_proof_metrics(audit)
        if metrics:
            entry["proof_metrics"] = metrics
        undistilled = _is_undistilled(cid, w, profile, checked, is_conditional)
        distilled = w.get("distilled") if isinstance(w.get("distilled"), bool) else None
        if distilled is not None:
            entry["distilled"] = distilled
        if undistilled:
            entry["undistilled"] = True
        default_main = ((w.get("assembly") or {}).get("declaration")
                        or (w.get("closure") or {}).get("declaration")
                        or (audit or {}).get("declaration"))
        step_map = resolve_claim_step_map(root, cid, w, m, tex_sources, default_main=default_main)
        step_verif = evaluate_step_verification(
            cid, step_map, audit, proof_checked=(checked or is_conditional), changed=changed,
        )
        if step_verif is not None:
            entry["step_verification"] = step_verif
        has_supp_entry = basis == "supplied" or bool(step_verif and step_verif.get("supplied_steps", 0) > 0)
        supp_url = f"supplement.md#{supplement_anchor(cid)}" if has_supp_entry else ""
        subproofs = []
        for part in w.get("subproofs", []):
            state = part["status"]
            if state == "checked" and changed:
                state = "awaiting recheck"
            subproofs.append(dict(part, status=state))
        entry["subproofs"] = subproofs
        has_parts = any(part["status"] == "checked" for part in subproofs)

        rd = reviews.packet(
            root, project, c, w, audit, comparisons.get(cid), reviews.history(root, cid),
            checked, statement_checked,
            conditional=is_conditional,
            assumes=[item["reference"] for item in assumed_items] if is_conditional else (),
            basis=basis, proof_metrics=metrics, distilled=distilled, undistilled=undistilled,
            supplement_url=supp_url, step_verification=step_verif,
        )
        rd["witness"] = reviews.witness_source(root, w, audit) if audit else None
        machine_verified = False
        if checked and project.get("hosting", {}).get("lean_ci") == "enabled":
            machine_verified, _, _, _ = _ci_claim_status(audit, receipt_bytes, ci, cid)

        res = claim_resolution(checked, is_conditional, rd["disputed"], has_parts)
        entry["resolution"] = res
        records.append(dict(
            claim=c,
            entry=entry,
            work=w,
            note=m,
            rd=rd,
            audit=audit,
            tier=tier,
            basis=basis,
            proof_metrics=metrics,
            distilled=distilled,
            step_verification=step_verif,
            resolution=res,
            checked=checked,
            is_conditional=is_conditional,
            has_parts=has_parts,
            changed=changed,
            assumed_items=assumed_items,
            unresolved_defaults=unresolved_defaults(rd),
            deferred_bridging_lemmas=_deferred_bridging_lemmas(cid, w),
            undistilled=undistilled,
            witness_plan=witness_plan(project, w, rd["witness"]) if tier != "conjecture" else None,
            machine_verified=machine_verified,
        ))

    grounded_edges, per_claim_deps, _ = ground_claim_dependencies(claims, records, edges)
    for edge in grounded_edges:
        if edge["claim"] in prereqs_by_cid and edge["prerequisite"] in by_id:
            prereqs_by_cid[edge["claim"]].add(edge["prerequisite"])
    for rec in records:
        cid = rec["claim"]["id"]
        if cid in per_claim_deps:
            rec["entry"]["lean_dependencies"] = per_claim_deps[cid]

    direct_confirm = {rec["claim"]["id"] for rec in records if rec["rd"].get("needs_author_confirmation")}
    order_ids = [rec["claim"]["id"] for rec in records]
    for rec in records:
        cid = rec["claim"]["id"]
        visited = set()
        stack = list(prereqs_by_cid.get(cid, ()))
        while stack:
            cur = stack.pop()
            if cur in visited or cur == cid:
                continue
            visited.add(cur)
            stack.extend(prereqs_by_cid.get(cur, ()))
        via_ids = [u for u in order_ids if u in visited and u in direct_confirm]
        rec["rd"]["needs_author_confirmation_via"] = [
            dict(id=u, reference=_claim_ref_label(u, by_id, notes), review_url=reviews.review_url(u))
            for u in via_ids
        ]
    return records


def _latex_escape(text):
    """Escape plain text and common Unicode math/punctuation symbols for pdfLaTeX safety."""
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "≤": r"$\le$",
        "≥": r"$\ge$",
        "≠": r"$\neq$",
        "→": r"$\to$",
        "←": r"$\leftarrow$",
        "↔": r"$\leftrightarrow$",
        "∀": r"$\forall$",
        "∃": r"$\exists$",
        "∧": r"$\land$",
        "∨": r"$\lor$",
        "¬": r"$\neg$",
        "∈": r"$\in$",
        "∉": r"$\notin$",
        "⊆": r"$\subseteq$",
        "×": r"$\times$",
        "·": r"$\cdot$",
        "∞": r"$\infty$",
        "ℝ": r"$\mathbb{R}$",
        "ℕ": r"$\mathbb{N}$",
        "ℤ": r"$\mathbb{Z}$",
        "ℚ": r"$\mathbb{Q}$",
        "−": "-",
        "–": "--",
        "—": "---",
        "’": "'",
        "‘": "`",
        "“": "``",
        "”": "''",
        "…": r"\ldots{}",
        "₀": r"$_0$", "₁": r"$_1$", "₂": r"$_2$", "₃": r"$_3$", "₄": r"$_4$",
        "₅": r"$_5$", "₆": r"$_6$", "₇": r"$_7$", "₈": r"$_8$", "₉": r"$_9$",
        "⁰": r"$^0$", "¹": r"$^1$", "²": r"$^2$", "³": r"$^3$", "⁴": r"$^4$",
        "⁵": r"$^5$", "⁶": r"$^6$", "⁷": r"$^7$", "⁸": r"$^8$", "⁹": r"$^9$",
    }
    return "".join(replacements.get(ch, ch) for ch in str(text))


def _collect_pinned_metadata(root, project, records, ci):
    """Collect pinned toolchain, Mathlib SHA, external packages, axioms, statement digests, and URLs."""
    from audit_lean import axiom_profile as format_axiom_profile, external_packages as read_external_packages

    toolchains = set()
    pkg_dirs = set()
    ext_by_key = {}
    axioms_union = set()
    axiom_profiles = set()
    statement_digests = []
    stmt_files = {}

    for rec in records:
        w = rec["work"]
        audit = rec["audit"]
        for holder in (w.get("closure"), w.get("statement_check"), w.get("assembly")):
            if isinstance(holder, dict) and holder.get("package"):
                pkg_dirs.add(holder["package"])
        if not audit:
            continue
        if audit.get("toolchain"):
            toolchains.add(audit["toolchain"])
        for pkg in audit.get("external_packages") or []:
            key = (pkg.get("name", ""), pkg.get("rev", ""))
            ext_by_key.setdefault(key, dict(pkg))
        if "axioms" in audit:
            axioms_union.update(audit["axioms"])
            axiom_profiles.add(rec["rd"].get("axiom_profile") or format_axiom_profile(audit["axioms"]))
        stmt = audit.get("statement") or {}
        if stmt.get("sha256"):
            statement_digests.append(dict(
                claim=rec["claim"]["id"],
                reference=rec["entry"]["reference"],
                expected=stmt.get("expected") or audit.get("expected") or "",
                sha256=stmt["sha256"],
            ))
        pkg_prefix = ((w.get("closure") or w.get("statement_check") or {}).get("package") or "")
        for rel, h in (audit.get("checked_inputs") or {}).items():
            if rel == "Statements.lean" or rel.startswith("Statements/"):
                full_rel = (Path(pkg_prefix) / rel).as_posix() if pkg_prefix else rel
                stmt_files[full_rel] = h

    for pkg in sorted(pkg_dirs):
        try:
            pkg_root = local(root, pkg)
        except ValueError:
            continue
        tc_path = pkg_root / "lean-toolchain"
        if tc_path.is_file():
            tc = tc_path.read_text(encoding="utf-8-sig").strip()
            if tc:
                toolchains.add(tc)
        manifest_path = pkg_root / "lake-manifest.json"
        if manifest_path.is_file():
            try:
                for entry in read_external_packages(pkg_root):
                    key = (entry.get("name", ""), entry.get("rev", ""))
                    ext_by_key.setdefault(key, entry)
            except (OSError, ValueError):
                pass

    ext_list = sorted(ext_by_key.values(), key=lambda p: (p.get("name", "").casefold(), p.get("rev", "")))
    mathlib = next((p for p in ext_list if p.get("name", "").casefold() == "mathlib"), None)
    third_party = [p for p in ext_list if p.get("third_party")]

    agg_digest = None
    if statement_digests:
        payload = "".join(f"{item['claim']} {item['expected']} {item['sha256']}\n" for item in statement_digests)
        agg_digest = hashlib.sha256(payload.encode("utf-8")).hexdigest()
    elif stmt_files:
        payload = "".join(f"{k} {v}\n" for k, v in sorted(stmt_files.items()))
        agg_digest = hashlib.sha256(payload.encode("utf-8")).hexdigest()

    hosting = project.get("hosting") or {}
    site_url = hosting.get("site") or ""
    repo_url = hosting.get("repository") or ""
    atlas_url = site_url or repo_url
    ci_commit = ci["commit"] if ci else ""
    ci_run_url = (f"{repo_url}/actions/runs/{ci['run_id']}/attempts/{ci['attempt']}"
                  if ci and repo_url else "")
    ci_level = ci.get("ci_level", "standard") if ci else None
    kernels_checked = []
    if ci:
        seen_k = []
        for k in (ci.get("kernels_checked") or ["lean-kernel"]):
            if k not in seen_k:
                seen_k.append(k)
        for rec_ci in (ci.get("claims") or {}).values():
            for k in (rec_ci.get("kernels_checked") or []):
                if k not in seen_k:
                    seen_k.append(k)
        kernels_checked = seen_k

    return dict(
        toolchains=sorted(toolchains),
        mathlib=mathlib,
        external_packages=ext_list,
        third_party_packages=third_party,
        axioms=sorted(axioms_union),
        axiom_profiles=sorted(axiom_profiles),
        aggregate_axiom_profile=format_axiom_profile(sorted(axioms_union)) if axiom_profiles else "Not yet audited",
        statement_digests=statement_digests,
        statements_files_digests=dict(sorted(stmt_files.items())),
        aggregate_statement_digest=agg_digest,
        atlas_url=atlas_url,
        site_url=site_url,
        repository_url=repo_url,
        hosting_decision=hosting.get("decision", "pending"),
        lean_ci=hosting.get("lean_ci", "not configured"),
        lean_ci_level=lean_ci_level(project),
        ci_level=ci_level,
        kernels_checked=kernels_checked,
        ci_commit=ci_commit,
        ci_run_url=ci_run_url,
    )


def _collect_scope_caveats(records):
    """Collect every active non-agrees comparison case, conditional assumption, noncomputable def, and scope note."""
    caveats = []
    for rec in records:
        cid = rec["claim"]["id"]
        ref = rec["entry"]["reference"]
        tier = rec["tier"]
        rd = rec["rd"]
        analysis = rd["view"].get("analysis", {})
        typed_non_agrees = False
        for row in analysis.get("cases", []):
            kind = row.get("kind")
            if kind and kind != "agrees":
                typed_non_agrees = True
                caveats.append(dict(
                    claim=cid,
                    reference=ref,
                    tier=tier,
                    kind=kind,
                    case=row["case"],
                    paper=row["paper"],
                    lean=row["lean"],
                    why=row["why"],
                    needs_author_confirmation=bool(
                        row.get("needs_author_confirmation")
                        or (rd.get("needs_author_confirmation") and kind in reviews.CONFIRMATION_KINDS)
                    ),
                ))
        if rd.get("disputed") and not typed_non_agrees and rd.get("issue"):
            caveats.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                kind="discrepancy",
                result=rd.get("result") or "difference",
                note=rd["issue"],
            ))
        if rec["is_conditional"]:
            caveats.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                kind="conditional",
                assumes=rec["assumed_items"],
            ))
        if rd.get("noncomputable_constants"):
            caveats.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                kind="noncomputable",
                constants=list(rd["noncomputable_constants"]),
            ))
        if rd.get("author_scope"):
            caveats.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                kind="author_scope",
                note=rd["author_scope"],
            ))
        if rd.get("stronger_result"):
            caveats.append(dict(
                claim=cid,
                reference=ref,
                tier=tier,
                kind="stronger_result",
                note=rd["stronger_result"],
            ))
    return caveats


def _render_manifest_latex(project, summary, caveats, backlog, pinned):
    """Deterministically generate a paste-ready LaTeX verification scope paragraph."""
    h = summary["headline"]
    s = summary["supporting"]
    a = summary["all_results"]
    conj = summary["conjectures"]
    profile = proof_work_profile(project)

    def state_phrase(b, noun):
        parts = [f"{b['unconditionally_closed']}/{b['total']} {noun} unconditionally closed"]
        if b["conditional"]:
            parts.append(f"{b['conditional']} conditional")
        if b["subproofs_checked"]:
            parts.append(f"{b['subproofs_checked']} with subproofs checked")
        if b["supplied_proof"]:
            parts.append(f"{b['supplied_proof']} with Lean-supplied proofs")
        if b["open"]:
            parts.append(f"{b['open']} open")
        return ", ".join(parts)

    sentences = []
    tier_clauses = []
    if h["total"]:
        tier_clauses.append(state_phrase(h, "headline results"))
    if s["total"]:
        tier_clauses.append(state_phrase(s, "supporting results"))
    if not tier_clauses:
        tier_clauses.append("no stated results inventoried yet")
    coverage = (
        f"We formalized results from this manuscript in Lean~4 using Proof Atlas"
        f"{' (currently in \\texttt{quick} triage profile)' if profile == 'quick' else ''}: "
        + "; and ".join(tier_clauses)
    )
    if conj["total"]:
        coverage += f" ({conj['total']} conjecture{'s' if conj['total'] != 1 else ''} tracked separately)"
    coverage += "."
    sentences.append(coverage)
    if a["supplied_proof"] or conj["supplied_proof"]:
        total_supplied = a["supplied_proof"] + conj["supplied_proof"]
        sentences.append(
            f"For {total_supplied} claim{'s' if total_supplied != 1 else ''} stated without a complete manuscript proof, "
            "Lean supplies the derivation outside the PDF (collected in \\texttt{supplement.md})."
        )
    sv_paper = a["step_verified_paper"] + conj["step_verified_paper"]
    sv_supp = a["step_verified_with_supplied"] + conj["step_verified_with_supplied"]
    if sv_paper or sv_supp:
        sv_total = sv_paper + sv_supp
        parts = []
        if sv_paper:
            parts.append(f"{sv_paper} matching verbatim manuscript steps (\\texttt{{{_latex_escape(STEP_VERIFIED_PAPER_BADGE)}}})")
        if sv_supp:
            parts.append(
                f"{sv_supp} with Lean-supplied intermediate steps collected in \\texttt{{supplement.md}} "
                f"(\\texttt{{{_latex_escape(STEP_VERIFIED_SUPPLIED_BADGE)}}})"
            )
        sentences.append(
            f"At the proof-body level, {sv_total} claim{'s are' if sv_total != 1 else ' is'} 1:1 step-verified via "
            "compiled \\texttt{Expr} auditing (" + "; ".join(parts) + ")."
        )

    # Verification tier (CI vs local-only).
    if a["machine_verified"]:
        paranoid_ci = (pinned.get("ci_level") == "paranoid"
                       and any(k != "lean-kernel" for k in pinned.get("kernels_checked") or []))
        if paranoid_ci:
            kernels_tex = ", ".join(f"\\texttt{{{_latex_escape(k)}}}" for k in pinned["kernels_checked"])
            ci_note = (
                f"Of {a['unconditionally_closed']} unconditionally closed results, "
                f"{a['machine_verified']} {'was' if a['machine_verified'] == 1 else 'were'} "
                f"independently rebuilt and re-verified in GitHub Actions paranoid CI (kernels: {kernels_tex})"
            )
        else:
            ci_note = (
                f"Of {a['unconditionally_closed']} unconditionally closed results, "
                f"{a['machine_verified']} {'was' if a['machine_verified'] == 1 else 'were'} "
                f"independently rebuilt in GitHub Actions CI"
            )
        if pinned["ci_commit"]:
            ci_note += f" at commit \\texttt{{{_latex_escape(pinned['ci_commit'][:12])}}}"
        ci_note += "."
        sentences.append(ci_note)
    elif a["unconditionally_closed"] or a["conditional"]:
        sentences.append("Current Lean checks were audited locally (no GitHub Actions CI verification receipt is attached to this revision).")

    # Active scope caveats.
    caveat_bits = []
    for cav in caveats:
        ref = _latex_escape(cav["reference"])
        kind = cav["kind"]
        if kind == "conditional":
            deps = ", ".join(_latex_escape(d["reference"]) for d in cav["assumes"])
            caveat_bits.append(f"{ref} (conditional on {deps})")
        elif kind == "noncomputable":
            names = ", ".join(f"\\texttt{{{_latex_escape(n)}}}" for n in cav["constants"])
            caveat_bits.append(f"{ref} (noncomputable: {names})")
        elif kind == "author_scope":
            caveat_bits.append(f"{ref} (author scope note: {_latex_escape(cav['note'])})")
        elif kind == "stronger_result":
            caveat_bits.append(f"{ref} (Lean proves stronger result: {_latex_escape(cav['note'])})")
        elif kind == "discrepancy":
            tag = "open question" if cav.get("result") == "unsure" else "open discrepancy"
            caveat_bits.append(f"{ref} ({tag}: {_latex_escape(cav['note'])})")
        else:
            confirm_tag = "; awaits author confirmation" if cav.get("needs_author_confirmation") else ""
            caveat_bits.append(f"{ref} ({_latex_escape(kind)} on {_latex_escape(cav['case'])}{confirm_tag})")
    if caveat_bits:
        sentences.append("Active formalization scope caveats: " + "; ".join(caveat_bits) + ".")
    else:
        sentences.append("No non-agreeing formalization scope caveats are recorded across compared statements.")

    # Deferred / refinement checks (witnesses, unresolved defaults, bridging, distillation).
    deferred_bits = []
    by_key = {g["key"]: g["items"] for g in backlog["priorities"]}
    if by_key["needs_author_confirmation"]:
        refs = ", ".join(_latex_escape(i["reference"]) for i in by_key["needs_author_confirmation"])
        deferred_bits.append(f"unattended readings awaiting author confirmation ({refs})")
    missing_w = [i for i in by_key["witnesses_and_defaults"] if i["missing_witness"]]
    if missing_w:
        refs = ", ".join(_latex_escape(i["reference"]) for i in missing_w)
        deferred_bits.append(f"missing non-vacuity hypothesis witnesses ({refs})")
    unres_d = [i for i in by_key["witnesses_and_defaults"] if i["unresolved_defaults"]]
    if unres_d:
        total_flags = sum(len(i["unresolved_defaults"]) for i in unres_d)
        refs = ", ".join(_latex_escape(i["reference"]) for i in unres_d)
        deferred_bits.append(f"{total_flags} unresolved Lean default-value flag{'s' if total_flags != 1 else ''} ({refs})")
    bridging = [i for i in by_key["bridging_and_distillation"] if i["deferred_bridging_lemmas"]]
    if bridging:
        refs = ", ".join(_latex_escape(i["reference"]) for i in bridging)
        deferred_bits.append(f"deferred Mathlib bridging lemmas ({refs})")
    undist = [i for i in by_key["bridging_and_distillation"] if i["undistilled"]]
    if undist:
        refs = ", ".join(_latex_escape(i["reference"]) for i in undist)
        deferred_bits.append(f"undistilled exploratory proofs ({refs})")
    if deferred_bits:
        sentences.append("Deferred checks and open refinement items: " + "; ".join(deferred_bits) + ".")
    elif a["with_witness"] and a["total"]:
        sentences.append(f"Non-vacuity hypothesis witnesses are checked for {a['with_witness']}/{a['total']} stated results.")

    # Pinned environment, digests, and atlas URL.
    env_bits = []
    if pinned["toolchains"]:
        env_bits.append("Lean toolchain " + ", ".join(f"\\texttt{{{_latex_escape(t)}}}" for t in pinned["toolchains"]))
    if pinned["mathlib"]:
        env_bits.append(f"Mathlib commit \\texttt{{{_latex_escape(pinned['mathlib']['rev'][:12])}}}")
    if pinned["third_party_packages"]:
        tp = ", ".join(f"\\texttt{{{_latex_escape(p['name'])}}} (\\texttt{{{_latex_escape(p['rev'][:12])}}})"
                       for p in pinned["third_party_packages"])
        env_bits.append(f"third-party packages {tp}")
    env_bits.append(f"axiom profile: {_latex_escape(pinned['aggregate_axiom_profile'])}")
    if pinned["aggregate_statement_digest"]:
        env_bits.append(f"statement digest \\texttt{{{_latex_escape(pinned['aggregate_statement_digest'][:12])}}}")
    provenance = "Pinned verification artifacts: " + "; ".join(env_bits) + "."
    if pinned["atlas_url"]:
        provenance += f" The interactive Proof Atlas and full audit logs are available at \\url{{{pinned['atlas_url']}}}."
    else:
        provenance += " The Proof Atlas is currently maintained locally."
    sentences.append(provenance)
    sentences.append("Plain-English and structured explanations, as well as any external numerical scripts, are outside Lean's kernel check.")
    return "\\paragraph{Formal Verification and Scope.}\n" + " ".join(sentences) + "\n"


def _render_manifest_markdown(project, records, summary, caveats, backlog, pinned, latex_snippet,
                              *, dag_grounding=None, has_supplement=False):
    """Deterministically generate dist/VERIFICATION.md."""
    profile = proof_work_profile(project)
    lines = [
        f"# Formal Verification Manifest — {project['title']}",
        "",
        f"- **Edition:** {project.get('edition', 'unspecified')}",
    ]
    if project.get("authors"):
        lines.append(f"- **Authors:** {', '.join(project['authors'])}")
    lines.append(f"- **Resolution profile:** `{profile}`")
    if pinned["atlas_url"]:
        lines.append(f"- **Proof Atlas URL:** {pinned['atlas_url']}")
    else:
        lines.append("- **Proof Atlas URL:** Local-only (not publicly hosted)")
    if pinned["repository_url"] and pinned["repository_url"] != pinned["atlas_url"]:
        lines.append(f"- **Repository:** {pinned['repository_url']}")
    if pinned["ci_run_url"]:
        kernels_md = ", ".join(f"`{k}`" for k in (pinned.get("kernels_checked") or ["lean-kernel"]))
        lines.append(
            f"- **GitHub Actions CI run:** {pinned['ci_run_url']} (`{pinned['ci_commit']}`) "
            f"· level: `{pinned.get('ci_level') or 'standard'}` · kernels: {kernels_md}"
        )
    else:
        lines.append(
            f"- **Verification tier:** Local Lean audit (`lean_ci`: `{pinned['lean_ci']}`, "
            f"`lean_ci_level`: `{pinned['lean_ci_level']}`)"
        )

    show_supplied = any(b["supplied_proof"] for b in summary.values())
    lines.extend(["", "## Verification Summary", ""])
    if show_supplied:
        lines.append("| Category | Total | Unconditionally closed | Conditional | Subproofs checked | Lean-supplied proof | Open | With witness | Needs confirmation | Machine verified (CI) | Author reviewed |")
        lines.append("| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")
    else:
        lines.append("| Category | Total | Unconditionally closed | Conditional | Subproofs checked | Open | With witness | Needs confirmation | Machine verified (CI) | Author reviewed |")
        lines.append("| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")

    def md_row(label, b):
        cols = [
            label, str(b["total"]), str(b["unconditionally_closed"]), str(b["conditional"]),
            str(b["subproofs_checked"]),
        ]
        if show_supplied:
            cols.append(str(b["supplied_proof"]))
        cols.extend([
            str(b["open"]), f"{b['with_witness']}/{b['total']}",
            str(b["needs_confirmation"]), f"{b['machine_verified']}/{b['total']}",
            f"{b['author_reviewed']}/{b['total']}",
        ])
        return "| " + " | ".join(cols) + " |"

    lines.append(md_row("Headline results", summary["headline"]))
    lines.append(md_row("Supporting results", summary["supporting"]))
    lines.append(md_row("**All stated results**", summary["all_results"]))
    if summary["conjectures"]["total"]:
        lines.append(md_row("Conjectures (tracked separately)", summary["conjectures"]))

    lines.extend(["", "## Active Scope Caveats", ""])
    if not caveats:
        lines.append("None recorded across currently compared claims.")
    else:
        for cav in caveats:
            ref = f"**{cav['reference']}** (`{cav['claim']}`)"
            kind = cav["kind"]
            if kind == "conditional":
                deps = ", ".join(f"{a['reference']} (`{a['expected']}`)" for a in cav["assumes"])
                lines.append(f"- {ref} — **Conditional**: assumes unproved prerequisite(s): {deps}.")
            elif kind == "noncomputable":
                names = ", ".join(f"`{n}`" for n in cav["constants"])
                lines.append(f"- {ref} — **`noncomputable` statement definitions**: {names}. Verify whether any explicit/algorithmic claim is affected.")
            elif kind == "author_scope":
                lines.append(f"- {ref} — **Author scope note**: {cav['note']}")
            elif kind == "stronger_result":
                lines.append(f"- {ref} — **Lean proves more**: {cav['note']}")
            elif kind == "discrepancy":
                label = "Open question" if cav.get("result") == "unsure" else "Open discrepancy"
                lines.append(f"- {ref} — **{label}**: {cav['note']}")
            else:
                confirm = " *(Needs author confirmation)*" if cav.get("needs_author_confirmation") else ""
                lines.append(
                    f"- {ref} — **`{kind}`** ({cav['case']}){confirm}: "
                    f"Paper: {cav['paper']} | Lean: {cav['lean']} | Why: {cav['why']}"
                )

    lines.extend(["", "## Open Shortcomings & Refinement Backlog", ""])
    if not backlog["total_items"]:
        lines.append("No open shortcomings or deferred refinement items.")
    else:
        for group in backlog["priorities"]:
            if not group["items"]:
                continue
            lines.append(f"### P{group['priority']}: {group['title']} ({len(group['items'])})")
            lines.append("")
            for item in group["items"]:
                ref = f"**{item['reference']}** (`{item['claim']}`)"
                details = []
                if group["key"] == "needs_author_confirmation":
                    if item["cases"]:
                        details.append("; ".join(f"`{c['kind']}` on {c['case']}" for c in item["cases"]))
                    if item["dependents"]:
                        details.append("dependents: " + ", ".join(d["reference"] for d in item["dependents"]))
                elif group["key"] == "conditional_claims":
                    details.append("assumes: " + ", ".join(a["reference"] for a in item["assumes"]))
                elif group["key"] == "weaker_or_noncomputable":
                    if item["weaker_conclusions"]:
                        details.append("weaker conclusion: " + "; ".join(w["case"] for w in item["weaker_conclusions"]))
                    if item.get("open_discrepancy"):
                        details.append("open discrepancy: " + item["open_discrepancy"])
                    if item["noncomputable_constants"]:
                        details.append("noncomputable: " + ", ".join(f"`{n}`" for n in item["noncomputable_constants"]))
                    if item["open_subproofs"]:
                        details.append("open subproofs: " + ", ".join(item["open_subproofs"]))
                elif group["key"] == "witnesses_and_defaults":
                    if item["missing_witness"]:
                        plan = item["witness_plan"] or {}
                        plan_str = f" (`{plan.get('mode')}`: {plan.get('action')})" if plan else ""
                        details.append(NO_EXAMPLE + plan_str)
                    if item["unresolved_defaults"]:
                        flags = ", ".join(f"`{d['construct']}` in `{d['constant']}` [{d['status']}]" for d in item["unresolved_defaults"])
                        details.append("unresolved default-value flags: " + flags)
                elif group["key"] == "bridging_and_distillation":
                    if item["deferred_bridging_lemmas"]:
                        details.append("deferred bridging lemmas: " + "; ".join(item["deferred_bridging_lemmas"]))
                    if item["undistilled"]:
                        details.append("Exploratory proof (undistilled)")
                suffix = f" — {'; '.join(details).rstrip('.')}" if details else ""
                lines.append(f"- {ref}{suffix}. *Next:* {item['action']}")
            lines.append("")

    lines.extend(["## Pinned Environment & Statement Digests", ""])
    lines.append(f"- **Lean toolchain:** {', '.join(f'`{t}`' for t in pinned['toolchains']) or 'Not yet audited'}")
    if pinned["mathlib"]:
        m = pinned["mathlib"]
        lines.append(f"- **Mathlib commit:** `{m['rev']}`" + (f" ({m['url']})" if m.get("url") else ""))
    else:
        lines.append("- **Mathlib commit:** Not recorded")
    if pinned["third_party_packages"]:
        tp = ", ".join(f"`{p['name']}` (`{p['rev']}`)" for p in pinned["third_party_packages"])
        lines.append(f"- **Third-party external packages:** {tp}")
    else:
        lines.append("- **Third-party external packages:** None")
    lines.append(f"- **Aggregate axiom profile:** {pinned['aggregate_axiom_profile']}")
    if pinned["aggregate_statement_digest"]:
        lines.append(f"- **Aggregate statement digest (SHA-256):** `{pinned['aggregate_statement_digest']}`")
    if pinned["statements_files_digests"]:
        files_str = ", ".join(f"`{k}` (`{v[:12]}`)" for k, v in pinned["statements_files_digests"].items())
        lines.append(f"- **Pinned `Statements/` files:** {files_str}")

    lines.extend([
        "",
        "| Claim | Tier | Resolution | Declaration | Axiom profile | Witness | Statement SHA-256 |",
        "| :--- | :--- | :--- | :--- | :--- | :--- | :--- |",
    ])
    state_labels = {
        "unconditionally_closed": "Unconditionally closed",
        "conditional": "Conditional",
        "subproofs_checked": "Subproofs checked",
        "open": "Open",
    }
    for rec in records:
        cid = rec["claim"]["id"]
        ref = f"{rec['entry']['reference']} (`{cid}`)"
        decl = ((rec["audit"] or {}).get("declaration")
                or (rec["work"].get("closure") or {}).get("declaration")
                or (rec["work"].get("statement_check") or {}).get("expected")
                or "—")
        ax = rec["rd"].get("axiom_profile") or "—"
        wit = f"`{rec['entry']['hypotheses']['declaration']}`" if rec["entry"].get("hypotheses") else ("—" if rec["tier"] == "conjecture" else "Missing")
        sha = ((rec["audit"] or {}).get("statement") or {}).get("sha256")
        sha_cell = f"`{sha[:12]}`" if sha else "—"
        lines.append(
            f"| {ref} | {rec['tier']} | {state_labels[rec['resolution']]} | `{decl}` | {ax} | {wit} | {sha_cell} |"
            if decl != "—" else
            f"| {ref} | {rec['tier']} | {state_labels[rec['resolution']]} | — | {ax} | {wit} | {sha_cell} |"
        )

    supplied_recs = [rec for rec in records if rec.get("basis") == "supplied"]
    supplied_step_recs = [
        rec for rec in records
        if rec.get("basis") != "supplied" and _has_supplied_steps(rec)
    ]
    if supplied_recs or supplied_step_recs:
        lines.extend([
            "",
            "## Supplied Proofs (Outside Manuscript)",
            "",
            "The following claims are stated in the manuscript without a complete written proof (or include "
            "Lean-supplied intermediate steps); their Lean-checked derivations are supplied outside the manuscript PDF"
            + (" and collected in [`supplement.md`](supplement.md)." if has_supplement else "."),
            "",
        ])
        for rec in supplied_recs:
            cid = rec["claim"]["id"]
            ref = f"**{rec['entry']['reference']}** (`{cid}`)"
            badge = (SUPPLIED_BADGE if rec["resolution"] == "unconditionally_closed"
                     else f"{rec['resolution'].replace('_', ' ').title()} (proof supplied outside manuscript)")
            decl = ((rec.get("audit") or {}).get("declaration")
                    or (rec["work"].get("closure") or {}).get("declaration") or "")
            decl_bit = f" — `{decl}`" if decl else ""
            lines.append(f"- {ref} ({rec['tier']}) — {badge}{decl_bit}")
        for rec in supplied_step_recs:
            cid = rec["claim"]["id"]
            ref = f"**{rec['entry']['reference']}** (`{cid}`)"
            sv = rec["step_verification"]
            badge = sv["badge"] if sv.get("verified") else "Supplied proof steps (awaiting Lean step audit)"
            lines.append(
                f"- {ref} ({rec['tier']}) — {badge} ({sv['supplied_steps']}/{sv['step_count']} step(s) supplied outside manuscript)"
            )

    step_verified_recs = [
        rec for rec in records
        if (rec.get("step_verification") or {}).get("verified")
    ]
    if step_verified_recs:
        lines.extend([
            "",
            "## Step-Level Verification (1:1 Expr Audit)",
            "",
            "| Claim | Badge | Steps (Paper / Supplied) | Main declaration | Step Map SHA-256 |",
            "| :--- | :--- | :---: | :--- | :--- |",
        ])
        for rec in step_verified_recs:
            cid = rec["claim"]["id"]
            ref = f"{rec['entry']['reference']} (`{cid}`)"
            sv = rec["step_verification"]
            counts_cell = f"{sv['step_count']} ({sv['paper_steps']} paper / {sv['supplied_steps']} supplied)"
            main_cell = f"`{sv['main_declaration']}`" if sv.get("main_declaration") else "—"
            sha_cell = f"`{sv['step_map_sha256'][:12]}`" if sv.get("step_map_sha256") else "—"
            lines.append(f"| {ref} | {sv['badge']} | {counts_cell} | {main_cell} | {sha_cell} |")

    metrics_recs = [rec for rec in records if rec.get("proof_metrics") or rec.get("distilled") is not None]
    if metrics_recs:
        lines.extend([
            "",
            "## Proof Size & Distillation Metrics",
            "",
            "| Claim | Checked Lean LoC | Reachable local defs | Reachable local theorems | Distillation |",
            "| :--- | :---: | :---: | :---: | :--- |",
        ])
        for rec in metrics_recs:
            cid = rec["claim"]["id"]
            ref = f"{rec['entry']['reference']} (`{cid}`)"
            m = rec.get("proof_metrics") or {}
            loc_cell = str(m["checked_lean_loc"]) if "checked_lean_loc" in m else "—"
            defs_cell = str(m["reachable_local_defs"]) if "reachable_local_defs" in m else "—"
            thms_cell = str(m["reachable_local_theorems"]) if "reachable_local_theorems" in m else "—"
            dist_cell = ("Distilled" if rec.get("distilled") is True else
                         "Exploratory (undistilled)" if rec.get("undistilled") else "—")
            lines.append(f"| {ref} | {loc_cell} | {defs_cell} | {thms_cell} | {dist_cell} |")

    if dag_grounding and any(dag_grounding.get(k) for k in ("both", "paper_only", "lean_only")):
        lines.extend([
            "",
            "## Kernel-Extracted Dependency Grounding",
            "",
            f"- **Used in both paper & Lean proof:** {dag_grounding.get('both', 0)}",
            f"- **Paper-only dependency (Lean proved independently):** {dag_grounding.get('paper_only', 0)}",
            f"- **Lean-only prerequisite:** {dag_grounding.get('lean_only', 0)}",
        ])
        if dag_grounding.get("paper"):
            lines.append(f"- **Paper dependency (Lean proof not yet audited):** {dag_grounding['paper']}")

    lines.extend([
        "",
        "## Paste-Ready LaTeX Snippet",
        "",
        "```latex",
        latex_snippet.rstrip("\n"),
        "```",
        "",
    ])
    return "\n".join(lines)


def manifest(root, *, ci_receipt=None, commit=None, write=True, propose_edit=False,
             edit_location="", edit_original="", edit_reason="", edit_claim="manuscript"):
    """Deterministically build dist/VERIFICATION.md and a paste-ready LaTeX scope snippet."""
    project = json.loads((root / "project.json").read_text(encoding="utf-8-sig"))
    claims = manuscript_claims(root, project)
    by_id = {c["id"]: c for c in claims}
    if "claim_order" in project:
        order = project["claim_order"]
        if len(order) != len(claims) or set(order) != set(by_id):
            raise ValueError("claim_order must list every manuscript claim exactly once")
        claims = [by_id[label] for label in order]
    ci = github_verification(project, ci_receipt, commit)
    if ci is None and ci_receipt is None:
        receipt = root / "dist/logs/lean-verification.json"
        if receipt.is_file():
            try:
                data = json.loads(receipt.read_bytes())
                ci = github_verification(project, receipt, commit or data.get("commit"))
            except (OSError, ValueError):
                ci = None
    materials = json.loads(local(root, project["reader"]).read_text(encoding="utf-8-sig")) if project.get("reader") else {}
    paper_edges = materials.get("dependencies", [])
    records = _collect_claim_states(root, project, claims, ci=ci)
    _, _, dag_grounding = ground_claim_dependencies(claims, records, paper_edges)
    summary = summarize_records(records)
    backlog = build_refinement_backlog(project, records)
    caveats = _collect_scope_caveats(records)
    pinned = _collect_pinned_metadata(root, project, records, ci)
    supplement_md = render_supplement_markdown(project, records)
    latex_snippet = _render_manifest_latex(project, summary, caveats, backlog, pinned)
    markdown = _render_manifest_markdown(
        project, records, summary, caveats, backlog, pinned, latex_snippet,
        dag_grounding=dag_grounding, has_supplement=supplement_md is not None,
    )
    md_path = root / "dist" / "VERIFICATION.md"
    supp_path = root / "dist" / "supplement.md"
    if write:
        md_path.parent.mkdir(parents=True, exist_ok=True)
        atomic(md_path, markdown.encode("utf-8"))
        if supplement_md is not None:
            atomic(supp_path, supplement_md.encode("utf-8"))
        elif supp_path.exists():
            supp_path.unlink()
    edit_result = None
    if propose_edit:
        reason = edit_reason or (
            "Synchronize manuscript verification statement with Proof Atlas scope caveats, "
            "headline/supporting counts, deferred checks, and pinned Lean digests."
        )
        key, entry, changed = manuscript_edits.propose(
            root,
            MANIFEST_EDIT_KEY,
            claim=edit_claim,
            edition=project.get("edition", ""),
            location=edit_location or "Abstract / Introduction (Formal Verification and Scope)",
            original=edit_original,
            replacement=latex_snippet.strip(),
            reason=reason,
        )
        edit_result = dict(key=key, entry=entry, updated=changed)
    return dict(
        markdown_path=str(md_path),
        markdown=markdown,
        latex=latex_snippet,
        supplement_path=str(supp_path) if supplement_md is not None else None,
        supplement=supplement_md,
        dag_grounding=dag_grounding,
        summary=summary,
        caveats=caveats,
        backlog=backlog,
        pinned=pinned,
        atlas_url=pinned["atlas_url"],
        manuscript_edit=edit_result,
    )


def review_work(root, labels=(), *, require_ci=False, ci_receipt=None):
    """List actionable review findings, multi-resolution counts, and prioritized backlog."""
    import subprocess
    project = reviews.read(root/"project.json", {})
    claims = manuscript_claims(root, project)
    by_id = {c["id"]: c for c in claims}
    if "claim_order" in project:
        order = project["claim_order"]
        if len(order) == len(claims) and set(order) == set(by_id):
            claims = [by_id[label] for label in order]
    if set(labels) - by_id.keys():
        raise ValueError("Unknown review-work claim")
    selected = list(dict.fromkeys(labels or [c["id"] for c in claims]))
    selected_set = set(selected)
    report = {"scope": project.get("proof_work"), "profile": proof_work_profile(project),
              "lean_ci_level": lean_ci_level(project),
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
    elif ci_receipt:
        path = Path(ci_receipt)
        if path.is_file():
            data = json.loads(path.read_bytes())
            ci = github_verification(project, path, data.get("commit"))
    all_records = _collect_claim_states(root, project, claims, ci=ci)
    by_rec = {rec["claim"]["id"]: rec for rec in all_records}
    selected_records = [by_rec[cid] for cid in selected]
    for rec in selected_records:
        cid = rec["claim"]["id"]
        work = rec["work"]
        packet = rec["rd"]
        if rec["tier"] != "conjecture":
            report["witness_search"][cid] = rec["witness_plan"]
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
            need_paranoid = lean_ci_level(project) == "paranoid"
            claim_kernels = list(evidence.get("kernels_checked") or (ci or {}).get("kernels_checked") or [])
            paranoid_ok = (not need_paranoid or (
                (ci or {}).get("ci_level") == "paranoid"
                and any(k != "lean-kernel" for k in claim_kernels)
            ))
            if (not packet["checked"] or evidence.get("audit_sha256")!=digest
                    or not paranoid_ok
                    or (packet["view"]["bindings"]["statement"] and
                        evidence.get("statement_sha256")!=packet["view"]["bindings"]["statement"])):
                report["ci_pending"].append(cid)
    book, edits = manuscript_edits.inventory(root)
    for key,item in edits.items():
        in_scope = item["claim"] in selected_set or (not labels and item["claim"] not in by_id)
        if in_scope and key not in book.get("cleared",{}) and item.get("status")=="Draft requested":
            report["agent_tasks"].append(dict(claim=item["claim"], edit=key, next="Prepare the requested manuscript draft."))
    report["summary"] = summarize_records(selected_records)
    report["refinement_backlog"] = build_refinement_backlog(project, selected_records)
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
    materials = json.loads(local(root, p["reader"]).read_text(encoding="utf-8-sig")) if p.get("reader") else {}
    notes = materials.get("claims", {})
    tex_sources = load_bound_tex_sources(root, p)

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
                witness_modules=list(asm.get("witness_modules") or []),
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
                for wmod in spec.get("witness_modules") or ():
                    contract_imports.append(wmod)
                if spec.get("witness"):
                    resolved_wmod = False
                    if "." in spec["witness"]:
                        mod_guess = spec["witness"].rsplit(".", 1)[0]
                        if (pkg_root / ("/".join(mod_guess.split(".")) + ".lean")).is_file():
                            contract_imports.append(mod_guess)
                            resolved_wmod = True
                    if not resolved_wmod and not spec.get("witness_modules") and (pkg_root / "Examples").is_dir():
                        for ex_file in sorted((pkg_root / "Examples").rglob("*.lean")):
                            contract_imports.append(ex_file.relative_to(pkg_root).as_posix()[:-5].replace("/", "."))
            contract_text = "\n".join(f"import {m}" for m in sorted(set(contract_imports))) + "\n"
            atomic(pkg_root / contract_rel, contract_text.encode("utf-8"))
            ev_dir = root / "evidence"
            ev_dir.mkdir(exist_ok=True)
            for item in claim_reports:
                cid = item["claim"]
                spec = specs[cid]
                resolved_sm = resolve_claim_step_map(
                    root, cid, work.get(cid, {}), notes.get(cid, {}), tex_sources,
                    default_main=spec["declaration"],
                )
                step_map_arg = None
                if resolved_sm is not None:
                    other_decls = collect_other_claim_declarations(p, cid)
                    merged_forbidden = list(dict.fromkeys([*resolved_sm["forbidden_mains"], *other_decls]))
                    step_map_arg = dict(
                        main_declaration=resolved_sm["main_declaration"] or spec["declaration"],
                        main_deps=resolved_sm["main_deps"],
                        forbidden_mains=merged_forbidden,
                        steps=[
                            {k: v for k, v in s.items() if k in ("id", "lemma", "step_deps", "origin")}
                            for s in resolved_sm["steps"]
                        ],
                    )
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
                    step_map=step_map_arg,
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
                log_rel = f"evidence/assembly-{ident_by_cid[cid]}.log"
                if not w.get("run_log") or w.get("run_log") == log_rel:
                    atomic(root / log_rel, (audit_data.get("lean_output", "") + "\n").encode("utf-8"))
                    w["run_log"] = log_rel
                has_open_subproofs = any(part.get("status") != "checked" for part in w.get("subproofs", []))
                if item["unconditional"]:
                    w.pop("assumes", None)
                    if not has_open_subproofs:
                        w["status"] = "closed"
                    elif w.get("status") == "conditional":
                        w["status"] = "attempted"
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


def _parse_local_imports_from_source(pkg_root, rel_path):
    """Extract local Lean module imports from a package-relative source file without invoking Lake."""
    import audit_lean
    text = audit_lean.strip_lean_comments_and_strings((pkg_root / rel_path).read_text(encoding="utf-8-sig"))
    mods = []
    for line in text.splitlines():
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\b", line)
        if m:
            mod = m.group(1)
            if (pkg_root / ("/".join(mod.split(".")) + ".lean")).is_file():
                mods.append(mod)
    return mods


def _lakefile_has_libs(pkg_root, names):
    """Return True if lakefile.toml declares every named [[lean_lib]]."""
    toml_path = pkg_root / "lakefile.toml"
    if not toml_path.is_file():
        return False
    import tomllib
    try:
        config = tomllib.loads(toml_path.read_text(encoding="utf-8-sig"))
    except (OSError, ValueError):
        return False
    declared = {lib.get("name") for lib in config.get("lean_lib", []) if isinstance(lib, dict)}
    return set(names) <= declared


def generate_challenge_harness(root, *, package=None, write=True, check_only=False):
    """Mechanically generate hash-locked Challenge.lean and Solution.lean for closed claims.

    Challenge.lean imports ONLY isolated Statements/ modules (verified free of `sorry` and
    escape hatches) and declares each closed claim target as `theorem <name> : _root_.<expected> := by sorry`.
    Solution.lean imports Statements/ plus Assembly/Proofs and proves the identical theorem
    names and types via `_root_.<declaration>`.
    """
    import audit_lean

    p = json.loads((root / "project.json").read_text(encoding="utf-8-sig"))
    claims = manuscript_claims(root, p)
    by_id = {c["id"]: c for c in claims}
    order = p.get("claim_order") or [c["id"] for c in claims]
    work = p.get("work", {})

    pkg_claims = {}
    for cid in order:
        if cid not in by_id:
            continue
        w = work.get(cid, {})
        if w.get("status") != "closed":
            continue
        closure = w.get("closure") or {}
        pkg = closure.get("package")
        if not pkg:
            raise ValueError(f"{cid}: closed claim is missing closure.package")
        if package and pkg != package:
            continue
        if not closure.get("audit") or not closure.get("expected") or not closure.get("declaration"):
            raise ValueError(f"{cid}: closed claim is missing audit, expected, or declaration")
        prior = json.loads(local(root, closure["audit"]).read_bytes())
        if prior.get("assumes") or w.get("assumes"):
            raise ValueError(f"{cid}: closed claim cannot carry unresolved conditional assumptions")
        pkg_claims.setdefault(pkg, []).append((cid, w, closure, prior))

    if not pkg_claims:
        raise ValueError("No closed claims found to generate Challenge.lean / Solution.lean")

    report = {"packages": {}}
    for pkg, items in sorted(pkg_claims.items()):
        pkg_root = local(root, pkg)
        stmt_paths = []
        for _, w, _, prior in items:
            for sp in prior.get("statements") or (w.get("assembly") or {}).get("statements") or []:
                if sp not in stmt_paths:
                    stmt_paths.append(sp)
        if not stmt_paths:
            if (pkg_root / "Statements").is_dir():
                stmt_paths = ["Statements"]
            elif (pkg_root / "Statements.lean").is_file():
                stmt_paths = ["Statements.lean"]
            else:
                raise ValueError(
                    f"{pkg}: Challenge.lean generation requires isolated Statements/ modules "
                    "(pass --statements Statements when auditing claims)"
                )

        stmt_files = sorted(audit_lean.statement_paths(pkg_root, stmt_paths))
        if not stmt_files:
            raise ValueError(f"{pkg}: no .lean files found under statement paths: {', '.join(stmt_paths)}")
        hygiene_files = list(stmt_files)
        hygiene_stmt_set = set(stmt_files)
        if (pkg_root / "Prelude.lean").is_file():
            hygiene_files.append("Prelude.lean")
            hygiene_stmt_set.add("Prelude.lean")
        audit_lean.scan_lean_hygiene(pkg_root, hygiene_files, hygiene_stmt_set)
        audit_lean.scan_no_sorry(pkg_root, stmt_files)

        allowed_stmt_modules = {f[:-5].replace("/", ".") for f in stmt_files}
        stmt_digests = {f: hashlib.sha256((pkg_root / f).read_bytes()).hexdigest() for f in stmt_files}
        statements_sha256 = hashlib.sha256(
            "".join(f"{f} {h}\n" for f, h in sorted(stmt_digests.items())).encode("utf-8")
        ).hexdigest()

        used_names = set()
        challenge_imports = set()
        solution_imports = set()
        challenge_decls = []
        solution_decls = []
        targets_meta = []

        for cid, w, closure, prior in items:
            expected = closure["expected"]
            declaration = closure["declaration"]
            asm_name = (w.get("assembly") or {}).get("name")
            name = asm_name if (asm_name and asm_name not in used_names) else _lean_ident(cid, used_names)
            used_names.add(name)

            claim_stmt_mods = []
            for mod in (w.get("assembly") or {}).get("statement_modules") or []:
                if mod not in claim_stmt_mods:
                    claim_stmt_mods.append(mod)
            if not claim_stmt_mods:
                for const in (prior.get("statement") or {}).get("constants") or []:
                    if const.get("name") == expected and const.get("file", "").endswith(".lean"):
                        mod = const["file"][:-5].replace("/", ".")
                        if mod not in claim_stmt_mods:
                            claim_stmt_mods.append(mod)
            if not claim_stmt_mods:
                if "Statements" in allowed_stmt_modules:
                    claim_stmt_mods = ["Statements"]
                else:
                    claim_stmt_mods = sorted(allowed_stmt_modules)
            for mod in claim_stmt_mods:
                if mod not in allowed_stmt_modules:
                    raise ValueError(
                        f"{cid}: statement module {mod} is outside isolated Statements/ ({', '.join(stmt_paths)})"
                    )
                challenge_imports.add(mod)
                solution_imports.add(mod)

            proof_mods = []
            if declaration.startswith("Assembly.") and (pkg_root / "Assembly.lean").is_file():
                proof_mods.append("Assembly")
            else:
                for t in prior.get("targets") or []:
                    if t not in proof_mods and (pkg_root / ("/".join(t.split(".")) + ".lean")).is_file():
                        proof_mods.append(t)
                asm_mod = (w.get("assembly") or {}).get("module")
                if not proof_mods and asm_mod and (pkg_root / ("/".join(asm_mod.split(".")) + ".lean")).is_file():
                    proof_mods.append(asm_mod)
                if not proof_mods and prior.get("contract") and (pkg_root / prior["contract"]).is_file():
                    for mod in _parse_local_imports_from_source(pkg_root, prior["contract"]):
                        if mod not in allowed_stmt_modules and mod not in proof_mods:
                            proof_mods.append(mod)
            if not proof_mods:
                raise ValueError(f"{cid}: could not determine proof module(s) for Solution.lean ({declaration})")
            solution_imports.update(proof_mods)

            stmt_sha = (prior.get("statement") or {}).get("sha256") or ""
            doc_sha = f" (statement SHA-256: `{stmt_sha}`)" if stmt_sha else ""
            doc = f"/-- Claim `{cid}`: `{expected}`{doc_sha} -/"
            challenge_decls.append(f"{doc}\ntheorem {name} : _root_.{expected} := by sorry")
            solution_decls.append(f"{doc}\ntheorem {name} : _root_.{expected} :=\n  _root_.{declaration}")
            targets_meta.append(dict(
                claim=cid,
                name=name,
                theorem=f"ProofAtlasChallenge.{name}",
                expected=expected,
                declaration=declaration,
                statement_sha256=stmt_sha or None,
                proof_modules=sorted(set(proof_mods)),
            ))

        header = (
            "/- Generated by Proof Atlas (`atlas.py challenge`). Do not edit by hand.\n"
            f"   Statements digest (SHA-256): {statements_sha256}\n"
            f"   Targets: {len(targets_meta)} -/\n"
        )
        challenge_text = (
            header
            + "\n".join(f"import {m}" for m in sorted(challenge_imports))
            + "\n\nnamespace ProofAtlasChallenge\n\n"
            + "\n\n".join(challenge_decls)
            + "\n\nend ProofAtlasChallenge\n"
        )
        solution_text = (
            header
            + "\n".join(f"import {m}" for m in sorted(solution_imports))
            + "\n\nnamespace ProofAtlasChallenge\n\n"
            + "\n\n".join(solution_decls)
            + "\n\nend ProofAtlasChallenge\n"
        )
        challenge_bytes = challenge_text.encode("utf-8")
        solution_bytes = solution_text.encode("utf-8")
        challenge_path = pkg_root / "Challenge.lean"
        solution_path = pkg_root / "Solution.lean"

        if check_only:
            for label_name, path_obj, expected_bytes in (
                ("Challenge.lean", challenge_path, challenge_bytes),
                ("Solution.lean", solution_path, solution_bytes),
            ):
                if not path_obj.is_file():
                    raise ValueError(f"{pkg}: missing {label_name}; run `atlas.py challenge` to generate it")
                if path_obj.read_bytes() != expected_bytes:
                    raise ValueError(
                        f"{pkg}: committed {label_name} differs from the hash-locked generated harness; "
                        "regenerate with `atlas.py challenge`"
                    )
        elif write:
            atomic(challenge_path, challenge_bytes)
            atomic(solution_path, solution_bytes)

        report["packages"][pkg] = dict(
            challenge_file=(Path(pkg) / "Challenge.lean").as_posix(),
            solution_file=(Path(pkg) / "Solution.lean").as_posix(),
            challenge_sha256=hashlib.sha256(challenge_bytes).hexdigest(),
            solution_sha256=hashlib.sha256(solution_bytes).hexdigest(),
            statements_sha256=statements_sha256,
            statements_paths=stmt_paths,
            statements_files=stmt_digests,
            challenge_imports=sorted(challenge_imports),
            solution_imports=sorted(solution_imports),
            namespace="ProofAtlasChallenge",
            lakefile_configured=_lakefile_has_libs(pkg_root, ("Challenge", "Solution")),
            targets=targets_meta,
            _challenge_bytes=challenge_bytes,
            _solution_bytes=solution_bytes,
        )

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
    profile = proof_work_profile(p)
    tex_sources = load_bound_tex_sources(root, p)
    prereqs_by_cid = {c["id"]: set() for c in claims}
    for edge in edges:
        prereqs_by_cid[edge["claim"]].add(edge["prerequisite"])
    built_records = []
    for c in claims:
        cid = c["id"]
        w = work.get(cid, {})
        m = notes.get(cid, {})
        tier = claim_tier(c, m, w)
        basis = claim_basis(cid, m, w)
        status = w.get("status", "open")
        if status not in {"open", "drafted", "blocked", "attempted", "conditional", "closed"}:
            raise ValueError(f"{cid}: unsupported checkpoint status {status}")
        entry = {**c, **m, **w}
        entry["tier"] = tier
        entry["headline"] = tier == "headline"
        if basis is not None:
            entry["basis"] = basis
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
        metrics = extract_proof_metrics(active_audit)
        if metrics:
            entry["proof_metrics"] = metrics
        undistilled = _is_undistilled(cid, w, profile, checked, is_conditional)
        distilled = w.get("distilled") if isinstance(w.get("distilled"), bool) else None
        if distilled is not None:
            entry["distilled"] = distilled
        if undistilled:
            entry["undistilled"] = True
        default_main = ((w.get("assembly") or {}).get("declaration")
                        or (w.get("closure") or {}).get("declaration")
                        or (active_audit or {}).get("declaration"))
        step_map = resolve_claim_step_map(root, cid, w, m, tex_sources, default_main=default_main)
        step_verif = evaluate_step_verification(
            cid, step_map, active_audit, proof_checked=(checked or is_conditional), changed=bool(changed),
        )
        if step_verif is not None:
            entry["step_verification"] = step_verif
        has_supp_entry = basis == "supplied" or bool(step_verif and step_verif.get("supplied_steps", 0) > 0)
        supp_url = f"supplement.md#{supplement_anchor(cid)}" if has_supp_entry else ""
        rd = reviews.packet(root,p,c,w,active_audit,comparisons.get(cid),reviews.history(root,cid),
                            checked,statement_checked,
                            conditional=is_conditional,
                            assumes=[item["reference"] for item in assumed_items] if is_conditional else (),
                            basis=basis, proof_metrics=metrics, distilled=distilled,
                            undistilled=undistilled, supplement_url=supp_url,
                            step_verification=step_verif)
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
        res = claim_resolution(checked, is_conditional, rd["disputed"], has_parts)
        entry["resolution"] = res
        unres_defaults = unresolved_defaults(rd)
        if unres_defaults:
            entry["unresolved_defaults"] = unres_defaults
        bridging = _deferred_bridging_lemmas(cid, w)
        if bridging:
            entry["deferred_bridging_lemmas"] = bridging
        checked_label = SUPPLIED_BADGE if basis == "supplied" else "Lean checked"
        cond_label = f"Conditional (assumes {', '.join(item['reference'] for item in assumed_items)})"
        if basis == "supplied":
            cond_label += " · proof supplied outside manuscript"
        label = ("Open conjecture" if c["kind"] == "conjecture" and status == "open" else
                 checked_label if checked else "Awaiting Lean recheck" if changed else
                 cond_label if is_conditional else
                 "Subproofs checked" if has_parts else
                 "Statement drafted (proof in progress)" if statement_checked else "No completed Lean check")
        verification = {"label": label}
        if basis is not None:
            verification["basis"] = basis
        if basis == "supplied":
            verification["supplied"] = True
            verification["supplement_url"] = supp_url
        if step_verif and step_verif.get("verified"):
            verification["step_verified"] = True
            verification["step_badge"] = step_verif["badge"]
            verification["step_mode"] = step_verif["mode"]
            verification["step_count"] = step_verif["step_count"]
            verification["supplied_step_count"] = step_verif["supplied_steps"]
            if step_verif["supplied_steps"] > 0 and supp_url:
                verification.setdefault("supplement_url", supp_url)
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
            ci_ok, paranoid_ok, rec_kernels, rec_ci_level = _ci_claim_status(audit, receipt, ci, cid)
            if ci_ok:
                remote_label = "Multi-kernel / Comparator" if paranoid_ok else "Machine verified on GitHub"
                verification.update(remote=remote_label,
                                    url=f'{p["hosting"]["repository"]}/actions/runs/{ci["run_id"]}/attempts/{ci["attempt"]}',
                                    commit=ci["commit"], evidence="logs/lean-verification.json",
                                    ci_level=rec_ci_level, kernels_checked=rec_kernels)
                if paranoid_ok:
                    verification["paranoid"] = True
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
        built_records.append(dict(
            claim=c, entry=entry, work=w, note=m, rd=rd, audit=active_audit,
            tier=tier, basis=basis, proof_metrics=metrics, distilled=distilled,
            supplement_url=supp_url, step_verification=step_verif,
            resolution=res, checked=checked, is_conditional=is_conditional,
            has_parts=has_parts, changed=bool(changed), assumed_items=assumed_items,
            unresolved_defaults=unres_defaults, deferred_bridging_lemmas=bridging,
            undistilled=undistilled,
            witness_plan=witness_plan(p, w, rd["witness"]) if tier != "conjecture" else None,
            machine_verified="evidence" in verification,
            label=label,
        ))

    # Cross-reference kernel-extracted Lean constant closures against reader.json dependencies.
    grounded_edges, per_claim_deps, dag_grounding = ground_claim_dependencies(claims, built_records, edges)
    for edge in grounded_edges:
        prereqs_by_cid[edge["claim"]].add(edge["prerequisite"])
    for rec in built_records:
        cid = rec["claim"]["id"]
        if cid in per_claim_deps:
            rec["entry"]["lean_dependencies"] = per_claim_deps[cid]

    # Generate dist/supplement.md whenever any claim carries basis='supplied'.
    supplement_md = render_supplement_markdown(p, built_records)
    supp_path = output / "supplement.md"
    if supplement_md is not None:
        atomic(supp_path, supplement_md.encode("utf-8"))
    elif supp_path.exists():
        supp_path.unlink()

    # Propagate Needs author confirmation from unattended quick-mode readings to transitive dependents.
    direct_confirm = {rd["id"] for rd in review_entries if rd.get("needs_author_confirmation")}
    for rec in built_records:
        c = rec["claim"]
        entry = rec["entry"]
        rd = rec["rd"]
        checked = rec["checked"]
        is_conditional = rec["is_conditional"]
        label = rec["label"]
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
        if rec["basis"] == "supplied" and rec["supplement_url"]:
            badge += f' · <a href="{esc(rec["supplement_url"])}">Supplied proof</a>'
        if verification.get("step_verified") and verification.get("step_badge"):
            badge += f' · <a class="verified-badge" href="{url}?view=lamport">&#10003; {esc(verification["step_badge"])}</a>'
            if verification.get("supplied_step_count") and rec["supplement_url"] and rec["basis"] != "supplied":
                badge += f' · <a href="{esc(rec["supplement_url"])}">Supplied steps</a>'
        if (checked or is_conditional) and not entry.get("hypotheses"):
            badge += f' · {NO_EXAMPLE}'
        if rec["unresolved_defaults"]:
            badge += f' · <a href="{reviews.review_url(cid)}">Unresolved default-value flag ({len(rec["unresolved_defaults"])})</a>'
        if rec["undistilled"]:
            badge += ' · Exploratory proof (undistilled)'
        elif rec["distilled"] is True and (checked or is_conditional):
            badge += ' · Distilled'
        if rec["proof_metrics"] and "checked_lean_loc" in rec["proof_metrics"]:
            badge += f' · {rec["proof_metrics"]["checked_lean_loc"]} LoC'
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
            if verification.get("paranoid") and verification.get("kernels_checked"):
                badge += f' · Kernels: {esc(", ".join(verification["kernels_checked"]))}'
            badge += f' · <a href="{esc(verification["evidence"])}">Verification record</a>'
            if "artifact" in verification:
                badge += (f' · <a href="{esc(verification["artifact"])}" data-artifact-record="{esc(verification["evidence"])}">'
                          'GitHub artifact (sign-in required)</a>')
        elif "remote" in verification:
            badge += f' · <a href="{esc(verification["url"])}">{esc(verification["remote"])}</a>'
        rows.append(f'<li data-claim="{esc(cid)}" data-tier="{esc(rec["tier"])}" data-resolution="{esc(rec["resolution"])}"><a href="{url}">{esc(entry["reference"])} · {esc(c["title"])}</a> · {esc(entry["status"])}{badge}{target}<span class="claim-activity"></span></li>')
    if ci:
        (output / "logs").mkdir(exist_ok=True)
        atomic(output / "logs/lean-verification.json", Path(ci_receipt).read_bytes())
    summary = summarize_records(built_records)
    backlog = build_refinement_backlog(p, built_records)
    caveats = _collect_scope_caveats(built_records)
    pinned = _collect_pinned_metadata(root, p, built_records, ci)
    latex_snippet = _render_manifest_latex(p, summary, caveats, backlog, pinned)
    verification_md = _render_manifest_markdown(
        p, built_records, summary, caveats, backlog, pinned, latex_snippet,
        dag_grounding=dag_grounding, has_supplement=supplement_md is not None,
    )
    atomic(output / "VERIFICATION.md", verification_md.encode("utf-8"))
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
    summary_html = render_summary_table(summary)
    backlog_html = render_backlog_section(backlog)
    supp_link = ' · <a href="supplement.md">Supplied proofs supplement</a>' if supplement_md is not None else ""
    dashboard = (
        heading
        + f'<section id="claim-inventory" data-feed="{esc(feed)}"><h2>Claim inventory</h2>'
        + f'<p><strong>Authorized proof work</strong><br>{esc(scope)}</p>'
        + f'<p><a href="guide.html">How to use this atlas</a> · <a href="review.html">Review queue</a> · <a href="VERIFICATION.md">Verification manifest</a>{supp_link}</p>'
        + f'<p>{closed_results} of {total_results} stated results closed{pending}</p>'
        + summary_html
        + backlog_html
        + '<ol>' + "".join(rows) + '</ol></section>' + active
    )
    payload = dict(title=p["title"], focus=focus, claims=entries, dependencies=grounded_edges,
                   dag_grounding=dag_grounding,
                   macros=materials.get("macros", {}), summary=summary, backlog=backlog,
                   **({"supplement": "supplement.md"} if supplement_md is not None else {}))
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
        if v.get("evidence") and v.get("supplied"):
            extras.append(f'<a class="status" href="{esc(v.get("supplement_url", "supplement.md"))}">Proof supplied outside manuscript</a>')
        if v.get("step_verified") and v.get("step_badge"):
            extras.append(f'<a class="verified-badge" href="{link}?view=lamport">✓ {esc(v["step_badge"])}</a>')
        if v.get("needs_author_confirmation"):
            extras.append(f'<a class="status" href="{esc(v["review_url"])}">Needs author confirmation</a>')
        elif v.get("needs_author_confirmation_via"):
            extras.append(f'<a class="status" href="{esc(v["review_url"])}">Needs author confirmation</a>')
        if "approval" in v:
            extras.append(f'<a class="status approval approved" href="{esc(v["review_url"])}">{esc(v["approval"])}</a>')
        if extras:
            mark = f'<span class="marks">{mark}{"".join(extras)}</span>'
        tier_label = "Headline" if entry["tier"] == "headline" else ("Conjecture" if entry["tier"] == "conjecture" else "Supporting")
        contents.append(f'<li data-tier="{esc(entry["tier"])}" data-resolution="{esc(entry["resolution"])}"><a class="toc-claim" href="{link}"><small>{esc(entry["reference"])} · {tier_label}</small>'
                        f'<strong>{esc(entry["title"])}</strong></a>{mark}</li>')
    explorer = (template.replace("__MAST__", mast).replace("__TITLE__", esc(p["title"]))
                .replace("__SHORT_TITLE__", esc(short_title)).replace("__BYLINE__", byline)
                .replace("__FEATURE__", feature)
                .replace("__SUMMARY__", render_summary_table(summary, compact=True))
                .replace("__COUNT__", str(len(entries)))
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
    parser.add_argument("operation", choices=["build", "assemble", "challenge", "manifest", "approve", "review", "review-inputs","compare","review-work"])
    parser.add_argument("project", type=Path)
    parser.add_argument("claims", nargs="*", help="approve: claim labels (default: every closed claim awaiting approval)")
    parser.add_argument("--by", help="approve: the author approving the statements. Only the author runs approve")
    parser.add_argument("--package", help="assemble/challenge: limit generation to one project-relative Lean package")
    parser.add_argument("--audit", action="store_true", help="assemble: audit each assembled claim and update project.json")
    parser.add_argument("--ci-receipt", type=Path, help="Evidence downloaded from the trusted Lean workflow")
    parser.add_argument("--commit", help="Git revision being rendered")
    parser.add_argument("--artifact-id", type=int, help="ID of the GitHub artifact containing the supplied CI receipt")
    parser.add_argument("--no-open", action="store_true")
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--side",choices=["paper","lean"],help="Limit the independent reader to one source")
    parser.add_argument("--readings",type=Path,help="Agent comparison record for one claim")
    parser.add_argument("--check",action="store_true",help="review-work/challenge: exit nonzero for pending work or mismatched Challenge/Solution files")
    parser.add_argument("--require-ci",action="store_true",help="review-work: verify receipt coverage for the current checkout commit")
    parser.add_argument("--format",choices=["text","markdown","latex","json"],default="text",help="manifest: output format printed to stdout")
    parser.add_argument("--propose-edit",action="store_true",help="manifest: propose a synchronized manuscript-edits.json entry with the LaTeX scope snippet")
    parser.add_argument("--edit-location",default="",help="manifest --propose-edit: manuscript section/location for the proposed scope edit")
    parser.add_argument("--edit-original",default="",help="manifest --propose-edit: quoted manuscript text being clarified or replaced")
    parser.add_argument("--edit-reason",default="",help="manifest --propose-edit: rationale for the manuscript scope edit")
    parser.add_argument("--edit-claim",default="manuscript",help="manifest --propose-edit: claim label or 'manuscript' for paper-wide scope")
    args = parser.parse_args()
    try:
        if args.operation == "assemble":
            report = assemble(args.project.resolve(), package=args.package, run_audit=args.audit)
            print(json.dumps(report, ensure_ascii=False, indent=2))
        elif args.operation == "challenge":
            report = generate_challenge_harness(
                args.project.resolve(), package=args.package,
                write=not args.check, check_only=args.check,
            )
            cleaned = {
                "packages": {
                    pkg: {k: v for k, v in info.items() if not k.startswith("_")}
                    for pkg, info in report["packages"].items()
                }
            }
            print(json.dumps(cleaned, ensure_ascii=False, indent=2))
        elif args.operation == "manifest":
            result = manifest(
                args.project.resolve(),
                ci_receipt=args.ci_receipt,
                commit=args.commit,
                propose_edit=args.propose_edit,
                edit_location=args.edit_location,
                edit_original=args.edit_original,
                edit_reason=args.edit_reason,
                edit_claim=args.edit_claim,
            )
            if args.format == "json":
                print(json.dumps(result, ensure_ascii=False, indent=2))
            elif args.format == "markdown":
                print(result["markdown"], end="")
            elif args.format == "latex":
                print(result["latex"], end="")
            else:
                print(f"Wrote {result['markdown_path']}")
                if result.get("manuscript_edit"):
                    status = "updated" if result["manuscript_edit"]["updated"] else "unchanged"
                    print(f"Manuscript edit '{result['manuscript_edit']['key']}': {status}")
                print()
                print(result["latex"], end="")
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
