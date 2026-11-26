"""Project-local correspondence evidence and optional human decisions."""
import hashlib
import json
import os
import tempfile
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path

BADGE = "Author reviewed the theorem statement proved in Lean"
ADVICE = {"match": "Recommend approval", "difference": "Report a difference", "unsure": "Hold approval for clarification"}
# How each compared case relates to the paper. Every kind except "agrees" counts as a difference.
KINDS = ("agrees", "added hypothesis", "restriction", "chosen reading", "other form", "stronger", "weaker conclusion")
CONFIRMATION_KINDS = ("chosen reading", "added hypothesis", "restriction")


def differences(analysis):
    """The non-agreeing cases, or None when some case predates classification."""
    cases = (analysis or {}).get("cases", [])
    if not all("kind" in row for row in cases):
        return None
    return [row for row in cases if row["kind"] != "agrees"]


def validate_analysis(analysis, result, require_kinds=False):
    def present(obj, fields):
        return isinstance(obj, dict) and all(isinstance(obj.get(k), str) and obj[k].strip() for k in fields)

    if not present(analysis, ("summary", "scope", "advice")):
        raise ValueError("Supply a comparison summary, its scope and claim-specific author advice")
    cases = analysis.get("cases")
    if not isinstance(cases, list) or not cases or not all(present(row, ("case", "paper", "lean", "why")) for row in cases):
        raise ValueError("Explain at least one case with its paper claim, Lean claim and mathematical justification")
    if any(row.get("kind", KINDS[0]) not in KINDS or require_kinds and "kind" not in row for row in cases):
        raise ValueError("Give each case a kind: " + ", ".join(KINDS))
    for row in cases:
        if "needs_author_confirmation" in row:
            if type(row["needs_author_confirmation"]) is not bool:
                raise ValueError("Case needs_author_confirmation must be a boolean")
            if row["needs_author_confirmation"] and row.get("kind") not in CONFIRMATION_KINDS:
                raise ValueError(
                    "needs_author_confirmation may only be set on chosen reading, added hypothesis, or restriction cases"
                )
    if result == "match" and any(row.get("kind") == "weaker conclusion" for row in cases):
        raise ValueError("A weaker conclusion cannot be recorded as a match; use difference or unsure")
    if (result != "match" or "suggested_feedback" in analysis) and not present(analysis, ("suggested_feedback",)):
        raise ValueError("Supply suggested feedback the author can use to describe the difference or question")


def digest(value):
    data = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def read(path, default):
    return json.loads(path.read_bytes()) if path.exists() else default


def review_url(cid):
    return "review/" + digest(cid) + ".html"


def bindings(project, claim, audit):
    paper = {k: project.get(k) for k in ("edition", "publication", "tex", "pdf")}
    paper.update({k: claim[k] for k in ("id", "file", "line", "excerpt")})
    statement = (audit or {}).get("statement", {})
    inputs = (audit or {}).get("checked_inputs", {})
    return dict(paper=digest(paper), statement=statement.get("sha256"),
                expected=(audit or {}).get("expected"), toolchain=(audit or {}).get("toolchain"),
                manifest=inputs.get("lake-manifest.json"))


def history(root, cid):
    book = read(root / "reviews.json", {"version": 1, "claims": {}})
    if book.get("version") != 1:
        raise ValueError("Unknown reviews.json version")
    return book["claims"].get(cid, [])


def packet(root, project, claim, work, audit, comparison, events, checked, statement_checked=False,
           *, conditional=False, assumes=(), basis=None, proof_metrics=None,
           distilled=None, undistilled=False, supplement_url="", step_verification=None):
    from atlas import statement_defaults
    from audit_lean import axiom_profile as format_axiom_profile
    has_audit = bool(checked or conditional or statement_checked)
    defaults = statement_defaults(audit) if has_audit else []
    axiom_prof = ""
    if audit and has_audit and "axioms" in audit:
        axiom_prof = audit.get("axiom_profile") or format_axiom_profile(audit["axioms"])
    ext_pkgs = list((audit or {}).get("external_packages") or []) if has_audit else []
    noncomp = sorted(c["name"] for c in (audit or {}).get("statement", {}).get("constants", [])
                     if c.get("noncomputable")) if has_audit else []
    keys = bindings(project, claim, audit)
    has_statement = bool(has_audit and keys["statement"])
    current = comparison and comparison.get("bindings") == keys and has_statement
    fields = ("paper_reading", "lean_reading", "paper_refs", "lean_refs")
    if current:
        if comparison.get("result") not in ("match", "difference", "unsure") or any(
                not isinstance(comparison.get(k), str) or not comparison[k].strip() for k in fields):
            raise ValueError(f"{claim['id']}: incomplete independent comparison")
        if comparison["result"] != "match" and not all(comparison.get(k) for k in ("issue", "actor", "next")):
            raise ValueError(f"{claim['id']}: give the difference, next actor and resolution")
        if "needs_author_confirmation" in comparison and type(comparison["needs_author_confirmation"]) is not bool:
            raise ValueError(f"{claim['id']}: needs_author_confirmation must be a boolean")
    comp = comparison if current else {}
    view = dict(bindings=keys, excerpt=claim["excerpt"], edition=project["edition"],
                **{k:comp.get(k, "") for k in fields})
    if "analysis" in comp:
        validate_analysis(comp["analysis"], comp["result"])
        view.update(analysis=comp["analysis"], result=comp["result"])
    if comp.get("needs_author_confirmation"):
        view["needs_author_confirmation"] = True
    stronger = comp.get("stronger_result", "")
    if "stronger_result" in comp and (comp["result"] != "match" or not isinstance(stronger,str) or not stronger.strip()):
        raise ValueError("Use a stronger-result note only for a match and describe the extra conclusion")
    version = digest(view)
    last = events[-1] if events else {}
    resolved = comp.get("resolves", []) if comp.get("resolution") else []
    outstanding = [e for e in events if e["decision"] == "difference" and e["id"] not in resolved]
    machine_issue = (comparison or {}).get("result") in ("difference", "unsure")
    disputed = bool(outstanding or machine_issue)
    original_view = {k:v for k,v in view.items() if k not in ("analysis","result")}
    prior_readings = ("analysis" in view and last.get("view") == original_view and
                      last.get("version") == digest(original_view))
    statement_approved = (has_statement and comp.get("result") == "match" and not disputed
                          and last.get("decision") == "approve" and (last.get("version") == version or prior_readings))
    approved = bool(checked and statement_approved)
    preapproved = bool((statement_checked or conditional) and not checked and statement_approved)
    raw_confirmation = bool(
        comp.get("needs_author_confirmation")
        or any(row.get("needs_author_confirmation") for row in comp.get("analysis", {}).get("cases", []))
    )
    needs_author_confirmation = bool(raw_confirmation and not statement_approved)
    if outstanding:
        issue, actor, step = " · ".join(e["comment"] for e in outstanding), "Proof agent", "Investigate the reported difference and record a resolution."
    elif machine_issue:
        issue, actor, step = (comparison.get(k,"") for k in ("issue","actor","next"))
    elif not has_statement:
        if work.get("status") in ("closed", "conditional"):
            step = ("Refresh the Lean audit for the current sources." if not (checked or conditional)
                    else "Refresh the legacy audit to record statement fingerprints for optional review.")
        elif work.get("statement_check"):
            step = "Refresh the statement audit for the current sources."
        else:
            step = work.get("next") or "Finish the Lean check."
        issue, actor = "", "Proof agent"
    elif not comp:
        issue, actor, step = "", "Proof agent", "Prepare independent paper and Lean readings."
    elif "analysis" not in comp:
        issue, actor, step = "", "Proof agent", "Add the case-by-case justification and recommendation."
    elif needs_author_confirmation:
        issue = "Unattended reading awaits author confirmation."
        actor = "Author"
        step = "Confirm the chosen reading, added hypothesis, or restriction, or report a difference."
    elif conditional:
        if preapproved:
            issue, actor, step = "", "Proof agent", work.get("next") or "Close the assumed prerequisite claims and reassemble."
        else:
            issue, actor, step = "", "Author (optional)", "Review the conditionally proved statement whenever convenient while prerequisites remain open."
    elif not checked:
        if preapproved:
            issue, actor, step = "", "Proof agent", work.get("next") or "Finish the Lean proof."
        else:
            issue, actor, step = "", "Author (optional)", "Review the drafted statement whenever convenient while proof work continues."
    else:
        issue, actor, step = "", "Author (optional)", "Review the comparison whenever convenient."
    return dict(id=claim["id"], title=claim["title"], view=view, version=version,
                token=digest([version, comparison, last.get("id"), checked, bool(conditional), list(assumes),
                              bool(statement_checked), needs_author_confirmation, defaults]),
                events=events, defaults=defaults,
                axiom_profile=axiom_prof, external_packages=ext_pkgs, noncomputable_constants=noncomp,
                checked=checked, conditional=bool(conditional), assumes=list(assumes),
                statement_checked=has_audit,
                basis=basis, proof_metrics=proof_metrics,
                distilled=distilled, undistilled=bool(undistilled),
                supplement_url=supplement_url,
                step_verification=step_verification,
                approved=approved, preapproved=preapproved, disputed=disputed,
                needs_author_confirmation=needs_author_confirmation,
                needs_author_confirmation_via=[],
                ready=bool("analysis" in view and comp.get("result")=="match" and not disputed),
                feedback_open=bool(outstanding), approved_before_analysis=bool((approved or preapproved) and prior_readings),
                stronger_result=stronger if not disputed else "",
                author_scope=last.get("scope_note","") if (approved or preapproved) else "",
                assessment={"match":"Automated comparison found no discrepancy","difference":"Difference found",
                            "unsure":"Interpretation unresolved"}.get(comp.get("result"), "Comparison pending"),
                issue=issue, actor=actor, next=step, resolution=comp.get("resolution",""))


def _audit_package(work):
    if work.get("status") in ("closed", "conditional") and work.get("closure"):
        return work["closure"]["package"]
    return (work.get("statement_check") or work["closure"])["package"]


def exact_sources(root, work, audit):
    from atlas import local
    result = []
    if not audit:
        return result
    package = _audit_package(work)
    seen = set()
    for c in sorted(audit.get("statement", {}).get("constants", []),
                    key=lambda x:(x["name"] != audit["expected"], x["name"])):
        lines = c.get("lines")
        if not lines or (c["file"],tuple(lines)) in seen:
            continue
        seen.add((c["file"],tuple(lines)))
        source = local(root, package + "/" + c["file"]).read_text(encoding="utf-8-sig").splitlines()
        item = dict(name=c["name"], file=c["file"], lines=lines,
                    text="\n".join(source[lines[0]-1:lines[1]]))
        if c.get("noncomputable"):
            item["noncomputable"] = True
        if c.get("pp_no_notation"):
            item["pp_no_notation"] = c["pp_no_notation"]
        result.append(item)
    return result


def witness_source(root, work, audit):
    from atlas import local
    hyp = (audit or {}).get("hypotheses")
    if not hyp:
        return None
    item = dict(declaration=hyp["declaration"], proposition=hyp["proposition"])
    file, lines = hyp.get("file"), hyp.get("lines")
    if file and lines:
        package = _audit_package(work)
        source = local(root, package + "/" + file).read_text(encoding="utf-8-sig").splitlines()
        item.update(file=file, lines=lines, text="\n".join(source[lines[0]-1:lines[1]]))
    return item


def get_packet(root, cid):
    from atlas import (
        _is_undistilled, claim_basis, current_statement_audit, evaluate_step_verification,
        extract_proof_metrics, load_bound_tex_sources, local, manuscript_claims,
        proof_work_profile, read_source, resolve_claim_step_map, supplement_anchor,
    )
    project = read(root/"project.json", {})
    read_source(root,project["pdf"])
    claim = next((c for c in manuscript_claims(root,project) if c["id"]==cid), None)
    if claim is None:
        raise ValueError("Unknown claim")
    work = project.get("work", {}).get(cid, {})
    reader = read(local(root,project["reader"]), {}) if project.get("reader") else {}
    note = reader.get("claims", {}).get(cid, {})
    basis = claim_basis(cid, note, work)
    audit = None
    checked = False
    conditional = False
    statement_checked = False
    assumes = []
    if work.get("status") in ("closed", "conditional") or work.get("statement_check"):
        try:
            audit, checked = current_statement_audit(root,cid,work)
            statement_checked = True
            if work.get("status") == "conditional":
                conditional = True
                assumes = list((audit or {}).get("assumes") or [])
        except (ValueError, OSError):
            pass
    comp = read(root/"comparisons.json", {}).get(cid)
    profile = proof_work_profile(project)
    undistilled = _is_undistilled(cid, work, profile, checked, conditional)
    distilled = work.get("distilled") if isinstance(work.get("distilled"), bool) else None
    metrics = extract_proof_metrics(audit)
    tex_sources = load_bound_tex_sources(root, project)
    default_main = ((work.get("assembly") or {}).get("declaration")
                    or (work.get("closure") or {}).get("declaration")
                    or (audit or {}).get("declaration"))
    step_map = resolve_claim_step_map(root, cid, work, note, tex_sources, default_main=default_main)
    step_verif = evaluate_step_verification(
        cid, step_map, audit, proof_checked=(checked or conditional), changed=False,
    )
    has_supp_entry = basis == "supplied" or bool(step_verif and step_verif.get("supplied_steps", 0) > 0)
    supp_url = f"supplement.md#{supplement_anchor(cid)}" if has_supp_entry else ""
    data = packet(root,project,claim,work,audit,comp,history(root,cid),checked,statement_checked,
                  conditional=conditional,assumes=assumes,basis=basis,proof_metrics=metrics,
                  distilled=distilled,undistilled=undistilled,supplement_url=supp_url,
                  step_verification=step_verif)
    data["page"] = work.get("page") or note.get("page")
    data["sources"] = exact_sources(root,work,audit)
    data["witness"] = witness_source(root,work,audit)
    return data


@contextmanager
def project_lock(root):
    path = Path(tempfile.gettempdir()) / ("proof-atlas-" + digest(str(root.resolve())) + ".lock")
    with path.open("a+b") as lock:
        if lock.tell() == 0:
            lock.write(b"0")
            lock.flush()
        lock.seek(0)
        if os.name == "nt":
            import msvcrt
            msvcrt.locking(lock.fileno(), msvcrt.LK_LOCK, 1)
        else:
            import fcntl
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        yield


def decide(root,cid,token,decision,by,comment="",paper_edit="",scope_note=""):
    from atlas import atomic
    if decision not in ("approve","difference","skip"):
        raise ValueError("Unknown decision")
    with project_lock(root):
        data = get_packet(root,cid)
        if token != data["token"]:
            raise ValueError("The evidence or review changed. Reload and review the current version.")
        if decision == "skip":
            return
        if not by.strip() or (decision=="difference" and not comment.strip()):
            raise ValueError("Enter your name and describe any difference.")
        if decision=="approve" and not data["ready"]:
            raise ValueError("Approval requires a current checked comparison with no outstanding difference.")
        event = dict(by=by.strip(), decision=decision, comment=comment.strip(), version=data["version"],
                     at=datetime.now(timezone.utc).isoformat(), view=data["view"], sources=data["sources"])
        if data["defaults"]:
            event["defaults"] = data["defaults"]
        if paper_edit.strip():
            event["paper_edit"] = paper_edit.strip()
        if scope_note.strip():
            event["scope_note"] = scope_note.strip()
        if data["stronger_result"]:
            event["stronger_result_seen"] = data["stronger_result"]
        event["id"] = digest(event)
        path = root/"reviews.json"
        book = read(path, {"version":1,"claims":{}})
        book["claims"].setdefault(cid,[]).append(event)
        atomic(path, (json.dumps(book,indent=2,ensure_ascii=False)+"\n").encode())


def save_comparison(root,cid,record):
    """Install the agent's two readings only against the evidence it actually read."""
    from atlas import atomic
    with project_lock(root):
        data = get_packet(root,cid)
        if not data["statement_checked"] or not data["view"]["bindings"]["statement"]:
            raise ValueError("Refresh the checked statement fingerprint before recording a comparison")
        if record.get("bindings") != data["view"]["bindings"]:
            raise ValueError("Comparison inputs changed; repeat the readings")
        required = ("paper_reading","lean_reading","paper_refs","lean_refs")
        if any(not isinstance(record.get(k),str) or not record[k].strip() for k in required):
            raise ValueError("Supply both independent mathematical readings and their source references")
        result = record.get("result")
        if result not in ("match","difference","unsure"):
            raise ValueError("Choose match, difference or unsure")
        validate_analysis(record.get("analysis"), result, require_kinds=True)
        if "needs_author_confirmation" in record:
            if type(record["needs_author_confirmation"]) is not bool:
                raise ValueError("needs_author_confirmation must be a boolean")
            if record["needs_author_confirmation"] and not any(
                row.get("kind") in CONFIRMATION_KINDS for row in record["analysis"]["cases"]
            ):
                raise ValueError(
                    "needs_author_confirmation requires at least one chosen reading, added hypothesis, or restriction case"
                )
        assessments = record["analysis"].get("default_assessments", {})
        expected_ids = {finding["id"] for finding in data["defaults"]}
        if not isinstance(assessments, dict) or set(assessments) != expected_ids:
            raise ValueError("Supply one assessment for each current default-value finding, keyed by its id")
        for finding_id, assessment in assessments.items():
            if (not isinstance(assessment, dict) or assessment.get("status") not in ("justified", "needs attention")
                    or not isinstance(assessment.get("explanation"), str) or not assessment["explanation"].strip()):
                raise ValueError(f"{finding_id}: give a status (justified or needs attention) and a short explanation")
        if "stronger_result" in record and (result!="match" or
                not isinstance(record["stronger_result"],str) or not record["stronger_result"].strip()):
            raise ValueError("Use a stronger-result note only for a match and describe the extra conclusion")
        if result != "match" and (record.get("actor") not in ("Proof agent","Author") or
                                  not all(isinstance(record.get(k),str) and record[k].strip() for k in ("issue","next"))):
            raise ValueError("Record the precise issue, next actor and action")
        path=root/"comparisons.json"
        comparisons=read(path,{})
        prior=comparisons.get(cid,{})
        if prior.get("result") in ("difference","unsure") and result=="match" and not record.get("resolution"):
            raise ValueError("Record how the prior discrepancy was resolved")
        ids={e["id"] for e in data["events"] if e["decision"]=="difference"}
        resolves=record.get("resolves",[])
        if not isinstance(resolves,list) or any(i not in ids for i in resolves) or (resolves and not record.get("resolution")):
            raise ValueError("Reference reported feedback IDs and explain the resolution")
        comparisons[cid]=record
        atomic(path,(json.dumps(comparisons,ensure_ascii=False,indent=2)+"\n").encode())


def terminal(root,labels,by,ask=input):
    import sys
    from atlas import manuscript_claims
    if not sys.stdin.isatty() or not by.strip():
        raise ValueError("Review in an interactive terminal with --by NAME")
    project = read(root/"project.json", {})
    for cid in labels or [c["id"] for c in manuscript_claims(root,project)]:
        data=get_packet(root,cid)
        if not labels and (data["approved"] or data.get("preapproved") or not data["statement_checked"]):
            continue
        print(cid, data["view"]["edition"], data["view"]["excerpt"], sep="\n")
        if data["stronger_result"]:
            print("Lean proves more",data["stronger_result"],sep="\n")
        if data["author_scope"]:
            print("Author's scope note",data["author_scope"],sep="\n")
        view=data["view"]
        assessments = view.get("analysis", {}).get("default_assessments", {})
        for finding in data["defaults"]:
            assessment = assessments.get(finding["id"], {})
            print(f'{finding["constant"]} · {finding["construct"]} · {assessment.get("status", "not assessed")}',
                  assessment.get("explanation", ""), sep="\n")
        if analysis := view.get("analysis"):
            print("Agent analysis", analysis["summary"], sep="\n")
            for row in analysis["cases"]:
                print(row["case"]+" · "+row.get("kind", "not classified"), "Paper: "+row["paper"], "Lean: "+row["lean"],
                      row["why"], sep="\n")
            print("Scope", analysis["scope"], sep="\n")
            if not data["feedback_open"]:
                print(ADVICE[view["result"]], analysis["advice"], sep="\n")
                if analysis.get("suggested_feedback"):
                    print("Suggested feedback", analysis["suggested_feedback"], sep="\n")
        for key in ("paper_reading","paper_refs","lean_reading","lean_refs"):
            print(data["view"][key])
        for source in data["sources"]:
            print(source["file"],source["lines"],source["text"],sep="\n")
        print(data["assessment"],data["issue"],data["actor"],data["next"],sep="\n")
        for event in data["events"]:
            print(event["at"],event["by"],event["decision"],event["comment"])
        options = f"Type {cid} to approve, " if data["ready"] else ""
        answer=ask(options+"! to report a difference, or Enter to skip: ").strip()
        if answer=="!":
            decide(root,cid,data["token"],"difference",by,ask("What differs? "))
        elif answer==cid and data["ready"]:
            decide(root,cid,data["token"],"approve",by,scope_note=ask("Optional scope note for this approval (Enter to omit): "))
