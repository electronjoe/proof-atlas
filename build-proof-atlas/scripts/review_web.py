"""Local and published views of the same correspondence evidence."""
import html
import json
import secrets
import tempfile
import threading
import webbrowser
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, urlsplit
from urllib.request import urlopen

from author_review import ADVICE, BADGE, decide, digest, get_packet, review_url
import manuscript_edits


def document(title,body,base="../"):
    from atlas import esc
    return (f'<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">'
            f'<title>{esc(title)} · Proof Atlas</title><link rel="stylesheet" href="{base}review.css"></head><body>'
            f'<header><a href="{base}index.html">Proof Atlas<span>.</span></a><nav><a href="{base}review.html">Review queue</a> '
            f'<a href="{base}edits.html">Manuscript edits</a> <a href="{base}progress.html">Dashboard</a> <a href="{base}guide.html">How to use this atlas</a></nav></header>'
            f'<main>{body}</main></body></html>').encode()


def default_panel(findings, view):
    from atlas import esc
    if not findings:
        return ""
    assessments = view.get("analysis", {}).get("default_assessments", {})
    groups = {"needs attention": [], "not assessed": [], "justified": []}
    for finding in findings:
        assessment = assessments.get(finding["id"], {})
        status = assessment.get("status", "not assessed")
        explanation = esc(assessment.get("explanation", ""))
        typ = " on " + esc(finding["type"]) if finding.get("type") else ""
        location = esc(finding["file"])
        if finding.get("lines"):
            location += f' L{esc(finding["lines"][0])}'
        groups[status].append(
            f'<li><strong>{esc(status)}</strong> {explanation}<br>'
            f'<code>{esc(finding["construct"])}</code>{typ} in <code>{esc(finding["constant"])}</code> '
            f'({location}) · {esc(finding["meaning"])}</li>')
    parts = ['<section><h2>Lean default values</h2>']
    unresolved = groups["needs attention"] + groups["not assessed"]
    if unresolved:
        parts.extend(['<ul>', *unresolved, '</ul>'])
    if groups["justified"]:
        parts.extend(['<details><summary>Show explained uses</summary><ul>', *groups["justified"], '</ul></details>'])
    return "".join(parts) + "</section>"


def render(data,secret=None,notice=""):
    from atlas import esc
    v=data["view"]
    cid=esc(data["id"])
    def para(value): return f'<p>{esc(value)}</p>' if value else ""
    def analysis_panel(view, feedback_open=False):
        analysis = view.get("analysis")
        if not analysis:
            return ""
        rows = "".join(
            "<tr><th scope=\"row\">"+esc(row["case"])+"<br><small>"+esc(row.get("kind","not classified"))
            + (" · needs author confirmation" if row.get("needs_author_confirmation") else "")+"</small></th>"+
            "".join("<td>"+esc(row[k])+"</td>" for k in ("paper","lean","why"))+"</tr>"
            for row in analysis["cases"])
        parts = ['<section class="analysis"><h2>How the statements compare</h2>', para(analysis["summary"]),
                 '<div class="case-table"><table><caption>Case-by-case comparison</caption><thead><tr>',
                 '<th>Case</th><th>Paper</th><th>Checked Lean statement</th><th>Why</th></tr></thead><tbody>',
                 rows, '</tbody></table></div><h3>Scope of the conclusion</h3>', para(analysis["scope"])]
        if feedback_open:
            parts.append('<h3>Author feedback is open</h3><p>Review the reported difference below before deciding.</p>')
        else:
            parts.extend(['<aside><h3>Agent recommendation · '+esc(ADVICE[view["result"]])+'</h3>', para(analysis["advice"])])
            if wording := analysis.get("suggested_feedback"):
                parts.extend(['<h4>Suggested wording for feedback</h4><blockquote>', esc(wording), '</blockquote>'])
            parts.append('</aside>')
        return "".join(parts)+'</section>'
    def sources(items):
        rendered = []
        for s in items:
            nc = " · noncomputable" if s.get("noncomputable") else ""
            unfolded = (
                '<details><summary>Notation-free Lean signature (pp.notation false)</summary>'
                f'<pre>{esc(s["pp_no_notation"])}</pre></details>'
                if s.get("pp_no_notation") else ""
            )
            rendered.append(
                f'<details><summary>{esc(s["name"])} · {esc(s["file"])} L{s["lines"][0]}{nc}</summary>'
                f'<pre>{esc(s["text"])}</pre>{unfolded}</details>'
            )
        return "".join(rendered)
    def metadata_panel():
        from atlas import BASIS_LABELS
        parts = []
        if data.get("axiom_profile"):
            parts.append(f'<p><strong>Axiom profile:</strong> {esc(data["axiom_profile"])}</p>')
        if data.get("basis"):
            b = data["basis"]
            label = BASIS_LABELS.get(b, b)
            extra = (f' · <a href="../{esc(data["supplement_url"])}">Read supplied proof in supplement.md</a>'
                     if b == "supplied" and data.get("supplement_url") else "")
            parts.append(f'<p><strong>Proof basis:</strong> {esc(label)} (<code>{esc(b)}</code>){extra}</p>')
        sv = data.get("step_verification")
        if sv and sv.get("verified") and sv.get("badge"):
            supp_extra = (
                f' · <a href="../{esc(data["supplement_url"])}">Read supplied steps in supplement.md</a>'
                if sv.get("supplied_steps") and data.get("supplement_url") else ""
            )
            parts.append(
                f'<p><strong>Step verification:</strong> {esc(sv["badge"])} '
                f'({sv["paper_steps"]} verbatim paper / {sv["supplied_steps"]} supplied){supp_extra}</p>'
            )
        metrics = data.get("proof_metrics")
        if metrics:
            bits = []
            if "checked_lean_loc" in metrics:
                bits.append(f'{metrics["checked_lean_loc"]} checked Lean LoC')
            if "reachable_local_defs" in metrics:
                bits.append(f'{metrics["reachable_local_defs"]} reachable local defs')
            if "reachable_local_theorems" in metrics:
                bits.append(f'{metrics["reachable_local_theorems"]} reachable local theorems')
            if data.get("distilled") is True:
                bits.append("Distilled")
            elif data.get("undistilled"):
                bits.append("Exploratory proof (undistilled)")
            if bits:
                parts.append(f'<p><strong>Proof size:</strong> {esc(" · ".join(bits))}</p>')
        if data.get("noncomputable_constants"):
            names = ", ".join(f'<code>{esc(n)}</code>' for n in data["noncomputable_constants"])
            parts.append(
                f'<p><strong>Noncomputable definitions in statement:</strong> {names}. '
                'If the paper claims an explicit construction, algorithm, or runtime bound, verify whether this affects the claim.</p>'
            )
        pkgs = data.get("external_packages") or []
        third_party = [p for p in pkgs if p.get("third_party")]
        if third_party:
            items = "".join(
                f'<li><code>{esc(p["name"])}</code> ({esc(p["rev"][:12])})'
                + (f' · {esc(p["url"])}' if p.get("url") else "")
                + '</li>'
                for p in third_party
            )
            parts.append(
                '<section><h2>Third-party external dependencies</h2>'
                '<p>This Lean package depends on non-Mathlib external repositories. Review any definitions or lemmas imported from them.</p>'
                f'<ul>{items}</ul></section>'
            )
        return "".join(parts)
    def columns(view):
        return ('<div class="columns"><section><h2>Paper theorem</h2>'+para(view["paper_reading"])+
                para(view["paper_refs"])+'<details><summary>Original manuscript passage</summary><pre>'+esc(view["excerpt"])+'</pre></details></section>'
                '<section><h2>What Lean proved</h2><small>Mathematical reading of the audited Lean statement</small>'+para(view["lean_reading"] or "The agent has not supplied a current independent reading.")+
                para(view["lean_refs"])+'</section></div>')
    body=f'<p>{esc(v["edition"])} · {cid}</p><h1>{esc(data["title"])}</h1>'
    if data.get("basis") == "supplied":
        supp_href = f'../{esc(data["supplement_url"])}' if data.get("supplement_url") else "../supplement.md"
        badge_lead = ("Lean checked (proof supplied outside manuscript)" if data["checked"]
                      else "Proof supplied outside manuscript")
        body+=(f'<aside class="confirmation-warning"><h2>{esc(badge_lead)}</h2>'
               '<p>The manuscript states this claim without a complete written proof (for example, an unproved remark or skipped step); '
               f'Lean supplies the argument outside the PDF. <a href="{supp_href}">Open supplement.md</a>.</p></aside>')
    if data.get("conditional"):
        assumed_text = ", ".join(esc(a) for a in data.get("assumes", []))
        body+=(f'<p><strong>Conditional (assumes {assumed_text})</strong> · Lean checked this claim assuming '
               'unproved prerequisite statement(s). It upgrades to Lean checked once those prerequisites close.</p>')
    elif data.get("statement_checked") and not data["checked"]:
        body+='<p><strong>Statement drafted (proof in progress)</strong> · Lean checked the statement definitions; the proof is not closed yet.</p>'
    if data.get("needs_author_confirmation"):
        body+=('<aside class="confirmation-warning"><h2>Needs author confirmation</h2>'
               '<p>This comparison records an unattended reading (chosen reading, added hypothesis, or restriction). '
               'Confirm it below to approve, or report a difference.</p></aside>')
    if data.get("needs_author_confirmation_via"):
        via_links = ", ".join(
            f'<a href="../{esc(item["review_url"])}">{esc(item["reference"])}</a>'
            for item in data["needs_author_confirmation_via"]
        )
        body+=(f'<aside class="confirmation-warning"><h2>Needs author confirmation (upstream dependency)</h2>'
               f'<p>This claim depends on unconfirmed unattended reading(s) in: {via_links}.</p></aside>')
    body+=para(notice)+para(data["assessment"])
    body+=metadata_panel()
    body+=default_panel(data.get("defaults", []), v)
    if data["stronger_result"]:
        body+='<aside id="scope-note"><h2>Lean proves more</h2>'+para(data["stronger_result"])+'</aside>'
    if data["author_scope"]:
        body+='<aside id="author-scope"><h2>Author’s scope note</h2>'+para(data["author_scope"])+'</aside>'
    body+=analysis_panel(v,data["feedback_open"])+columns(v)
    if data["approved"]:
        body+=para(BADGE+" · "+data["events"][-1]["by"])
        if data["approved_before_analysis"]:
            body+=para("The author approved these same two readings before the case-by-case analysis was added.")
    elif data.get("preapproved"):
        body+=para("Statement approved (proof in progress) · "+data["events"][-1]["by"]+" · Carries over automatically at closure if Statements/ is unchanged.")
    elif any(e["decision"]=="approve" for e in data["events"]):
        body+=para("The earlier approval is historical. A fresh review is available after the current comparison is ready.")
    page = data.get("page")
    pdf = f"../manuscript.pdf#page={page}" if type(page) is int and page > 0 else "../manuscript.pdf"
    body+=(f'<p><a href="{pdf}">Paper PDF</a> · <a href="../proofs/index.html#/claim/'+quote(data["id"],safe="")+
           '?view=lean">Lean source and verification evidence</a></p>')
    if data["sources"]:
        body+='<details><summary>Inspect the exact Lean statement and definitions</summary>'+sources(data["sources"])+'</details>'
    if data.get("witness"):
        w = data["witness"]
        loc = f' · {esc(w["file"])} L{w["lines"][0]}' if w.get("file") and w.get("lines") else ""
        snippet = f'<pre>{esc(w["text"])}</pre>' if w.get("text") else ""
        body+=(f'<details><summary>Inspect the checked hypotheses example · {esc(w["declaration"])}{loc}</summary>'
               f'<p>Proves: <code>{esc(w["proposition"])}</code></p>{snippet}</details>')
    body+=para(data["issue"])+para(data["resolution"])
    body+='<p><strong>Next action · '+esc(data["actor"])+'</strong><br>'+esc(data["next"])+'</p>'
    if secret:
        body+=('<form method="post"><h2>Does the statement shown here match your paper’s theorem, including its assumptions and conclusion?</h2>'
               f'<input type="hidden" name="csrf" value="{esc(secret)}"><input type="hidden" name="token" value="{esc(data["token"])}">'
               '<label>Your name<input name="by" autocomplete="name"></label><label>Difference or question (for the proof agent)'
               '<textarea name="comment" rows="2"></textarea></label>'
               '<label>Suggested manuscript edit (optional)<textarea name="paper_edit" rows="2"></textarea></label>'
               + ('<label>Scope note to display with my approval (optional)<textarea name="scope_note" rows="2"></textarea></label>' if data["ready"] else '') +
               '<p>A suggestion saved with an approval or difference appears in <a href="../edits.html">Manuscript edits</a>.</p><div class="buttons">')
        if data["ready"]:
            body+='<button name="decision" value="approve">Yes, these match</button>'
        body+=('<button name="decision" value="difference">I see a difference</button>'
               '<button name="decision" value="skip">Skip for now</button></div>'
               '<p>Decisions save to this local project. Publishing the project shares the reviewer’s name and feedback.</p></form>')
    else:
        body+=para("To respond, ask your agent to open the local review dashboard for this paper.")
    if data["events"]:
        body+='<h2>Review history</h2>'
    for e in reversed(data["events"]):
        label=BADGE if e["decision"]=="approve" else "Difference reported"
        body+=(f'<details><summary>{esc(label)} · {esc(e["by"])} · {esc(e["at"])}</summary>'+para(e["comment"])+
               (para("Author’s scope note · "+e["scope_note"]) if e.get("scope_note") else "")+
               (para("Lean proves more · "+e["stronger_result_seen"]) if e.get("stronger_result_seen") else "")+
               para(e["view"]["edition"])+default_panel(e.get("defaults", []), e["view"])+
               analysis_panel(e["view"])+columns(e["view"])+sources(e.get("sources",[]))+'</details>')
    return document(data["title"],body)


def queue(entries):
    from atlas import esc
    def status_label(d):
        parts = []
        if d["approved"]:
            parts.append(BADGE)
        elif d.get("preapproved"):
            parts.append("Statement approved (proof in progress)")
        elif d.get("conditional"):
            parts.append(f'Conditional (assumes {", ".join(d.get("assumes", []))}) · {d["assessment"]}')
        elif d.get("statement_checked") and not d["checked"]:
            parts.append("Statement drafted (proof in progress) · " + d["assessment"])
        else:
            parts.append(d["assessment"])
        if d.get("basis") == "supplied":
            parts.append("Proof supplied outside manuscript")
        sv = d.get("step_verification")
        if sv and sv.get("verified") and sv.get("badge"):
            parts.append(sv["badge"])
        if d.get("needs_author_confirmation"):
            parts.append("Needs author confirmation")
        elif d.get("needs_author_confirmation_via"):
            refs = ", ".join(item["reference"] for item in d["needs_author_confirmation_via"])
            parts.append(f"Needs author confirmation (depends on {refs})")
        return " · ".join(parts)
    rows="".join(f'<li><a href="{review_url(d["id"])}">{esc(d["title"])}</a><br>'
                 f'{esc(status_label(d))} · {esc(d["actor"])}: {esc(d["next"])}</li>' for d in entries)
    return document("Author review",'<h1>Author review</h1><p>Compare the paper and the formal statement. Human review is optional.</p>'
                    '<p>Each next action names its owner. An active coding agent handles proof repairs during authorized work. '
                    'Submitting feedback saves it for that session or the next one. See the <a href="progress.html">dashboard</a> for reported activity.</p><ol>'+rows+'</ol>',"./")


def serve(root,open_browser=True,port=0):
    from atlas import atomic, build_local, manuscript_claims
    root=root.resolve()
    key=digest(str(root))
    session=Path(tempfile.gettempdir())/("proof-atlas-review-"+key+".json")
    try:
        cached=json.loads(session.read_bytes())
        base=f'http://127.0.0.1:{int(cached["port"])}'
        with urlopen(base+"/session",timeout=1) as response:
            if response.read(128).decode()==key:
                print(base+"/review.html",flush=True)
                if open_browser: webbrowser.open(base+"/review.html")
                return
    except (ValueError,OSError,KeyError):
        pass
    build_local(root)
    secret=secrets.token_urlsafe(32)
    def claims():
        p=json.loads((root/"project.json").read_bytes())
        return {"/"+review_url(c["id"]):c["id"] for c in manuscript_claims(root,p)}
    class Handler(SimpleHTTPRequestHandler):
        def reply(self,body,status=200):
            self.send_response(status)
            self.send_header("Content-Type","text/html; charset=utf-8")
            self.send_header("Cache-Control","no-store")
            self.send_header("X-Frame-Options","DENY")
            self.send_header("Content-Length",str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        def do_GET(self):
            if self.headers.get("Host")!=base.removeprefix("http://"):
                return self.send_error(403)
            path=urlsplit(self.path).path
            if path=="/session":
                return self.reply(key.encode())
            if path=="/edits.html":
                return self.reply(manuscript_edits.render(root,secret))
            if path.startswith("/review/") or path=="/review.html":
                try:
                    ids=claims()
                    if path=="/review.html":
                        return self.reply(queue([get_packet(root,c) for c in ids.values()]))
                    if path in ids:
                        notice="Saved locally." if urlsplit(self.path).query=="saved" else ""
                        data=get_packet(root,ids[path])
                        return self.reply(render(data,secret,notice))
                except (ValueError,KeyError,OSError) as error:
                    return self.send_error(409,str(error))
            super().do_GET()
        def do_POST(self):
            if self.headers.get("Origin")!=base or self.headers.get("Host")!=base.removeprefix("http://"):
                return self.send_error(403)
            try:
                if self.headers.get_content_type() != "application/x-www-form-urlencoded":
                    return self.send_error(415)
                size=int(self.headers.get("Content-Length","0"))
                if not 0<size<=32768: return self.send_error(413)
                values=parse_qs(self.rfile.read(size).decode(),keep_blank_values=True)
                form={k:v[0] for k,v in values.items()}
                if not secrets.compare_digest(form["csrf"],secret): return self.send_error(403)
                path=urlsplit(self.path).path
                if path=="/edits.html":
                    manuscript_edits.update(root,form["token"],form["action"],values.get("selected",[]))
                    location=path
                else:
                    cid=claims()[path]
                    decide(root,cid,form["token"],form["decision"],form.get("by",""),form.get("comment",""),form.get("paper_edit",""),form.get("scope_note",""))
                    location="/review.html" if form["decision"]=="skip" else path+"?saved"
                self.send_response(303)
                self.send_header("Location",location)
                self.end_headers()
            except (ValueError,KeyError,OSError) as error:
                self.reply(document("Review needs attention",'<h1>Review needs attention</h1><p>'+html.escape(str(error))+
                                    '</p><a href="">Reload the claim</a>'),409)
    from preview import inputs, watch
    with ThreadingHTTPServer(("127.0.0.1",port),partial(Handler,directory=str(root/"dist"))) as server:
        base=f"http://127.0.0.1:{server.server_port}"
        atomic(session,json.dumps({"port":server.server_port}).encode())
        stop=threading.Event()
        thread=threading.Thread(target=watch,args=(root,stop,inputs(root)),daemon=True)
        thread.start()
        try:
            print(base+"/review.html",flush=True)
            if open_browser: webbrowser.open(base+"/review.html")
            server.serve_forever()
        finally:
            stop.set()
            thread.join(timeout=5)
