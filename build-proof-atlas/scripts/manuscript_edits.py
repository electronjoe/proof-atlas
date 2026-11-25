"""Manuscript suggestions and local editorial decisions, separate from theorem reviews."""
import json
from datetime import datetime, timezone
from html import escape
from urllib.parse import urlsplit

from author_review import digest, project_lock, read, review_url


def inventory(root):
    book = read(root/"manuscript-edits.json", {"version": 1, "edits": {}})
    if book.get("version") != 1:
        raise ValueError("Unknown manuscript edit format")
    edits = dict(book["edits"])
    handled = {item.get("review_id") for item in edits.values()}
    for cid, events in read(root/"reviews.json", {}).get("claims", {}).items():
        for event in events:
            if event.get("paper_edit") and event["id"] not in handled:
                edits.setdefault(event["id"], dict(claim=cid, edition=event["view"]["edition"],
                    reason=event["paper_edit"], status="Suggested", review_id=event["id"]))
    return book, edits


def token(book, edits):
    return digest([edits, book.get("cleared", {})])


def propose(root, key, *, claim, edition, location="", original="", replacement="",
            reason="", status="Proposed", evidence="", review_id=None, force=False):
    """Create or update a manuscript edit suggestion without disturbing cleared entries."""
    from atlas import atomic
    if not isinstance(key, str) or not key.strip():
        raise ValueError("Manuscript edit key must be a non-empty string")
    if status not in ("Suggested", "Proposed", "Draft requested", "Draft ready", "Applied"):
        raise ValueError(f"Unsupported manuscript edit status: {status}")
    with project_lock(root):
        book, _ = inventory(root)
        cleared = book.get("cleared", {})
        if key in cleared and not force:
            return key, book["edits"].get(key), False
        existing = book["edits"].get(key, {})
        entry = dict(existing)
        entry.update(claim=claim, edition=edition)
        if location:
            entry["location"] = location
        if original:
            entry["original"] = original
        if replacement:
            entry["replacement"] = replacement
        if reason:
            entry["reason"] = reason
        if evidence:
            entry["evidence"] = evidence
        if review_id:
            entry["review_id"] = review_id
        # Preserve an author-initiated draft request or applied status unless forced.
        if force or existing.get("status") not in ("Draft requested", "Draft ready", "Applied"):
            entry["status"] = status
        if existing == entry and key in book["edits"]:
            return key, entry, False
        book["edits"][key] = entry
        atomic(root/"manuscript-edits.json", (json.dumps(book, indent=2, ensure_ascii=False) + "\n").encode())
        return key, entry, True


def update(root, expected, action, selected):
    from atlas import atomic
    with project_lock(root):
        book, edits = inventory(root)
        if expected != token(book, edits):
            raise ValueError("The suggestions changed. Reload the list before continuing.")
        cleared = book.setdefault("cleared", {})
        active = set(edits) - cleared.keys()
        eligible = set(cleared) & edits.keys() if action == "restore" else active
        ids = eligible if action == "clear-all" else set(selected)
        if action not in ("clear", "clear-all", "restore", "request") or not ids or not ids <= eligible:
            raise ValueError("Select one or more suggestions from the relevant list.")
        if action == "request" and any(edits[key].get("status") not in ("Suggested","Proposed") for key in ids):
            raise ValueError("Choose proposed suggestions when requesting a draft.")
        now = datetime.now(timezone.utc).isoformat()
        for key in sorted(ids):
            if action == "restore":
                del cleared[key]
            elif action == "request":
                book["edits"][key] = dict(edits[key], status="Draft requested")
            else:
                cleared[key] = now
        atomic(root/"manuscript-edits.json", (json.dumps(book,indent=2,ensure_ascii=False)+"\n").encode())


def render(root, secret=None):
    from atlas import manuscript_claims
    from review_web import document
    book, edits = inventory(root)
    project = read(root/"project.json", {})
    claims = {c["id"]:c for c in manuscript_claims(root,project)}
    cleared = book.get("cleared", {})
    out = ["<h1>Manuscript edits</h1><p>Copy a replacement into your manuscript, or request a draft from your proof agent. After handling a suggestion, clear it from the active list. You can restore it later. Theorem approvals are tracked separately.</p>"]
    for archived in (False, True):
        items = [(k,v) for k,v in edits.items() if (k in cleared) == archived]
        heading = "Cleared" if archived else "Active"
        out.append(f"<h2>{heading} ({len(items)})</h2>")
        if not items:
            out.append("<p>No "+heading.lower()+" suggestions.</p>")
            continue
        if secret:
            out.extend(['<form method="post" action="edits.html">',
                        '<input type="hidden" name="csrf" value="'+escape(secret)+'">',
                        '<input type="hidden" name="token" value="'+token(book,edits)+'">'])
        for key,item in items:
            claim = claims.get(item["claim"])
            title = claim["title"] if claim else item["claim"]
            out.append('<article class="edit"><h3>')
            if secret:
                out.append('<input type="checkbox" name="selected" aria-label="Select '+escape(title)+'" value="'+escape(key)+'"> ')
            if claim:
                out.append('<a href="'+review_url(item["claim"])+'">'+escape(title)+'</a>')
            else:
                out.append(escape(title))
            out.append('</h3><p>'+escape(item["edition"])+" · "+escape(item.get("location",""))+" · "+escape(item.get("status","Proposed"))+'</p>')
            if archived:
                out.append('<p>Cleared '+escape(cleared[key])+'</p>')
            for field,label in (("original","Current text in the cited edition"),("replacement","Proposed replacement"),("reason","Reason or suggestion")):
                if value := item.get(field):
                    out.append('<h4>'+label+'</h4><p class="edit-text">'+escape(value)+'</p>')
            if item.get("evidence"):
                evidence = item["evidence"]
                if urlsplit(evidence).scheme in ("https", "http"):
                    out.append('<p><a href="'+escape(evidence)+'">Draft or applied revision</a></p>')
                else:
                    out.append('<p>'+escape(evidence)+'</p>')
            out.append("</article>")
        if secret:
            if archived:
                out.append('<button name="action" value="restore">Restore selected</button>')
            else:
                out.append('<div class="buttons"><button name="action" value="clear">Clear selected</button>'
                           '<button name="action" value="clear-all">Clear all active suggestions</button>'
                           '<button name="action" value="request">Request draft for selected</button></div>')
            out.append("</form>")
    if not secret:
        out.append("<p>Open the local review dashboard to manage suggestions.</p>")
    return document("Manuscript edits","".join(out),"./")
