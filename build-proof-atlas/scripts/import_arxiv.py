"""Import an arXiv edition and build a first paper Atlas (Python 3.9+)."""
import argparse
import gzip
import hashlib
import html
from html.parser import HTMLParser
import io
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from urllib.request import Request, urlopen

from atlas import build, inventory


ID = r"(?:\d{4}\.\d{4,5}|[a-z][a-z0-9.-]*/\d{7})"
LIMIT = 128 * 1024 * 1024
KINDS = {"theorem", "lemma", "proposition", "corollary", "conjecture", "claim"}


def read_bounded(stream):
    data = stream.read(LIMIT + 1)
    if len(data) > LIMIT:
        raise ValueError("Manuscript exceeds the import limit")
    return data


def fetch(url):
    request = Request(url, headers={"User-Agent": "ProofAtlas/1.0 (paper import)"})
    with urlopen(request, timeout=90) as response:
        return read_bounded(response)


class Citation(HTMLParser):
    def __init__(self):
        super().__init__()
        self.authors = []
        self.year = ""

    def handle_starttag(self, tag, attrs):
        fields = dict(attrs)
        if tag != "meta" or not fields.get("content"):
            return
        value = " ".join(fields["content"].split())
        if fields.get("name") == "citation_title":
            self.title = value
        elif fields.get("name") == "citation_author":
            self.authors.append(value)
        elif fields.get("name") == "citation_date" and re.match(r"^\d{4}\b", value):
            self.year = value[:4]


def source_files(data):
    files = {}
    try:
        archive = tarfile.open(fileobj=io.BytesIO(data), mode="r:*")
    except tarfile.ReadError:
        if data.startswith(b"\x1f\x8b"):
            with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream:
                data = read_bounded(stream)
        if b"\\documentclass" not in data:
            raise ValueError("Expected a TeX submission")
        return {"main.tex": data}
    total = 0
    with archive:
        for entry in archive:
            if not entry.isfile() or not entry.name.lower().endswith(".tex"):
                continue
            total += entry.size
            parts = PurePosixPath(entry.name).parts
            if (not parts or total > LIMIT or len(files) >= 5000 or
                    any(not re.fullmatch(r"[\w .()+-]+", p) or p.endswith((" ", "."))
                        or PureWindowsPath(p).is_reserved() for p in parts)):
                raise ValueError("Unsupported TeX archive path or size")
            name = "/".join(parts)
            if name.casefold() in {s.casefold() for s in files}:
                raise ValueError(f"Duplicate TeX path: {name}")
            files[name] = archive.extractfile(entry).read()
    return files


def active(text):
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def ordered_sources(files, main):
    texts = {k: active(v.decode("utf-8-sig")) for k, v in files.items()}
    roots = [k for k, v in texts.items() if re.search(r"\\documentclass\b", v)]
    if main is None:
        if len(roots) != 1:
            raise ValueError(f"Choose --main from document roots {roots}")
        main = roots[0]
    order, includes = [], {}
    def visit(name):
        if name in order or name not in texts:
            raise ValueError(f"Repeated or unavailable TeX input: {name}")
        order.append(name)
        includes[name] = []
        for match in re.finditer(r"\\(?:input|include)\s*\{([^{}]+)\}", texts[name]):
            arg = match[1]
            arg = arg if arg.endswith(".tex") else arg + ".tex"
            candidates = [str(PurePosixPath(main).parent / arg), str(PurePosixPath(name).parent / arg)]
            child = next((p for p in candidates if p in texts), arg)
            includes[name].append((texts[name].count("\n", 0, match.start())+1, child))
            visit(child)
    visit(main)
    return order, texts, includes


def _read_braced(text, pos):
    """Read one balanced `{...}` group starting at `pos` (after skipping whitespace)."""
    n = len(text)
    while pos < n and text[pos].isspace():
        pos += 1
    if pos >= n or text[pos] != "{":
        return None, pos
    depth = 0
    start = pos + 1
    i = pos
    while i < n:
        ch = text[i]
        if ch == "\\" and i + 1 < n:
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[start:i], i + 1
        i += 1
    return None, pos


def _strip_tex_formatting(title):
    """Unwrap simple LaTeX formatting wrappers like `\\textbf{Theorem}` into plain text."""
    text = title.strip()
    wrapper = re.compile(
        r"\\(?:textbf|textit|textnormal|textrm|textsc|textsf|texttt|emph|mathbf|mathrm)\s*\{"
    )
    for _ in range(8):
        m = wrapper.search(text)
        if not m:
            break
        inner, end = _read_braced(text, m.end() - 1)
        if inner is None:
            break
        text = text[:m.start()] + inner + text[end:]
    text = re.sub(r"\\(?:bfseries|itshape|rmfamily|scshape|sffamily|ttfamily|normalfont)\b\s*", "", text)
    text = text.replace("{", "").replace("}", "")
    return " ".join(text.split())


def parse_newtheorems(text):
    """Extract `(env_name, printed_title, canonical_kind)` tuples from `\\newtheorem` declarations."""
    results = []
    for match in re.finditer(r"\\newtheorem\*?", text):
        pos = match.end()
        env, pos = _read_braced(text, pos)
        if not env or not re.fullmatch(r"[\w*-]+", env.strip()):
            continue
        env = env.strip()
        # Optional [numbered_like] argument before the printed title.
        opt = re.match(r"\s*\[[^\]]*\]", text[pos:])
        if opt:
            pos += opt.end()
        raw_title, pos = _read_braced(text, pos)
        if raw_title is None:
            continue
        printed = _strip_tex_formatting(raw_title)
        canonical = printed.lower()
        if canonical in KINDS:
            results.append((env, printed, canonical))
    return results


def pdf_pages(path):
    tool = shutil.which("pdftotext")
    if tool:
        result = subprocess.run([tool, "-enc", "UTF-8", str(path), "-"], capture_output=True)
        if result.returncode == 0:
            return result.stdout.decode("utf-8").split("\f")
    try:
        import fitz
    except ImportError:
        print(
            "Warning: neither 'pdftotext' (poppler-utils) nor PyMuPDF ('fitz') is installed; "
            "skipping automatic PDF page matching. Install poppler-utils or python3-fitz "
            "(and python3-pil for Folio figure cropping).",
            file=sys.stderr,
        )
        return []
    with fitz.open(path) as doc:
        return [page.get_text() for page in doc]


def identify(claims, pages, names):
    notes, candidates = {}, []
    labels = {c["id"] for c in claims}
    normalized = [" ".join(re.sub(r"(?<=\w)-\s*\n\s*(?=\w)", "", p).split()) for p in pages]
    for c in claims:
        key = c["id"]
        heading = " ".join(c["title"].split())
        pattern = re.compile(r"\b(" + re.escape(names[c["kind"]]) +
                             r"\s+[\d.]*\d)\s*\(\s*" + re.escape(heading) + r"\s*\)", re.I)
        matches = [(page, m[1]) for page, s in enumerate(normalized, 1) for m in pattern.finditer(s)]
        if len(matches) == 1:
            page, ref = matches[0]
            notes[key] = dict(reference=ref, page=page)
        if c["adjacent_proof"]:
            proof = active(c["excerpt"]).split(r"\begin{proof}", 1)[-1]
            for group in re.findall(r"\\(?:ref|cref|Cref|autoref)\{([^}]+)\}", proof):
                for target in (t.strip() for t in group.split(",")):
                    edge = dict(claim=key, prerequisite=target)
                    if target in labels and target != key and edge not in candidates:
                        candidates.append(edge)
    return notes, candidates


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def prepare(args, root):
    match = re.fullmatch(r"(?:https?://arxiv\.org/(?:abs|pdf)/|arXiv:)?(" + ID +
                         r")(v[1-9]\d*)?(?:\.pdf)?/?", args.paper.strip())
    if not match:
        raise ValueError("Expected an arXiv identifier or arxiv.org edition URL")
    paper, version = match.groups()
    if bool(args.archive) != bool(args.pdf):
        raise ValueError("Use --archive and --pdf together for a cached submission")
    if args.archive and (not version or not args.title):
        raise ValueError("A cached import needs the exact edition and its --title")
    parser = Citation()
    if not args.archive:
        record = fetch("https://arxiv.org/abs/" + paper + (version or "")).decode("utf-8")
        parser.feed(record)
        title = args.title or getattr(parser, "title", None)
        if not version:
            versions = re.findall(r"\[v(\d+)\]", html.unescape(record))
            if not versions:
                raise ValueError("Cannot resolve latest edition; supply a versioned arXiv URL")
            version = "v" + str(max(map(int, versions)))
    else:
        title = args.title
    if not title:
        raise ValueError("Cannot read title; supply --title")
    edition = paper + version
    dest = root / "manuscript"
    dest.mkdir(exist_ok=True)
    def record_file(name, data):
        path = dest / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return dict(path=path.relative_to(root).as_posix(), sha256=hashlib.sha256(data).hexdigest())
    pdf = args.pdf.read_bytes() if args.pdf else fetch("https://arxiv.org/pdf/" + edition)
    if not pdf.startswith(b"%PDF-"):
        raise ValueError("Edition download is not a PDF")
    pdf_info = record_file("paper.pdf", pdf)
    archive = args.archive.read_bytes() if args.archive else fetch("https://arxiv.org/src/" + edition)
    archive_info = record_file("submission.source", archive)
    files = source_files(archive)
    order, texts, includes = ordered_sources(files, args.main)
    names = {k: k.title() for k in KINDS}
    env_kinds = {}
    for name in order:
        for env, printed, canonical in parse_newtheorems(texts[name]):
            names[env] = printed
            if env.casefold() != canonical:
                env_kinds[env] = canonical
    per_file, sources = {}, []
    for name in order:
        info = record_file("tex/" + name, files[name])
        sources.append(info)
        per_file[name] = list(inventory(files[name].decode("utf-8-sig"), info["path"], sorted(names)))
    def manuscript_order(name):
        events = [(c["line"], False, c) for c in per_file[name]] + [
            (line, True, child) for line, child in includes[name]]
        for _, child, item in sorted(events, key=lambda e: e[0]):
            if child:
                yield from manuscript_order(item)
            else:
                yield item
    claims = list(manuscript_order(order[0]))
    if not claims:
        raise ValueError("No labeled theorem-like environments found; review the source macros")
    pages = pdf_pages(root / pdf_info["path"])
    notes, candidates = identify(claims, pages, names)
    save(root/"reader.json", dict(schema_version=1, claims=notes, dependencies=[]))
    save(root/"import-review.json", dict(candidate_dependencies=candidates,
         unmatched_pages=[c["id"] for c in claims if c["id"] not in notes],
         source_order_to_review=order, unvisited_tex=sorted(set(files)-set(order))))
    project_doc = dict(schema_version=1, title=" ".join(title.split()),
         authors=args.author or parser.authors, citation_details=args.citation_details or parser.year,
         edition="arXiv:"+edition, revision=edition, publication="https://arxiv.org/abs/"+edition,
         tex=sources, pdf=pdf_info, source_archive=archive_info, environments=sorted(names),
         claim_order=[c["id"] for c in claims], hosting={"decision":"pending"}, reader="reader.json", work={})
    if env_kinds:
        project_doc["environment_kinds"] = env_kinds
    save(root/"project.json", project_doc)
    build(root)
    print(f"{len(notes)}/{len(claims)} unique PDF headings; {len(candidates)} dependency candidates.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper")
    parser.add_argument("project", type=Path)
    parser.add_argument("--main", help="Main TeX path inside the source archive")
    parser.add_argument("--title")
    parser.add_argument("--author", action="append", help="Author in citation order; repeat for each author")
    parser.add_argument("--citation-details", help="Publication details following the edition, such as its date")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--pdf", type=Path)
    parser.add_argument("--init-existing", action="store_true",
                        help="Initialize Proof Atlas inside an existing directory (fails if project.json already exists)")
    args = parser.parse_args()
    target = args.project.resolve()
    if args.init_existing:
        if (target / "project.json").exists():
            parser.error("project.json already exists; resume existing projects with preview.py")
        target.mkdir(parents=True, exist_ok=True)
        prepare(args, target)
    else:
        if target.exists():
            parser.error("Choose a new directory (or pass --init-existing); resume existing projects with preview.py")
        target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=target.parent) as tmp:
            stage = Path(tmp)/"project"
            stage.mkdir()
            prepare(args, stage)
            stage.rename(target)
    print(f"Explorer: {target/'dist/proofs/index.html'}\nDashboard: {target/'dist/progress.html'}")
    print("Hosting decision pending. Ask the author where to host this paper's explorer and dashboard.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, tarfile.TarError) as exc:
        sys.exit(str(exc))
