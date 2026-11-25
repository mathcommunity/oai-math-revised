"""Read the repository's existing files and assemble the paper catalogue.

Sources:
  overview.tex   discipline -> family order and family summaries
  CONTENTS.md    family -> papers, with paper titles and abstracts
  preprints/*/README.md   author, date, BibTeX, version notes, withdrawals
  lean/docs/*.md Lean formalization scope notes, keyed by family
  preprints/*/NOTES.md, AGENT_NOTES.md   community and agent notes
"""

from __future__ import annotations

import csv
import datetime
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Contribution:
    date: str  # YYYY-MM-DD
    people: list[tuple[str, str]]  # (GitHub handle or "", display name or "")
    text: str  # Markdown
    order: int = 0  # position in NOTES.md, to keep same-day entries in order


@dataclass
class Paper:
    slug: str  # folder name under preprints/
    title: str  # display title (may contain $..$ math)
    pdf: str | None  # file name of the PDF inside the folder
    abstract: str = ""  # HTML-ish text from CONTENTS.md
    family: str | None = None  # "003"
    discipline: str | None = None
    author: str = "OpenAI"
    date: str = ""
    bibtex: str = ""
    readme_extra: str = ""  # README sections other than title/author/citation
    preamble: str = ""  # README text between the byline and the first section
    status: str = "current"  # current | superseded | withdrawn
    newer: str | None = None  # slug of the newer edition, if superseded
    older: list[str] = field(default_factory=list)  # slugs of earlier editions
    lean_notes: list[str] = field(default_factory=list)  # lean/docs/*.md paths
    notes_md: str | None = None
    agent_notes_md: str | None = None
    tex_dir: str | None = None  # "build" if TeX sources are present
    withdrawn_on: str = ""
    archived_pdf: str = ""  # pre-withdrawal PDF, for withdrawn papers
    community_revised: bool = False
    contributions: list[Contribution] = field(default_factory=list)  # from NOTES.md
    contribution_problems: list[str] = field(default_factory=list)  # lines that did not parse

    @property
    def notes_body(self) -> str:
        """NOTES.md without its "Contributions" section (shown separately)."""
        return split_contributions(self.notes_md or "")[1]

    @property
    def has_notes(self) -> bool:
        """NOTES.md has some content beyond headings (contributions included)."""
        if not self.notes_md:
            return False
        return any(line.strip() and not line.lstrip().startswith("#") for line in self.notes_md.splitlines())

    @property
    def has_notes_body(self) -> bool:
        return any(line.strip() and not line.lstrip().startswith("#") for line in self.notes_body.splitlines())


@dataclass
class ComparatorCheck:
    """One row of checks/comparator-<date>/results.tsv, for the challenge files as they are now."""
    result: str        # "accepted" or "not finished"
    date: str          # YYYY-MM-DD of the run
    log: str           # repository path of the log
    note: str
    changed: bool      # the challenge's .lean or .json differs from the version that was checked


@dataclass
class LeanChallenge:
    label: str         # result label from the scope note
    challenge: str     # lean/ComparatorChallenges/X.lean
    proof: str | None  # file of the solution module named in X.json
    check: ComparatorCheck | None = None


@dataclass
class Family:
    num: str
    title: str
    summary: str
    discipline: str
    papers: list[str] = field(default_factory=list)
    lean_doc: str | None = None  # lean/docs/NNN.md, if present
    lean_challenges: list[LeanChallenge] = field(default_factory=list)  # comparator table in lean_doc

    @property
    def summary_text(self) -> str:
        """Summary without the trailing "([Lean](...))" pointer (shown as a marker instead)."""
        return re.sub(r"\s*\(\[Lean\]\([^)]*\)\)", "", self.summary)


@dataclass
class Discipline:
    name: str
    families: list[str] = field(default_factory=list)


def _contents_math(text: str) -> str:
    """CONTENTS.md writes inline math as $`...`$; normalise to $...$."""
    return re.sub(r"\$`(.+?)`\$", r"$\1$", text)


def parse_contents(root: Path):
    text = (root / "CONTENTS.md").read_text(encoding="utf-8")
    cells = re.findall(r"<td>\s*(.*?)\s*</td>", text, flags=re.S)
    families: dict[str, dict] = {}
    papers: dict[str, Paper] = {}
    current = None
    for cell in cells:
        cell = re.sub(r'^<a name="family-\d+"></a>\s*', "", cell)
        m = re.match(r"\*\*(\d{3})\. (.+?)\.\*\*\s*(.*)", cell, flags=re.S)
        if m:
            current = m.group(1)
            families[current] = {
                "title": _contents_math(m.group(2)).strip(),
                "summary": _contents_math(m.group(3)).strip(),
                "papers": [],
            }
            continue
        m = re.match(r"&emsp;\[(.+)\]\(preprints/([^/]+)/([^)]+)\)\s*(.*)", cell, flags=re.S)
        if m and current:
            slug = m.group(2)
            papers[slug] = Paper(
                slug=slug,
                title=_contents_math(m.group(1)).strip(),
                pdf=m.group(3),
                abstract=_contents_math(m.group(4)).strip(),
                family=current,
            )
            families[current]["papers"].append(slug)
    return families, papers


def parse_overview(root: Path):
    """Return [(discipline, [family numbers])] in the overview's order."""
    text = (root / "overview.tex").read_text(encoding="utf-8")
    out = []
    for line in text.splitlines():
        m = re.match(r"\\cataloguesection\{(.+?)\}\{\d+\}", line)
        if m:
            out.append((m.group(1), []))
            continue
        m = re.match(r"\\resultentry\{(\d{3})\}", line)
        if m and out:
            out[-1][1].append(m.group(1))
    return out


# NOTES.md records changes made by people in a "## Contributions" section,
# one line each:  - 2026-10-20 @handle (Optional Name), @other: What changed ([PR #3](...)).
_CONTRIB_LINE = re.compile(r"[-*]\s+(\d{4}-\d{2}-\d{2})\s+(.+?):\s+(.+?)\s*")
_PERSON = re.compile(r"@([A-Za-z0-9](?:[A-Za-z0-9-]{0,38}))(?:\s*\((.+)\))?|([^@()]+)")


def split_contributions(notes: str) -> tuple[str, str]:
    """Return (body of the Contributions section, the rest of NOTES.md)."""
    m = re.search(r"^## Contributions[ \t]*\n(.*?)(?=^## |\Z)", notes, flags=re.M | re.S)
    if not m:
        return "", notes
    return m.group(1), notes[:m.start()] + notes[m.end():]


def parse_contributions(notes: str) -> tuple[list[Contribution], list[str]]:
    section, _ = split_contributions(notes)
    entries, problems = [], []
    for line in section.splitlines():
        if not line.strip():
            continue
        m = _CONTRIB_LINE.fullmatch(line.strip())
        people = []
        try:
            m = m if m and datetime.date.fromisoformat(m.group(1)) else None
        except ValueError:  # not a calendar date
            m = None
        if m:
            # Split on commas outside parentheses: "@a (Doe, Jane), @b".
            for part in re.split(r",(?![^()]*\))", m.group(2)):
                pm = _PERSON.fullmatch(part.strip())
                if not pm:
                    break
                people.append((pm.group(1), (pm.group(2) or "").strip()) if pm.group(1) else ("", pm.group(3).strip()))
            else:
                entries.append(Contribution(date=m.group(1), people=people, text=m.group(3), order=len(entries)))
                continue
        problems.append(line.strip())
    return entries, problems


_MONTHS = "January|February|March|April|May|June|July|August|September|October|November|December"
_DATE = rf"(?:{_MONTHS}) \d{{1,2}}, \d{{4}}"


def parse_readme(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    info: dict = {}
    m = re.match(r"# \[(.+)\]\(([^)]+)\)", text)
    if m:
        info["title"], info["pdf"] = m.group(1), m.group(2)
    header = re.split(r"^## ", text, maxsplit=1, flags=re.M)[0]
    header = re.sub(r"\A# .*\n", "", header).replace("**", "")
    m = re.search(r"Author:\s*(.+?)\s*$", header, flags=re.M)
    if m:
        info["author"] = m.group(1)
    m = re.search(_DATE, header)
    if m:
        info["date"] = m.group(0)
    info["preamble"] = "\n".join(
        line for line in header.splitlines()
        if line.strip() and not re.match(rf"\s*(Author:|Date:|OpenAI\s*(·.*)?$|(?:{_MONTHS}) \d)", line))
    m = re.search(r"(```|~~~)bibtex\n(.*?)\1", text, flags=re.S)
    if m:
        info["bibtex"] = m.group(2).strip()
    m = re.search(r"## Version note\s*\n(.*?)(?=\n## |\Z)", text, flags=re.S)
    if m:
        info["older"] = re.findall(r"\]\(\.\./([^/]+)/", m.group(1))
    info["withdrawn"] = text.startswith("# [Withdrawal notice")
    m = re.search(rf"Withdrawn on ({_DATE})", text)
    info["withdrawn_on"] = m.group(1) if m else ""
    m = re.search(r"## Archived manuscript\s*\n.*?\]\((https?://[^)]+)\)", text, flags=re.S)
    info["archived_pdf"] = m.group(1) if m else ""
    # Keep everything after the citation block (version notes, verification
    # instructions, withdrawal text) for display on the paper page.
    parts = re.split(r"^(?=## )", text, flags=re.M)
    body = "".join(part for part in parts[1:] if not part.startswith("## Citation"))
    if info["withdrawn"]:
        # The explanation of a withdrawal sits before the first heading.
        head = re.sub(r"\A# .*\n", "", parts[0])
        head = re.sub(r"\A\s*OpenAI\s*\n", "", head)
        body = "".join(part for part in parts[1:] if not part.startswith(("## Citation", "## Archived manuscript")))
        head = re.sub(r"\A\s*\*\*Withdrawn on .*\*\*\s*\n", "", head)
        body = head + body
    info["extra"] = body.strip()
    return info


def _date_from_slug(slug: str) -> str:
    m = re.search(rf"({_MONTHS})-(\d{{1,2}})-(\d{{4}})$", slug)
    return f"{m.group(1)} {m.group(2)}, {m.group(3)}" if m else ""


def load(root: Path):
    families_raw, papers = parse_contents(root)
    overview = parse_overview(root)

    disciplines: list[Discipline] = []
    families: dict[str, Family] = {}
    for name, nums in overview:
        disciplines.append(Discipline(name=name, families=nums))
        for num in nums:
            f = families_raw[num]
            families[num] = Family(num=num, title=f["title"], summary=f["summary"],
                                   discipline=name, papers=f["papers"])
            for slug in f["papers"]:
                papers[slug].discipline = name

    # Folders not listed in CONTENTS.md: superseded editions and withdrawals.
    for d in sorted((root / "preprints").iterdir()):
        if d.is_dir() and d.name not in papers:
            info = parse_readme(d / "README.md")
            papers[d.name] = Paper(slug=d.name, title=info.get("title", d.name),
                                   pdf=info.get("pdf"))

    for slug, p in papers.items():
        d = root / "preprints" / slug
        info = parse_readme(d / "README.md")
        if info.get("withdrawn"):
            p.status = "withdrawn"
            p.withdrawn_on = info.get("withdrawn_on", "")
            p.archived_pdf = info.get("archived_pdf", "")
            p.title = re.sub(r"^Withdrawal notice:\s*", "", info.get("title", p.title))
            p.pdf = None  # the folder holds no manuscript; README links the archive
        p.author = info.get("author", p.author)
        # A withdrawal notice's only date is the withdrawal date.
        p.date = (_date_from_slug(slug) if info.get("withdrawn") else info.get("date")) or _date_from_slug(slug)
        p.bibtex = info.get("bibtex", "")
        p.readme_extra = info.get("extra", "")
        if not info.get("withdrawn"):
            p.preamble = info.get("preamble", "")
        p.older = info.get("older", [])
        if (d / "build").is_dir():
            p.tex_dir = "build"
        # Community revisions so far mark the byline "OpenAI (with community
        # contributions)", in the README or at least in the TeX \author.
        p.community_revised = "community" in p.author.lower() or any(
            re.search(r"\\author\{[^}]*community", t.read_text(encoding="utf-8", errors="ignore"))
            for t in (d / "build").glob("*.tex"))
        for name, attr in (("NOTES.md", "notes_md"), ("AGENT_NOTES.md", "agent_notes_md")):
            if (d / name).is_file():
                setattr(p, attr, (d / name).read_text(encoding="utf-8"))
        if p.notes_md:
            p.contributions, p.contribution_problems = parse_contributions(p.notes_md)
        if p.pdf and not (d / p.pdf).is_file():
            p.pdf = None

    for slug, p in papers.items():
        for old in p.older:
            if old in papers:
                papers[old].newer = slug
                if papers[old].status == "current":
                    papers[old].status = "superseded"

    # Superseded editions inherit the family of their newest edition.
    for p in papers.values():
        if p.family is None:
            q = p
            while q.newer and q.family is None:
                q = papers[q.newer]
            if q.family:
                p.family, p.discipline = q.family, q.discipline

    checks = comparator_checks(root)
    for num, fam in families.items():
        if (root / "lean" / "docs" / f"{num}.md").is_file():
            fam.lean_doc = f"lean/docs/{num}.md"
            fam.lean_challenges = lean_challenges(root, fam.lean_doc, checks)

    for doc in sorted((root / "lean" / "docs").glob("*.md")):
        for slug in set(re.findall(r"\.\./\.\./preprints/([^/]+)/", doc.read_text(encoding="utf-8"))):
            if slug in papers:
                papers[slug].lean_notes.append(f"lean/docs/{doc.name}")

    return disciplines, families, papers


def git_blob(path: Path) -> str | None:
    """The git blob hash of a file (as `git hash-object` computes it), or None if it is missing."""
    try:
        data = path.read_bytes()
    except OSError:
        return None
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def comparator_checks(root: Path) -> dict[str, ComparatorCheck]:
    """The most recent comparator run under checks/comparator-<YYYY-MM-DD>/results.tsv, by challenge name."""
    runs = sorted((root / "checks").glob("comparator-*/results.tsv"))
    if not runs:
        return {}
    tsv = runs[-1]
    date = tsv.parent.name.removeprefix("comparator-")
    out = {}
    with tsv.open(encoding="utf-8") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            name = row["challenge"]
            base = root / "lean" / "ComparatorChallenges" / name
            # Unchanged only if the challenge, its configuration and every repository file the
            # challenge imports (path=blob;...) are byte-identical to the checked versions; a
            # missing file counts as changed, since it cannot be compared.
            imports = [dep.split("=", 1) for dep in row.get("imports", "").split(";") if dep]
            changed = (git_blob(base.with_suffix(".lean")) != row["challenge_blob"]
                       or git_blob(base.with_suffix(".json")) != row["config_blob"]
                       or any(git_blob(root / path) != blob for path, blob in imports))
            out[name] = ComparatorCheck(row["result"], date, f"{tsv.parent.relative_to(root).as_posix()}/{row['log']}",
                                        row["note"], changed)
    return out


def lean_challenges(root: Path, doc: str, checks: dict[str, ComparatorCheck] | None = None) -> list[LeanChallenge]:
    """Rows "| result | [X.lean](../ComparatorChallenges/X.lean) |" of a scope note, with the proof
    module that ComparatorChallenges/X.json names, as a file path (None if the .json is missing),
    and the latest comparator result for X, if any.
    A challenge in a folder (ComparatorChallenges/Dir/Challenge.lean) has its config in Dir/main.json.
    A line anchor on the link (X.lean#L84, several results in one file) is kept in the statement link."""
    out = []
    for label, name, anchor in re.findall(r"^\|\s*(.+?)\s*\|\s*\[[^\]]*\]\(\.\./ComparatorChallenges/([^)#]+?)\.lean(#L\d+)?\)",
                                  (root / doc).read_text(encoding="utf-8"), re.M):
        proof = None
        config = root / "lean" / "ComparatorChallenges" / f"{name}.json"
        if not config.exists() and "/" in name:
            config = config.parent / "main.json"
        try:
            module = json.loads(config.read_text())["solution_module"]
            proof = "lean/" + module.replace(".", "/") + ".lean"
        except (OSError, ValueError, KeyError) as e:
            print(f"warning: {doc}: no proof module for {name}: {e}", file=sys.stderr)
        out.append(LeanChallenge(label, f"lean/ComparatorChallenges/{name}.lean{anchor}", proof,
                                 (checks or {}).get(name)))
    return out


if __name__ == "__main__":
    import collections
    import sys

    disciplines, families, papers = load(Path(sys.argv[1] if len(sys.argv) > 1 else "."))
    print(len(disciplines), "disciplines,", len(families), "families,", len(papers), "folders")
    print(collections.Counter(p.status for p in papers.values()))
    print("no family:", [s for s, p in papers.items() if not p.family])
    print("no pdf:", [s for s, p in papers.items() if not p.pdf and p.status != "withdrawn"])
    print("no bibtex:", sum(1 for p in papers.values() if not p.bibtex))
    print("no date:", [s for s, p in papers.items() if not p.date][:5])
    print("with lean notes:", sum(1 for p in papers.values() if p.lean_notes))
