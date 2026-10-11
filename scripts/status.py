#!/usr/bin/env python3
"""The status of the textbook's statements in Lean.

Reads
  textbook/manifest.toml  hand-edited: one [[statement]] and one [[definition]]
                          per item of the book, keyed by its label
  the inventory           named by textbook/edition.toml: the book's items as
                          printed, each with a hash (absent until Phase 3)
  build/report.json       written by `lake env lean --run scripts/Report.lean`

and computes the status of each statement:
  planned    no Lean statement carries its label
  stated     a Lean statement does, but it awaits review, has changed since
             review, or has no proof that proves exactly it with the three
             permitted axioms
  proved     reviewed, unchanged since review, and so proved
  partial    as proved, for a narrower statement (set by hand, with fidelity;
             stated until it is reviewed)
  informal   not formalized by design (set by hand, with fidelity)
and of each definition: planned, defined (a declaration carries its label),
mathlib or informal (both set by hand).

Usage, from the repository root:
  python3 scripts/status.py --write           write STATUS.md, the README's
                                              status block, and the statuses
                                              and Lean names in the manifest
  python3 scripts/status.py --check           fail if anything is stale or wrong
  python3 scripts/status.py --tex PATH        write only the guide's statement
                                              table, with the counts as macros
  python3 scripts/status.py --approve KEY...  record the judge's approval of the
                                              statements KEY
Options: --report PATH (default build/report.json); --tex PATH, which also
writes the guide's statement table; --date YYYY-MM-DD, for --approve.

The script edits only one-line fields of the manifest: status, lean_statement,
lean_proof, lean, book_sha256, reviewed, review_text_sha256 and
review_term_sha256, review_context_sha256 and review_return (cleared on approval).
"""
import argparse
import datetime
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEXTBOOK = ROOT / "textbook"
MANIFEST = TEXTBOOK / "manifest.toml"
EDITION = TEXTBOOK / "edition.toml"
STATUS_MD = TEXTBOOK / "STATUS.md"
README = ROOT / "README.md"
REVIEW_LOG = TEXTBOOK / "review" / "review-log.md"
STATUS_JSON = ROOT / "build" / "status.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATEMENT_STATUSES = ("proved", "partial", "stated", "planned", "informal")
DEFINITION_STATUSES = ("defined", "mathlib", "planned", "informal")
BEGIN, END = "<!-- status:begin -->", "<!-- status:end -->"
EMPTY = "No statement is recorded yet."


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def text_hash(statement):
    """The hash of what the reviewer reads: the statement and its definitions."""
    return sha("\n\n".join([statement["text"], *statement["surface"]]))


def term_hash(statement):
    """The hash of the exact Lean terms of the same declarations."""
    return sha("\n\n".join(statement["terms"]))


def context_hash(entry, definitions, inventory):
    """Bind approval to the book and the declared scope of its translation.

    Lean dependencies alone cannot detect a changed book definition or a new
    fidelity qualification. Conservatively include every inventoried book
    item and every definition's fidelity note; the inventory does not record
    which book definitions a statement uses. Ignore locations and numbering.
    """
    context = {
        "book": {key: {field: item.get(field, "")
                       for field in ("kind", "title", "statement")}
                 for key, item in (inventory or {}).items()},
        "definitions": {e["key"]: {field: e.get(field, "")
                                  for field in ("fidelity", "planned_home")}
                        for e in definitions},
        "fidelity": entry.get("fidelity", ""),
        "partial": entry.get("status") == "partial",
    }
    return sha(json.dumps(context, sort_keys=True, ensure_ascii=False))


def slug(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def item_key(item):
    """The manifest key of an inventory item: its label, or a stand-in."""
    if item.get("key"):
        return item["key"]
    if item["label"]:
        return item["label"]
    return "nolabel:%s:%s" % (Path(item["file"]).stem, slug(item["title"]))


def plain(tex):
    """A title in LaTeX, as plain text for a Markdown table."""
    s = tex.replace("---", "—").replace("--", "–").replace("\\times", "×")
    s = re.sub(r"\\[a-zA-Z]+", "", s)
    return s.replace("$", "").replace("{", "").replace("}", "").replace("|", "\\|")


def toml_value(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, list):
        return "[" + ", ".join(json.dumps(x, ensure_ascii=False) for x in v) + "]"
    return json.dumps(v, ensure_ascii=False)


def set_fields(text, table, key, fields):
    """Set one-line fields of the [[table]] entry whose key is `key`."""
    lines = text.split("\n")
    keyline = re.compile(r"key\s*=\s*" + re.escape(json.dumps(key, ensure_ascii=False)) + r"\s*$")
    start = end = None
    i = 0
    while i < len(lines):
        if lines[i].strip() == f"[[{table}]]":
            j = i + 1
            while j < len(lines) and not lines[j].startswith("[["):
                j += 1
            if any(keyline.match(line) for line in lines[i:j]):
                start, end = i, j
                break
            i = j
        else:
            i += 1
    if start is None:
        raise KeyError(f"no [[{table}]] entry with key {key}")
    for field, value in fields.items():
        new = f"{field} = {toml_value(value)}"
        for k in range(start + 1, end):
            if re.match(rf"{re.escape(field)}\s*=", lines[k]):
                lines[k] = new
                break
        else:
            k = end
            while k > start + 1 and not lines[k - 1].strip():
                k -= 1
            lines.insert(k, new)
            end += 1
    return "\n".join(lines)


def load_manifest():
    if not MANIFEST.exists():
        return "", [], []
    text = MANIFEST.read_text(encoding="utf-8")
    data = tomllib.loads(text)
    return text, data.get("statement", []), data.get("definition", [])


def load_inventory():
    if not EDITION.exists():
        return None, None
    edition = tomllib.loads(EDITION.read_text(encoding="utf-8"))
    items = json.loads((TEXTBOOK / edition["inventory"]).read_text(encoding="utf-8"))
    return edition, {item_key(i): i for i in items}


def load_report(path):
    if not path.exists():
        sys.exit(f"{path} is missing; first run:\n"
                 f"  mkdir -p build && lake env lean --run scripts/Report.lean > build/report.json")
    statements, proofs, definitions, problems = {}, {}, {}, []
    for row in json.loads(path.read_text(encoding="utf-8")):
        label = row["label"]
        if row["kind"] == "statement":
            if label in statements:
                problems.append(f"two Lean statements carry {label}: "
                                f"{statements[label]['decl']} and {row['decl']}")
            statements[label] = row
        elif row["kind"] == "proof":
            proofs.setdefault(label, []).append(row)
        else:
            definitions.setdefault(label, []).append(row)
    return statements, proofs, definitions, problems


def evaluate(st_entries, def_entries, inventory, report):
    """Statuses, problems (which --write cannot repair) and manifest updates."""
    lean_st, proofs, lean_def, problems = report
    problems = list(problems)
    updates = []                      # (table, key, {field: value})
    keys = [e["key"] for e in st_entries + def_entries]
    for k in sorted({k for k in keys if keys.count(k) > 1}):
        problems.append(f"the manifest has {k} twice")
    known_st = {e["key"] for e in st_entries}
    known_def = {e["key"] for e in def_entries}

    for label, row in sorted(lean_st.items()):
        if label not in known_st:
            problems.append(f"{row['decl']} carries {label}, which is not a [[statement]] of the manifest")
    for label, rows in sorted(proofs.items()):
        target = lean_st.get(label)
        for row in rows:
            bad = sorted(set(row["axioms"]) - ALLOWED_AXIOMS)
            if bad:
                problems.append(f"{row['decl']} uses the axioms {', '.join(bad)}")
            if target is None:
                problems.append(f"the proof {row['decl']} carries {label}, but no Lean statement does")
            elif row["proves"] != target["decl"]:
                problems.append(f"the proof {row['decl']} carries {label} but proves "
                                f"{row['proves'] or 'something that is not a statement'}, "
                                f"not {target['decl']}")
    for label, rows in sorted(lean_def.items()):
        if label not in known_def:
            problems.append(f"{rows[0]['decl']} carries {label}, which is not a [[definition]] of the manifest")

    if inventory is not None:
        inv_st = {k for k, i in inventory.items() if i["kind"] != "definition"}
        inv_def = {k for k, i in inventory.items() if i["kind"] == "definition"}
        for k in sorted(inv_st - known_st):
            problems.append(f"the book's statement {k} has no [[statement]] entry")
        for k in sorted(known_st - inv_st):
            problems.append(f"[[statement]] {k} is not a statement of the book's inventory")
        for k in sorted(inv_def - known_def):
            problems.append(f"the book's definition {k} has no [[definition]] entry")
        for k in sorted(known_def - inv_def):
            problems.append(f"[[definition]] {k} is not a definition of the book's inventory")

    results = []
    for e in st_entries:
        key = e["key"]
        recorded = e.get("status", "planned")
        if recorded not in STATEMENT_STATUSES:
            problems.append(f"{key}: unknown status {recorded!r}")
        if recorded in ("partial", "informal") and not e.get("fidelity", "").strip():
            problems.append(f"{key}: the status {recorded} needs a fidelity note")
        book = inventory.get(key) if inventory else None
        st = lean_st.get(key)
        good = [p for p in proofs.get(key, [])
                if st and p["proves"] == st["decl"] and not set(p["axioms"]) - ALLOWED_AXIOMS]
        notes = ["returned: " + e["review_return"]] if e.get("review_return") else []
        if recorded == "informal":
            status = "informal"
        elif st is None:
            status = "planned"
        else:
            ok = not e.get("review_return")
            if not e.get("reviewed"):
                ok = False
                if not e.get("review_return"):
                    notes.append("awaits review")
            else:
                if (e.get("review_text_sha256") != text_hash(st)
                        or e.get("review_term_sha256") != term_hash(st)):
                    ok = False
                    notes.append("changed since review")
                if book and e.get("book_sha256") != book["statement_sha256"]:
                    ok = False
                    notes.append("the book's text changed since review")
                if e.get("review_context_sha256") != context_hash(e, def_entries, inventory):
                    ok = False
                    notes.append("the book or fidelity context changed since review")
            if not good:
                ok = False
                notes.append("no proof yet" if not proofs.get(key) else "no valid proof")
            status = ("partial" if recorded == "partial" else "proved") if ok else "stated"
            if recorded == "partial" and not ok:
                # A statement decided to be partial may be recorded so before
                # its review; until the review it counts as stated.
                if notes != ["awaits review"]:
                    problems.append(f"{key}: recorded as partial, but {'; '.join(notes)}")
                status = "stated"
        fields = {}
        if recorded not in ("partial", "informal") and recorded != status:
            fields["status"] = status
        statement_decl = st["decl"] if st else ""
        proof_decl = good[0]["decl"] if good else ""
        if e.get("lean_statement", "") != statement_decl:
            fields["lean_statement"] = statement_decl
        if e.get("lean_proof", "") != proof_decl:
            fields["lean_proof"] = proof_decl
        if book and not e.get("reviewed") and e.get("book_sha256") != book["statement_sha256"]:
            fields["book_sha256"] = book["statement_sha256"]
        if fields:
            updates.append(("statement", key, fields))
        results.append({
            "key": key, "number": e.get("number", ""), "title": e.get("title", ""),
            "optional": e.get("optional", False), "tier": e.get("tier", ""),
            "batch": e.get("batch", ""), "status": status,
            "statement": statement_decl, "proof": proof_decl, "notes": notes,
        })

    def_results = []
    for e in def_entries:
        key = e["key"]
        recorded = e.get("status", "planned")
        if recorded not in DEFINITION_STATUSES:
            problems.append(f"{key}: unknown status {recorded!r}")
        if recorded == "informal" and not e.get("fidelity", "").strip():
            problems.append(f"{key}: the status informal needs a fidelity note")
        if recorded == "mathlib" and not e.get("planned_home", "").strip():
            problems.append(f"{key}: the status mathlib needs planned_home to name the Mathlib notion")
        names = sorted(r["decl"] for r in lean_def.get(key, []))
        if recorded in ("mathlib", "informal"):
            status = recorded
        else:
            status = "defined" if names else "planned"
        fields = {}
        if recorded != status:
            fields["status"] = status
        if e.get("lean", []) != names:
            fields["lean"] = names
        if fields:
            updates.append(("definition", key, fields))
        def_results.append({
            "key": key, "number": e.get("number", ""), "title": e.get("title", ""),
            "status": status, "lean": names, "home": e.get("planned_home", ""),
        })
    return results, def_results, problems, updates


def ordinal(n):
    n = int(n)
    if 10 <= n % 100 <= 13:
        return f"{n}th"
    return f"{n}" + {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")


def counts(results):
    rows = ["| Status | Statements |", "|---|---|"]
    for s in STATEMENT_STATUSES:
        rows.append(f"| {s} | {sum(r['status'] == s for r in results)} |")
    rows.append(f"| **total** | **{len(results)}** |")
    return rows


def render_status(edition, results, def_results):
    out = ["# Status of the textbook's statements", "",
           "*Generated by `scripts/status.py` from `manifest.toml` and the Lean "
           "report; do not edit by hand.*"]
    if edition:
        out += ["", f"Book edition followed: the {ordinal(edition['number'])}, "
                    f"`{edition['name']}` ({edition['pages']} pages)."]
    out.append("")
    if not results and not def_results:
        return "\n".join(out + [EMPTY]) + "\n"
    out += counts(results)
    out += ["", "## Statements", "",
            "| No. | Title | Label | Tier | Batch | Status | Lean | Notes |",
            "|---|---|---|---|---|---|---|---|"]
    for r in results:
        lean = " / ".join(f"`{x}`" for x in (r["statement"], r["proof"]) if x)
        title = plain(r["title"]) + (" ◊" if r["optional"] else "")
        out.append(f"| {r['number']} | {title} | `{r['key']}` | {r['tier']} | {r['batch']} "
                   f"| {r['status']} | {lean} | {'; '.join(r['notes'])} |")
    if def_results:
        out += ["", "## Definitions", "",
                "| No. | Definition | Label | Status | Lean |", "|---|---|---|---|---|"]
        for r in def_results:
            lean = ", ".join(f"`{x}`" for x in r["lean"])
            if r["status"] == "mathlib":
                lean = plain(r["home"])
            out.append(f"| {r['number']} | {plain(r['title'])} | `{r['key']}` "
                       f"| {r['status']} | {lean} |")
    return "\n".join(out) + "\n"


def render_readme(results):
    text = README.read_text(encoding="utf-8")
    if BEGIN not in text or END not in text:
        return text, f"README.md lacks the markers {BEGIN} and {END}"
    head, rest = text.split(BEGIN, 1)
    _, tail = rest.split(END, 1)
    body = EMPTY if not results else "\n".join(counts(results))
    return f"{head}{BEGIN}\n{body}\n{END}{tail}", None


def tex_escape(s):
    return s.replace("\\", "\\textbackslash{}").replace("_", "\\_").replace("&", "\\&") \
            .replace("#", "\\#").replace("%", "\\%")


def render_tex(results):
    """The guide's statement table (xltabular and booktabs, as the guide loads),
    kept in the macro \\statustable, after the counts of each status as macros
    (\\statustotal, and statuscount@proved and so on), so that the guide can
    read the file in its preamble."""
    counts = {s: sum(r["status"] == s for r in results) for s in STATEMENT_STATUSES}
    out = ["% Generated by scripts/status.py; do not edit by hand.",
           "\\def\\statustotal{%d}" % len(results)]
    out += ["\\expandafter\\def\\csname statuscount@%s\\endcsname{%d}" % kv
            for kv in counts.items()]
    out += ["\\def\\statustable{%",
            "\\begin{xltabular}{\\linewidth}{@{}l>{\\raggedright\\arraybackslash}X"
            ">{\\raggedright\\arraybackslash}p{.4\\linewidth}l@{}}", "\\toprule",
           "No. & Statement & Lean & Status\\\\", "\\midrule", "\\endhead"]
    for r in results:
        name = (r["proof"] or r["statement"]).removeprefix("Artform.")
        name = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak ", tex_escape(name))
        name = name.replace(".", ".\\allowbreak ")
        lean = f"\\texttt{{\\footnotesize {name}}}" if name else "---"
        out.append(f"{r['number']} & {r['title']} & {lean} & {r['status']}\\\\")
    out += ["\\bottomrule", "\\end{xltabular}}"]
    return "\n".join(out) + "\n"


def approve(keys, date, report, inventory):
    text = MANIFEST.read_text(encoding="utf-8")
    manifest = tomllib.loads(text)
    entries = {e["key"]: e for e in manifest.get("statement", [])}
    definitions = manifest.get("definition", [])
    lean_st = report[0]
    log = []
    for key in keys:
        st = lean_st.get(key)
        if st is None:
            sys.exit(f"{key}: no Lean statement carries this label")
        fields = {"reviewed": date, "review_text_sha256": text_hash(st),
                  "review_term_sha256": term_hash(st),
                  "review_context_sha256": context_hash(entries[key], definitions, inventory)}
        if entries[key].get("review_return"):
            fields["review_return"] = ""
        if inventory and key in inventory:
            fields["book_sha256"] = inventory[key]["statement_sha256"]
        text = set_fields(text, "statement", key, fields)
        log.append(f"- {date}: `{key}` approved as `{st['decl']}` "
                   f"(text {fields['review_text_sha256'][:12]}, "
                   f"term {fields['review_term_sha256'][:12]}, "
                   f"context {fields['review_context_sha256'][:12]})")
    candidate = tomllib.loads(text)
    problems = evaluate(candidate.get("statement", []), candidate.get("definition", []),
                        inventory, report)[2]
    if problems:
        sys.exit("approval not recorded:\n" + "\n".join(problems))
    MANIFEST.write_text(text, encoding="utf-8")
    REVIEW_LOG.parent.mkdir(parents=True, exist_ok=True)
    old = REVIEW_LOG.read_text(encoding="utf-8") if REVIEW_LOG.exists() else (
        "# Review log\n\nOne line per approval, written by `scripts/status.py --approve`.\n\n")
    REVIEW_LOG.write_text(old + "\n".join(log) + "\n", encoding="utf-8")
    print(f"approved: {', '.join(keys)}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--approve", nargs="+", metavar="KEY")
    ap.add_argument("--report", type=Path, default=ROOT / "build" / "report.json")
    ap.add_argument("--tex", type=Path)
    ap.add_argument("--date", default=datetime.date.today().isoformat())
    args = ap.parse_args()
    if not (args.write or args.check or args.approve or args.tex):
        ap.error("one of --write, --check, --approve or --tex is required")

    report = load_report(args.report)
    edition, inventory = load_inventory()
    if args.approve:
        approve(args.approve, args.date, report, inventory)
    text, st_entries, def_entries = load_manifest()
    results, def_results, problems, updates = evaluate(st_entries, def_entries, inventory, report)

    new_text = text
    for table, key, fields in updates:
        new_text = set_fields(new_text, table, key, fields)
    if new_text != text:
        tomllib.loads(new_text)
    outputs = {STATUS_MD: render_status(edition, results, def_results)}
    readme, err = render_readme(results)
    if err:
        problems.append(err)
    else:
        outputs[README] = readme
    if args.tex:
        outputs[args.tex] = render_tex(results)

    tally = ", ".join(f"{sum(r['status'] == s for r in results)} {s}" for s in STATEMENT_STATUSES)
    summary = f"{len(results)} statements ({tally}); {len(def_results)} definitions"
    if args.check:
        stale = [p for p, content in outputs.items()
                 if not p.exists() or p.read_text(encoding="utf-8") != content]
        if new_text != text:
            stale.append(MANIFEST)
        for p in stale:
            print(f"stale: {p.relative_to(ROOT)} (run scripts/status.py --write)")
        for p in problems:
            print(f"problem: {p}")
        print(summary)
        return 1 if stale or problems else 0

    if not (args.write or args.approve):
        # --tex alone writes the guide's table and nothing else.
        if problems:
            for p in problems:
                print(f"problem: {p}")
            return 1
        args.tex.parent.mkdir(parents=True, exist_ok=True)
        args.tex.write_text(outputs[args.tex], encoding="utf-8")
        print(summary)
        return 0
    for p, content in outputs.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    if new_text != text:
        MANIFEST.write_text(new_text, encoding="utf-8")
    STATUS_JSON.parent.mkdir(parents=True, exist_ok=True)
    STATUS_JSON.write_text(json.dumps({
        "edition": edition, "statements": results, "definitions": def_results,
        "problems": problems}, indent=1, ensure_ascii=False, default=str) + "\n",
        encoding="utf-8")
    for p in problems:
        print(f"problem: {p}")
    print(summary)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
