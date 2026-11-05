"""Turn bug records into draft CPython issues for human review.

Reads reports/triage.tsv (proposed_action per record) and bugs/*.yaml, and writes:
  reports/drafts/single/<id>.md         one issue per 'file-alone' record
  reports/drafts/group/<module>-<n>.md  grouped issues, at most GROUP_MAX findings each
  reports/drafts/INDEX.md               checklist: tick a box to approve that draft for filing
Nothing here talks to GitHub; reports/file_issues.py files the ticked drafts.
Run: python3 reports/make_drafts.py
"""

import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DRAFTS = ROOT / "reports" / "drafts"
PAGE = "https://broyojo.com/python-formalization/"
REPO = "https://github.com/Broyojo/python-formalization"
GROUP_MAX = 8
GROUP_PRIORITIES = {"P3"}  # P4/P5 stay in bugs/ and are offered in the Discourse post, not filed

# Short titles for single issues, in CPython's usual style.
TITLES = {
    "bytecode-eg-match-split-items-unchecked": "except* trusts the items returned by an overridden split()",
    "bytecode-flineno-iter-index-as-object": "Setting f_lineno to jump out of a for loop crashes",
    "bytecode-flineno-null-on-stack": "Setting f_lineno to jump into a with block leaves NULL on the stack",
    "bytecode-flineno-stack-swap-truncation": "Setting f_lineno into deeply nested blocks corrupts the stack",
    "bytecode-gen-close-deep-chain-stack-overflow": "Closing a deep yield-from chain overflows the C stack",
    "bytecode-kwonly-defaults-borrowed-dict": "Use-after-free when __eq__ replaces f.__kwdefaults__ during a call",
    "bytesobj-bytearray-init-iterator-ignores-start": "bytearray.__init__ from an iterator can write past the buffer",
    "bytesobj-bytearray-strip-release-uaf": "Use-after-free in bytearray.strip() when __release_buffer__ mutates self",
    "bytesobj-memoryview-eq-released-by-buffer": "memoryview == reads freed memory when __buffer__ releases the view",
    "bytesobj-memoryview-setitem-c-released": "memoryview item assignment writes through a view released by __index__",
    "corelibs-inplace-mul-heap-left": "x *= [1] raises TypeError where x * [1] works for __index__ objects",
    "corelibs-lru-evicted-hit-gc-hang": "lru_cache: a raising __eq__ during eviction makes gc.collect() hang",
    "corelibs-partial-setstate-phcount": "functools.partial.__setstate__ with a tuple subclass reads out of bounds",
    "corelibs-partial-vectorcall-stale-kw-count": "Calling functools.partial writes out of bounds when a key's __eq__ re-enters",
    "datetime-pep495-delta-cmp-none": "datetime == crashes when utcoffset() is None for one fold only",
    "datetime-subclass-arith-result-type-confusion": "datetime.astimezone() crashes when a subclass __new__ returns a non-datetime",
    "datetime-zoneinfo-clear-cache-reentrant-free": "ZoneInfo.clear_cache() can free cache nodes that are still in use",
    "dictset-fromkeys-frozendict-rewritten": "frozendict.fromkeys() on a subclass can mutate a frozendict in place",
    "dictset-fromkeys-gc-track-non-gc": "dict.fromkeys() on a subclass GC-tracks a non-GC object",
    "dictset-setdefault-split-null": "dict.setdefault() segfaults on an instance __dict__ with a str-subclass key",
    "operator-methodcaller-reduce-shares-kwargs": "operator.methodcaller.__reduce__ exposes its private kwargs dict",
    "pygrammar-check-none-in-list-segfault": "compile() segfaults on an AST with None in a list field",
    "pyio-buffered-reentrant-detach-crash": "BufferedReader.read() crashes if raw.closed detaches the buffer",
    "pyio-buffered-reentrant-init-free": "BufferedReader.__init__ re-entered from the raw stream frees the buffer in use",
    "pyio-buffered-reentrant-init-size0": "A failed re-entrant BufferedReader.__init__ leaves buffer_size 0",
    "sequences-array-e-ins1-overflow-keeps-slot": "array('e').append(65536.0) raises but keeps an uninitialised item",
    "sequences-array-fromlist-restore-stale": "array.fromlist() exposes stale memory when __index__ clears the array",
    "sequences-array-ins1-stale-size": "array.append() exposes stale memory when __index__ clears the array",
    "textlibs-email-msgid-no-fold-literal-space": "email: Message-ID '<a@[ x]>' raises UnboundLocalError",
    "textlibs-etree-slice-backward-dup": "ElementTree slice assignment with start > stop corrupts the children",
    "textlibs-struct-reinit-memory-safety": "Calling Struct.__init__ on a live Struct accesses freed memory",
    "typeobj-exc-getstate-borrowed-dict": "AttributeError.__reduce__ uses a __dict__ that __eq__ can free",
    "typeobj-set-class-reentrant-slot-eq": "__class__ assignment can free the old class while it is in use",
    "typeobj-set-mro-error-borrowed-mro": "The MRO conflict error message can read freed memory",
    "typeobj-structseq-mutable-size-attrs": "Struct sequences trust size attributes that Python code can rebind",
    "typeobj-super-uninitialized-get": "super.__new__(super).__get__(1) segfaults",
}

MODULE_NAMES = {"corelibs": "functools, enum, random and other core library modules", "textlibs": "text and binary codecs",
                "datetime": "datetime", "bytesobj": "bytes, bytearray and memoryview", "pyio": "io and _pyio",
                "typeobj": "type objects", "pygrammar": "the parser and grammar", "pickle": "pickle",
                "decimal": "decimal", "accel": "C accelerator modules", "sequences": "array and collections",
                "json": "json", "bytecode": "the bytecode interpreter", "binary64": "float and complex",
                "calstat": "calendar and statistics", "ipaddress": "ipaddress", "itertools": "itertools",
                "longobj": "int", "mathint": "math", "fractions": "fractions", "unicodeobj": "str",
                "dictset": "dict and set", "getargs": "argument parsing", "rangeslice": "range and slice"}


def field(t, k):
    m = re.search(rf"^{k}:\s*\|\s*\n((?:[ ]{{2}}.*\n|[ ]*\n)+)", t, re.M)
    if m:
        lines = m.group(1).splitlines()
        return "\n".join(l[2:] if l.startswith("  ") else l for l in lines).strip()
    m = re.search(rf"^{k}:\s*(.+)$", t, re.M)
    return m.group(1).strip().strip('"') if m else ""


def inner_code(repro):
    """The script inside a subprocess wrapper (code = r'''...'''), without REPRODUCED checks."""
    m = re.search(r'code\s*=\s*r?("""|\'\'\')\n(.*?)\1', repro, re.S)
    code = m.group(2) if m else repro
    keep = [l for l in code.splitlines() if "REPRODUCED" not in l
            and not re.match(r"\s*import resource", l) and "RLIMIT_CORE" not in l]
    while keep and re.match(r"\s*if .*:\s*$", keep[-1]):
        keep.pop()
    return "\n".join(keep).strip()


def clean(s):
    s = " ".join(s.split())
    s = re.sub(r"\s*REPRODUCED( by check_bugs\.py)?\.?", "", s)
    s = re.sub(r"@3\.14\.7:", ":", s)  # flagged in INDEX; citations to re-check
    return s.strip()


def first_para(s):
    return s.split("\n\n")[0].strip()


FOOTER = ("Found while building a Lean 4 model of CPython ({page}). The report was drafted with AI "
          "assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.")


def single(bid, t):
    title = TITLES.get(bid) or field(t, "title")
    body = ["# Bug report", "", "### Bug description", "", clean(first_para(field(t, "summary"))), "",
            "```python", inner_code(field(t, "reproducer")), "```", "",
            "**Expected:** " + clean(field(t, "expected")), "",
            "**Actual:** " + clean(first_para(field(t, "observed"))), ""]
    if field(t, "cause"):
        body += ["**Cause:** " + clean(field(t, "cause")), ""]
    if field(t, "possible_fix"):
        body += ["**Possible fix:** " + clean(field(t, "possible_fix")), ""]
    body += ["### CPython versions tested on", "", "3.15, CPython main branch", "",
             "### Operating systems tested on", "", "Linux", "", "---", FOOTER.format(page=PAGE),
             f"Record: {REPO}/blob/main/bugs/{bid}.yaml"]
    return title, "\n".join(body) + "\n"


def group(mod, items, part, parts):
    name = MODULE_NAMES.get(mod, mod)
    suffix = f" (part {part} of {parts})" if parts > 1 else ""
    title = f"Small inconsistencies in {name} found by a formal model{suffix}"
    body = ["# Bug report", "", "### Bug description", "",
            f"While modelling CPython 3.15.2 in Lean 4 ({PAGE}), we found the cases below, where the "
            "implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with "
            "its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on "
            "3.15.2 and on main. They are grouped here so they can be triaged together; we're happy to split "
            "out any that deserve their own issue.", ""]
    for i, (bid, t) in enumerate(items, 1):
        mi = field(t, "maybe_intended")
        note = f"\n\n*May be intended:* {clean(first_para(mi))}" if re.match(r"(?i)(likely|probably|yes|possibly)", mi) else ""
        body += [f"#### {i}. {clean(field(t, 'title'))}", "", clean(first_para(field(t, "summary"))) + note, "",
                 "<details><summary>Reproducer</summary>", "", "```python", inner_code(field(t, "reproducer")),
                 "```", "", "</details>", ""]
    body += ["### CPython versions tested on", "", "3.15, CPython main branch", "",
             "### Operating systems tested on", "", "Linux", "", "---",
             "Drafted with AI assistance (Claude); each case was reproduced on 3.15.2 and on main and the report "
             f"reviewed before filing. Records: {REPO}/tree/main/bugs"]
    return title, "\n".join(body) + "\n"


def main():
    rows = list(csv.DictReader(open(ROOT / "reports/triage.tsv"), delimiter="\t"))
    for d in ("single", "group"):
        (DRAFTS / d).mkdir(parents=True, exist_ok=True)
        for old in (DRAFTS / d).glob("*.md"):
            old.unlink()
    index = ["# Draft issues for python/cpython", "",
             "Change `[ ]` to `[x]` for each draft you have read and can explain in your own words "
             "(CPython's AI-tools policy requires it). `python3 reports/file_issues.py` files only ticked drafts "
             "and does nothing without `--go`.", "", "## Single issues (crashes and memory errors)", ""]
    groups, stale, minor = {}, [], []
    for r in rows:
        t = (ROOT / "bugs" / f"{r['id']}.yaml").read_text()
        a = r["proposed_action"]
        if a == "file-alone":
            title, body = single(r["id"], t)
            (DRAFTS / "single" / f"{r['id']}.md").write_text(f"<!-- title: {title} -->\n" + body)
            flag = " *(re-check a 3.14.7 citation)*" if "@3.14.7:" in t else ""
            index.append(f"- [ ] {r['priority']} [{title}](single/{r['id']}.md){flag}")
        elif a.startswith("group:") and r["priority"] in GROUP_PRIORITIES:
            groups.setdefault(r["module"], []).append((r["id"], t))
        elif a.startswith("group:") or a == "ask-in-group":
            minor.append(r["id"])
        elif a == "check-main":
            stale.append(r["id"])
    index += ["", f"## Grouped issues (at most {GROUP_MAX} findings each)", ""]
    for mod, items in sorted(groups.items(), key=lambda x: -len(x[1])):
        chunks = [items[i:i + GROUP_MAX] for i in range(0, len(items), GROUP_MAX)]
        for n, chunk in enumerate(chunks, 1):
            title, body = group(mod, chunk, n, len(chunks))
            name = f"{mod}-{n}.md"
            (DRAFTS / "group" / name).write_text(f"<!-- title: {title} -->\n" + body)
            index.append(f"- [ ] [{title}](group/{name})")
    index += ["", f"## Waiting on a re-run on main ({len(stale)})", "",
              "These are filed only after scripts/check_bugs.py confirms them on main: " + ", ".join(stale) + ".", "",
              f"## Not filed at launch ({len(minor)} minor or possibly intended findings)", "",
              "P4/P5 findings, and ones whose record says they are probably intended, stay in bugs/ and are offered "
              "in the Discourse post. Duplicates of existing issues and 3.14-only behaviour are not filed either; "
              "see reports/triage.tsv."]
    (DRAFTS / "INDEX.md").write_text("\n".join(index) + "\n")
    ng = sum(1 for _ in (DRAFTS / "group").glob("*.md"))
    print(f"{sum(r['proposed_action'] == 'file-alone' for r in rows)} single drafts, {ng} grouped drafts, "
          f"{len(stale)} waiting on main, {len(minor)} minor not filed")


if __name__ == "__main__":
    main()
