"""File the approved drafts on python/cpython.

Reads reports/drafts/INDEX.md and files only lines ticked `- [x]`. Each filed issue is recorded in
reports/filed.tsv (draft, title, url), and a draft already listed there is never filed again.

  python3 reports/file_issues.py          dry run: list what would be filed
  python3 reports/file_issues.py --go     file them, using the gh CLI's logged-in account
"""

import argparse
import csv
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DRAFTS = ROOT / "reports" / "drafts"
FILED = ROOT / "reports" / "filed.tsv"
REPO = "python/cpython"


def approved():
    for line in (DRAFTS / "INDEX.md").read_text().splitlines():
        m = re.match(r"- \[[xX]\] .*?\]\(([^)]+\.md)\)", line)
        if m:
            yield m.group(1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--go", action="store_true", help="actually file the issues")
    ap.add_argument("--pause", type=float, default=20.0, help="seconds between issues")
    args = ap.parse_args()

    done = {}
    if FILED.exists():
        done = {r["draft"]: r["url"] for r in csv.DictReader(FILED.open(), delimiter="\t")}
    todo = [d for d in approved() if d not in done]
    print(f"{len(todo)} approved drafts to file ({len(done)} already filed)")
    if not FILED.exists():
        FILED.write_text("draft\ttitle\turl\n")
    for i, rel in enumerate(todo):
        text = (DRAFTS / rel).read_text()
        title = re.match(r"<!-- title: (.*?) -->\n", text).group(1)
        body = text.split("\n", 1)[1]
        if not args.go:
            print(f"  would file: {title}")
            continue
        out = subprocess.run(["gh", "issue", "create", "--repo", REPO, "--title", title, "--body", body],
                             capture_output=True, text=True)
        if out.returncode != 0:
            print(f"  FAILED {rel}: {out.stderr.strip()}")
            break
        url = out.stdout.strip().splitlines()[-1]
        with FILED.open("a") as f:
            f.write(f"{rel}\t{title}\t{url}\n")
        print(f"  filed {url}  {title}")
        if i + 1 < len(todo):
            time.sleep(args.pause)


if __name__ == "__main__":
    main()
