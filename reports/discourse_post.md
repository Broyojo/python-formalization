<!-- Draft for discuss.python.org, category: Core Development. Post from your own account.
     Fill in the six issue links after filing. -->

**Title:** Formalizing CPython in Lean: findings from a machine-checked model, and how you'd like them

Hi all,

Over the past two weeks I've been building a model of CPython 3.15.2 in Lean 4, a proof assistant. AI agents did most of the work (Claude Opus 5.5, with Codex helping in the final review of the reports), and I directed it and reviewed the results. Each model copies a C or Python function line by line and is tested against the real interpreter on at least 50,000 generated inputs. Only then do we prove properties about it. A second agent reviews every function, and only functions that pass review count. So far that's 4,071 functions, with 3,834 proved properties and 588 refuted ones.

When a refuted property turns out to be CPython's fault rather than the model's, we write it up with a plain Python reproducer. That has produced 418 reports that reproduce on 3.15.2. Most are small: C and pure-Python versions that disagree, wrong exception types, edge cases. About 55 are crashes or memory errors reachable from Python code, usually a callback that changes an object while C code is still using it.

I know the tracker was flooded with automated reports in October, and I don't want to repeat that. So today I've filed only six crash reports, each of which I've read and checked myself, and each reproduced on 3.15.2 and main:

- ISSUE_1
- ISSUE_2
- ISSUE_3
- ISSUE_4
- ISSUE_5
- ISSUE_6

The rest are in the repository with reproducers, causes with line numbers, and a duplicate search; findings that duplicate existing issues link the existing issue instead of being refiled. How would you prefer to receive them, if at all: a few at a time, grouped by module for the relevant experts, or left in the repo for anyone to pick up? I can also send PRs for the ones with small, obvious fixes.

Everything is public:
- Write-up: https://broyojo.com/python-formalization/
- Code, models and all bug records: https://github.com/Broyojo/python-formalization

The project is open to contributors too: most of CPython is still unmodelled.

Thanks, and thanks for CPython.

David
