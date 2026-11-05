<!-- Draft for discuss.python.org, category: Core Development. Post from your own account.
     Fill in N_ISSUES and the issue links after filing. -->

**Title:** Formalizing CPython in Lean: N_ISSUES bug reports filed from a machine-checked model

Hi all,

Over the past week I've been building a model of CPython 3.15.2 in Lean 4, a proof assistant. AI agents (Claude Opus 5.5) did most of the work, and I directed it and reviewed the results. Each model copies a C or Python function line by line and is tested against the real interpreter on at least 50,000 generated inputs. Only then do we prove properties about it. A second agent reviews every function, and only functions that pass review count. So far that's 4,071 functions, with 3,834 proved properties and 588 refuted ones.

When a refuted property turns out to be CPython's fault rather than the model's, we write it up with a plain Python reproducer. Each one was checked on 3.15.2 and on main, and the tracker was searched for duplicates. Today I've filed N_ISSUES of them:

- CRASH_COUNT crashes or memory errors reachable from pure Python, each filed as its own issue (most involve a callback that mutates a container while C code holds a pointer into it);
- GROUP_COUNT grouped issues, one per module, for smaller inconsistencies: C and pure-Python versions disagreeing, wrong exception types, and documentation mismatches. Some of these may be intended, and I've said so where we weren't sure.

Duplicates of existing issues aren't refiled; the write-up links them instead.

Everything is public:
- Write-up: https://broyojo.com/python-formalization/
- Code, models and all bug records: https://github.com/Broyojo/python-formalization

I've tried to keep the reports short and verified, and I'm happy to change the format if another one works better for triage, such as one tracking issue, or fewer and larger grouped issues. I can also send PRs for the ones with small, obvious fixes if that would help.

Thanks, and thanks for CPython.

David
