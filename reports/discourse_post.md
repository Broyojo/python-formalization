<!-- Draft for discuss.python.org, category: Core Development. Post from your own account.
     Issue links filled in after filing on 2026-11-09. -->

**Title:** Formalizing CPython in Lean: findings from a machine-checked model, and how you'd like them

Hi all,

Since late October I've been building a model of CPython 3.15.2 in Lean 4, a proof assistant. AI agents did most of the work (Claude Opus 5.5, with GPT-6.1 Sol in Codex helping in the final review of the reports), and I directed it and reviewed the results. Each model copies a C or Python function line by line and is tested against the real interpreter on at least 50,000 generated inputs. Only then do we prove properties about it. A second agent reviews every function, and only functions that pass review count. So far that's 4,071 functions, with 3,834 proved properties and 588 refuted ones.

When a refuted property turns out to be CPython's fault rather than the model's, we write it up with a plain Python reproducer. That has produced 418 reports that reproduce on 3.15.2. Most are small: C and pure-Python versions that disagree, wrong exception types, edge cases. About 55 are crashes or memory errors reachable from Python code, usually a callback that changes an object while C code is still using it.

I know the tracker was flooded with automated reports in October, and I don't want to repeat that. So today I've filed only six crash reports, each of which I've read and checked myself, and each reproduced on 3.15.2 and main:

- [gh-161688](https://github.com/python/cpython/issues/161688): bytearray.strip() reads freed memory if the argument's __release_buffer__ resizes the bytearray
- [gh-161689](https://github.com/python/cpython/issues/161689): ElementTree slice assignment with start greater than stop duplicates a child without owning its second reference
- [gh-161690](https://github.com/python/cpython/issues/161690): dict.fromkeys() GC-tracks a non-GC object returned by a subclass constructor (3.15 regression)
- [gh-161691](https://github.com/python/cpython/issues/161691): memoryview: a view released by __buffer__ or __index__ in the middle of == or item assignment is still used
- [gh-161692](https://github.com/python/cpython/issues/161692): functools.partial: changing p.keywords during the call's keyword merge overflows a stack buffer (new in 3.15)
- [gh-161693](https://github.com/python/cpython/issues/161693): dict.setdefault() segfaults on an instance dict with an absent shared key passed as a str subclass

The rest are in the repository with reproducers, causes with line numbers, and a duplicate search; findings that duplicate existing issues link the existing issue instead of being refiled. How would you prefer to receive them, if at all: a few at a time, grouped by module for the relevant experts, or left in the repo for anyone to pick up? I can also send PRs for the ones with small, obvious fixes.

Everything is public:
- Write-up: https://broyojo.com/python-formalization/
- Code, models and all bug records: https://github.com/Broyojo/python-formalization

The project is open to contributors too: most of CPython is still unmodelled.

Thanks for reading, and for all your work on CPython.

David
