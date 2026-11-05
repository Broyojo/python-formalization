# X thread (draft)

Post after the issues are filed and the page is live. Replace N_ISSUES with the count from
reports/filed.tsv. Attach docs/og.png to post 1 if the link card does not show it.

---

**1/**
I had AI agents (Claude Opus 5.5) formalize CPython in Lean: 613,318 lines of Lean that copy Python's internals line by line, tested against the real interpreter and checked by Lean.

On the way they found real bugs in Python, including crashes from plain Python code. 🧵

**2/**
How it works: for each function in CPython 3.15.2, an agent writes a Lean model that mirrors the C or Python source. The model runs against python3 on 50,000+ generated inputs until they agree. Then it proves properties about it, and a second agent reviews every function.

**3/**
One of the bugs. This segfaults Python 3.15:

class C: pass
a = C(); a.x = 1
b = C(); b.y = 2
class S(str): pass
b.__dict__.setdefault(S('x'), 5)

An instance dict shares its keys with the class, and setdefault misses the "key known, no value here" case.

**4/**
The hard part wasn't the proofs. It was proofs that prove nothing: a theorem Lean accepts can still say nothing true about Python. Independent review threw out more than half of the early work, so only functions that pass review count: 4,071 so far.

**5/**
So far: 4,071 functions reviewed, 3,834 properties proved, 588 refuted, 418 bug reports with reproducers. We've reported the crashes and the clearest findings to CPython: N_ISSUES issues, each reproduced on 3.15 and main.

**6/**
Write-up: https://broyojo.com/python-formalization/
Code, models and every bug record (Apache-2.0): https://github.com/Broyojo/python-formalization

Nothing here is specific to Python. The write-up says how to do this for your own language or library.
