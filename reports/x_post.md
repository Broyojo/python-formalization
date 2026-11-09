# X thread (draft)

Post after the issues are filed and the page is live. Links only in post 6 (X shows posts with links to fewer people).
Images: post 1 reports/x_images/post1-map.mp4 (video), post 3 reports/x_images/post3-crash.png, post 4 reports/x_images/post4-proofs.png,
post 5 reports/x_images/post5-coverage.png. Regenerate with python3 site/x_map.py and python3 site/x_images.py.

---

**1/**  _(video: reports/x_images/post1-map.mp4)_
I had Opus 5.5 formalize CPython in Lean: 613,318 lines of Lean that copy Python's internals line by line, tested against the real interpreter and checked by Lean.

On the way it found real bugs in Python, including crashes from plain Python code. 🧵

**2/**
How it works: for each function in CPython 3.15.2, an agent writes a Lean model that mirrors the C or Python source. The model runs against python3 on 50,000+ generated inputs until they agree. Then it proves properties about it, and a second agent reviews every function.

**3/**  _(image: reports/x_images/post3-crash.png)_
One of the bugs: five lines of plain Python that segfault Python 3.15.

Instances of a class share one table of attribute names. dict.setdefault on an instance's __dict__ misses the case "this name exists, but not on this object", and dereferences a null pointer.

**4/**  _(image: reports/x_images/post4-proofs.png)_
The hard part wasn't the proofs. It was proofs that prove nothing: a theorem Lean accepts can still say nothing true about Python. Independent review threw out more than half of the early work, so only functions that pass review count: 4,071 so far.

**5/**  _(image: reports/x_images/post5-coverage.png)_
So far: 4,071 functions reviewed, 3,834 properties proved, 588 refuted, 418 bug reports with reproducers. We've started reporting them to CPython, beginning with six crashes, each reproduced on 3.15 and main.

**6/**
Write-up: https://broyojo.com/python-formalization/
Code, models and every bug record (Apache-2.0): https://github.com/Broyojo/python-formalization

Nothing here is specific to Python. The write-up says how to do this for your own language or library, and contributions are welcome: most of CPython is still to do.
