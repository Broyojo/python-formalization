<!-- title: Binding an uninitialized super object segfaults in supercheck -->
### Crash report

**Triage:** the record identifies this as a duplicate of gh-155376, with PR gh-155379 addressing the dereference. Keep this as a local draft for comparison with that report; it should not be filed as a new finding.

Calling `super.__new__` without `super.__init__` creates an object whose internal type is NULL. Its repr handles that state, but descriptor binding does not. Both explicit `__get__` and normal attribute access crash:

```python
import subprocess, sys
cases = ["super.__new__(super).__get__(1)",
         "class A:\n    s = super.__new__(super)\nA().s"]
codes = [subprocess.run([sys.executable, '-c', c], capture_output=True).returncode
         for c in cases]
print('return codes', codes)
```

Recorded on 3.15.2 and main: `return codes [-11, -11]` (SIGSEGV). Expected: an exception or an unbound result, with no interpreter crash.

Cause: Objects/typeobject.c:12891 checks whether the super object is already bound, but does not check `su->type`. It passes NULL to `supercheck` at :12902; the error path dereferences `type->tp_name` at :12868. Check for an uninitialized type before binding or calling `supercheck`.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [typeobj-super-uninitialized-get](https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-super-uninitialized-get.yaml)
