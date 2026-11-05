<!-- title: Writable struct-sequence size attributes cause out-of-bounds access in copy.replace, __reduce__ and construction -->
### Crash report

Heap struct-sequence types such as `os.terminal_size` and `os.stat_result` expose writable size attributes. C code trusts them for allocation and indexing while also using bounds derived from an existing object's layout. The three independent subprocesses below exercise replacement, reduction and a constructor whose iterable changes the sizes during iteration. None supplies a dict argument to the constructor.

```python
import subprocess, sys
CASES = {
    "copy.replace after n_fields = n_sequence_fields = 0": (
        "import os, copy\n"
        "T = os.terminal_size\n"
        "T.n_fields = T.n_sequence_fields = 100000\n"
        "t = T(range(100000))\n"
        "T.n_fields = T.n_sequence_fields = 0\n"
        "copy.replace(t)\n"
        "print('no crash')\n"),
    "__reduce__ after n_unnamed_fields = 10**6": (
        "import os\n"
        "s = os.stat_result(range(19))\n"
        "os.stat_result.n_unnamed_fields = 10**6\n"
        "s.__reduce__()\n"
        "print('no crash')\n"),
    "constructor whose argument rebinds n_fields while it is iterated": (
        "import os\n"
        "T = os.terminal_size\n"
        "class It:\n"
        "    def __iter__(self):\n"
        "        T.n_fields = T.n_sequence_fields = 0\n"
        "        return iter(range(100000))\n"
        "T.n_fields = T.n_sequence_fields = 100000\n"
        "T(It())\n"
        "print('no crash')\n"),
}
for name, code in CASES.items():
    r = subprocess.run([sys.executable, "-I", "-c", code], capture_output=True, text=True, timeout=60)
    print(f"{name}: return code {r.returncode} {r.stdout.strip()}")
```

Recorded on 3.15.2 and main: all three children exit with SIGSEGV (`-11`) without printing `no crash`. Expected: reject invalid layout metadata or use stable layout bounds; ordinary attribute rebinding must not cause out-of-bounds C access.

Cause: Objects/structseq.c:27-42 reads the attributes from the type dict. `PyStructSequence_New` (:65-88) allocates from these values, but `structseq_replace` copies the original object's real number of fields (:399, :447-449). `structseq_reduce` indexes `tp_members` using unchecked `n_unnamed_fields` (:351, :368-370). The constructor reads sizes before `PySequence_Fast` can run Python and allocates using freshly read sizes afterwards (:173-186, :228-236). Store layout metadata outside the writable dict, or make it read-only and validate consistency with the fixed type layout.

**Triage:** gh-155322 reports the same mutable-metadata root cause through construction with a dict argument. The record's review of PR gh-155361 identifies these additional paths as uncovered. Review them with that issue and recheck the current patch before opening another report.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [typeobj-structseq-mutable-size-attrs](https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-structseq-mutable-size-attrs.yaml)
