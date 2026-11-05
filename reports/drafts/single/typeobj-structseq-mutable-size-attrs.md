<!-- title: Struct sequences trust n_fields, n_sequence_fields and … -->
# Bug report

### Bug description

`get_type_attr_as_size` (structseq.c:27-42) reads `n_fields`, `n_sequence_fields` and
`n_unnamed_fields` from the type's dict. The heap types built by `PyStructSequence_NewType`
(`os.stat_result`, `os.terminal_size`, `time.struct_time`, `resource.struct_rusage`, ...) are
not `Py_TPFLAGS_IMMUTABLETYPE`, so plain Python can rebind those attributes. The C code then
uses them as memory bounds, mixed with `get_real_size` (`Py_SIZE` + the hidden slots counted in
`tp_basicsize`, :55-62), which Python cannot change. Three paths go out of bounds without a
`dict` argument, and so are not the path in gh-155322:

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
crashed = 0
for name, code in CASES.items():
    r = subprocess.run([sys.executable, "-I", "-c", code], capture_output=True, text=True, timeout=60)
    print(f"{name}: return code {r.returncode} {r.stdout.strip()}")
    crashed += r.returncode < 0
```

**Expected:** Each case raises an exception (or works on the new sizes), and the interpreter keeps running.

**Actual:** python3 (3.15.2): all three subprocesses die with SIGSEGV (return code -11); the n_fields = 2**62 case also segfaults. REPRODUCED by scripts/check_bugs.py. main (3.16.0a1+dev, vendor/cpython-main/python.exe): the same, REPRODUCED.

**Cause:** Objects/structseq.c:27-42 returns whatever int the dict holds. :65-88 sizes the block from it; :399, :447-449 (replace) and :351, :368-370 (reduce) loop over `get_real_size`, which comes from `tp_basicsize`; :369 and :242 index `tp_members` with `n_unnamed_fields` from the dict; :173-186 then :228 read the dict on both sides of `PySequence_Fast`, which runs Python code. `PyStructSequence_NewType` (:780) builds a mutable heap type.

**Possible fix:** Do not take memory bounds from the dict: use `get_real_size`/`Py_SIZE`, the layout fixed when the type was built (store the three sizes in the type, or derive them from `tp_basicsize` and `tp_members`), and read them once per call after any Python code has run. Alternatively make the three attributes read-only on these types (`Py_TPFLAGS_IMMUTABLETYPE`, or data descriptors). The open PR gh-155361 validates the sizes at the top of `PyStructSequence_New` and `structseq_new_impl` only, which leaves the three paths above.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
