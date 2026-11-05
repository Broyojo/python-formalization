<!-- title: DUPLICATE of #158979: textwrap.wrap never returns when an indent is … -->
# Bug report

### Bug description

`textwrap.wrap(' ', width=1, initial_indent='xxx')` never returns. With an indent wider than width,
`_handle_long_word` takes one character each pass, and when that uses up the chunk it leaves `''` on
the stack. On the first line nothing removes it, and every pass after that takes zero characters.
With `drop_whitespace=False` and a wide `subsequent_indent`, `lines` also grows until memory runs out.

```python
import signal, textwrap

class Hang(Exception):
    pass

def alarm(*a):
    raise Hang

signal.signal(signal.SIGALRM, alarm)
signal.alarm(3)
try:
    print(textwrap.wrap(' ', width=1, initial_indent='xxx'))
except Hang:
```

**Expected:** A result, as the width < 1 guard in _handle_long_word intends.

**Actual:** python3 3.15.2: no result within 3 seconds. REPRODUCED. main 3.16.0a1+dev: no result within 3 seconds. REPRODUCED.

**Cause:** Lib/textwrap.py:223-224 leaves `chunk[end:]` on the stack even when it is empty. Lib/textwrap.py:284 drops it only once a line exists, and Lib/textwrap.py:291 fits it only when width is at least 0.

**Possible fix:** In _handle_long_word, pop the chunk when `chunk[end:]` is empty. Linked PRs on #158979 do this.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
