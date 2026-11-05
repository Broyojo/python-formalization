<!-- title: csv.reader segfaults when its input iterator re-enters the reader and … -->
# Bug report

### Bug description

A plain Python iterator class crashes the interpreter with SIGSEGV. The iterator's __next__ calls
next() on the reader that is reading it. The inner call reads an unterminated quoted field, hits
the end of input and returns the row, which sets self->fields to NULL but leaves
state == IN_QUOTED_FIELD. When the outer call's PyIter_Next then also reports the end of input, the
test at Modules/_csv.c:948 passes on the state, and parse_save_field appends to the NULL list. The
guard added for the same situation, "iterator has already advanced the reader", is only on the path
where the iterator returns a line. The Lean model reached this by itself: difftest scripts with a
re-entrant step predicted every segfault CPython then produced.

```python
import csv
class It:
    def __init__(self):
        self.n = 0
        self.reader = None
    def __iter__(self):
        return self
    def __next__(self):
        self.n += 1
        if self.n == 1:
            next(self.reader)
            raise StopIteration
        if self.n == 2:
            return '"abc'
        raise StopIteration
it = It()
r = csv.reader(it)
it.reader = r
next(r)
```

**Expected:** A csv.Error, such as "iterator has already advanced the reader", or StopIteration. No crash.

**Actual:** python3 3.15.2: exit status -11 (SIGSEGV). REPRODUCED. main 3.16.0a1+dev: exit status -11 (SIGSEGV). REPRODUCED.

**Cause:** Modules/_csv.c:948-953: the end-of-input branch calls parse_save_field without checking self->fields, which is NULL after an inner call returned a row (:992-993). parse_save_field reaches PyList_Append(NULL, ...) at :688, and PyList_Check reads through the pointer (Objects/listobject.c:562).

**Possible fix:** Check self->fields == NULL in the end-of-input branch too, and raise the same csv.Error, as python/cpython#157379 proposes.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
