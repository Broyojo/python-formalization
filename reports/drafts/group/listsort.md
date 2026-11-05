<!-- title: listsort: 1 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. listobject.c: the MAX_MERGE_PENDING comment understates the stack depth powersort can need

The comment above MAX_MERGE_PENDING says "For a list with n elements, this needs at most
floor(log2(n)) + 1 entries even if we didn't force runs to a minimal length. So the number of
bits in a Py_ssize_t is plenty large enough for all cases." With runs not forced to a minimal
length, the bound is false: n = 3 with runs [1, 1, 1] keeps 3 entries pending, and
floor(log2(3)) + 1 = 2. Runs [2, 2, 1, 1] for n = 6 reach 4 entries (the comment allows 3). In
general [2**k, 2**k, 2**(k-1), ..., 2, 1, 1] sums to n = 3 * 2**k and reached k + 3 entries, one more
than the comment allows, at every k checked (0 to 61). An exhaustive search over all run structures
for n <= 18 exceeds the comment exactly at n = 3, 6, 7 and 12 to 15.
The Lean proof gives the correct bound for arbitrary run lengths: after each push the stack holds
s entries with 2**s < 4n, so s <= ceil(log2(n)) + 1 (listsort-stack-bound). That bound is attained:
n = 3 * 2**61 <= PY_SSIZE_T_MAX with runs [2**61, 2**61, 2**60, ..., 2, 1, 1] fills all 64 slots
(listsort-stack-bound-tight). So the conclusion of the comment holds, but with no slack for
arbitrary runs rather than "plenty".
This concerns a comment only. The code is correct: assert(ms.n < MAX_MERGE_PENDING) is proven to
hold for every list length up to PY_SSIZE_T_MAX, every comparison function and every run structure
(listsort-sort-push-assert).

<details><summary>Reproducer</summary>

```python
# Pending-stack depth cannot be observed from Python, so this is a line-for-line transcription of
# powerloop() and found_new_run() (Objects/listobject.c:2679-2749); it does not run list.sort.
import math
def powerloop(s1, n1, n2, n):
    result = 0
    a = 2 * s1 + n1
    b = a + n1 + n2
    while True:
        result += 1
        if a >= n:
            a -= n
            b -= n
        elif b >= n:
            break
        a <<= 1
        b <<= 1
    return result
def max_depth(lens):
    n = sum(lens)
    stack, pos, depth = [], 0, 0  # entries are [start, length, power]
    for n2 in lens:
        if stack:
            power = powerloop(stack[-1][0], stack[-1][1], n2, n)
            while len(stack) > 1 and stack[-2][2] > power:
                stack[-2][1] += stack[-1][1]
                stack.pop()
            stack[-1][2] = power
        stack.append([pos, n2, 0])
        pos += n2
        depth = max(depth, len(stack))
    return depth
for lens in ([1, 1, 1], [2, 2, 1, 1]):
    n = sum(lens)
    print(lens, 'n =', n, 'depth', max_depth(lens), 'comment allows', math.floor(math.log2(n)) + 1)
tight = [2**61] + [2**i for i in range(61, -1, -1)] + [1]
print('n = 3 * 2**61, sum ok:', sum(tight) == 3 * 2**61, 'depth', max_depth(tight))
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
