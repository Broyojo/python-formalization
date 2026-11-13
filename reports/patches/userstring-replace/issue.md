<!-- title: collections.UserString.replace() rejects the count keyword -->
### Bug report

Since 3.13, `str.replace()` accepts `count` as a keyword argument (gh-106487), and 3.15 did the same for `bytes.replace()` (gh-147856). `collections.UserString.replace()` names that parameter `maxsplit` instead, so the keyword form that works on `str` raises `TypeError` on a `UserString`. It looks like the name was copied from `split()` a long time ago.

```python
from collections import UserString

print('aaa'.replace('a', 'b', count=1))
print(UserString('aaa').replace('a', 'b', count=1))
```

Actual:

```
baa
Traceback (most recent call last):
  ...
TypeError: UserString.replace() got an unexpected keyword argument 'count'
```

Expected: `baa` printed twice. (Conversely, `UserString('aaa').replace('a', 'b', maxsplit=1)` works although `str.replace` has no such parameter.)

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude) helped find this and prepare the fix; I reviewed and tested it.
