<!-- title: frozendict.fromkeys() can expose an untracked frozendict and later mutate it after hashing -->
<!-- form: bug -->
<!-- records: dictset-fromkeys-frozendict-rewritten -->
`frozendict.fromkeys()` on a subclass passes a completed but untracked frozendict to the subclass constructor. If the constructor saves that argument, another subclass can return it from `__new__`; a later `fromkeys()` then fills the saved object in place. Its contents change without invalidating its cached hash.

```python
leaked = []
class F(frozendict):
    def __init__(self, *args):
        if args:
            leaked.append(args[0])
F.fromkeys([1, 2])
fd = leaked[0]
before = dict(fd)
h = hash(fd)
table = {fd: 'value'}
class G(frozendict):
    def __new__(cls, *args):
        return fd
r = G.fromkeys(['x'])
equal = frozendict(dict(fd))
print('type', type(fd).__name__, 'same object', r is fd)
print('before', before, 'after', dict(fd))
print('hash unchanged', hash(fd) == h, 'equal copy == fd', equal == fd,
      'hash(copy) == hash(fd)', hash(equal) == hash(fd), 'copy in table', equal in table)
```

Recorded output on 3.15.2 and main:

```text
type frozendict same object True
before {1: None, 2: None} after {1: None, 2: None, 'x': None}
hash unchanged True equal copy == fd True hash(copy) == hash(fd) False copy in table False
```

The original frozendict should remain unchanged. Instead, an equal copy has a different hash and cannot find its entry in `table`.

Cause: Objects/dictobject.c:3443-3455 copies only a tracked frozendict returned by `cls()`. At :3592-3595 it passes the untracked copy to `cls(d)` without tracking it first. A later call accepts the escaped, untracked object as writable and inserts into it. Tracking the copy before calling Python, or copying any frozendict returned by `cls()`, would prevent this path. The record relates this to the change for gh-151722; that earlier issue does not describe this mutation.
