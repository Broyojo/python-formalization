# Draft issues for python/cpython

Checked boxes record Codex's technical approval in the [prelaunch review](../prelaunch_review.md): **41 approved drafts (22 single, 19 grouped)**. The person filing must still read and be able to explain each draft, as required by this checklist. `python3 reports/file_issues.py` files only ticked drafts; no filing was performed during review.

## Single issues

- [ ]  [array('e'): append() or insert() of an out-of-range float raises OverflowError but still grows the array (new in 3.15)](single/array-e-overflow.md)
- [ ] P2 [array.fromlist() regrows a callback-cleared array on its error path, exposing uninitialized items](single/array-fromlist-restore.md)
- [ ] P1 [array.append/insert/extend use a size saved before item conversion, exposing uninitialized items after a callback clears the array](single/array-ins1-stale-size.md)
- [x] P2 [compile() segfaults on a small hand-built AST with None in Try.handlers](single/ast-none-list.md)
- [ ] P2 [BufferedReader.read() crashes if the raw stream's closed property detaches the reader](single/buffered-detach.md)
- [x] P1 [Reentrant BufferedReader/Writer initialization frees active storage or leaves an invalid buffer size](single/buffered-reinit-free.md)
- [ ] P1 [A reentrant BufferedReader/Writer.__init__(raw, 0) leaves a zero buffer size: division by zero or an endless write loop](single/buffered-reinit-size0.md)
- [x] P1 [bytearray.strip() reads freed memory if the argument's __release_buffer__ resizes the bytearray](single/bytearray-strip-release.md)
- [x] P2 [Reentrant __class__ assignment from a __slots__ name comparison decrefs the old class twice and crashes](single/class-assignment-slot-eq.md)
- [x] P2 [datetime == reads None as a timedelta when utcoffset() is None for only one fold](single/datetime-pep495-none.md)
- [x] P2 [except* crashes when an ExceptionGroup subclass's split() returns a non-exception](single/eg-match-split.md)
- [x] P2 [email: UnboundLocalError when a Message-ID's [domain literal] starts with a space](single/email-msgid-space.md)
- [x] P1 [ElementTree slice assignment with start greater than stop duplicates a child without owning its second reference](single/etree-backward-slice.md)
- [x] P2 [AttributeError and ImportError copy a borrowed instance dict during __reduce__, allowing it to be freed by a key comparison](single/exception-getstate-dict.md)
- [x] P2 [Setting frame.f_lineno can approve a jump to an incompatible stack and crash (three cases)](single/flineno-jumps.md)
- [x] P2 [frozendict.fromkeys() can expose an untracked frozendict and later mutate it after hashing](single/fromkeys-frozendict.md)
- [x] P1 [dict.fromkeys() GC-tracks a non-GC object returned by a subclass constructor (3.15 regression)](single/fromkeys-gc-track.md)
- [x] P2 [Closing a long chain of yield-from generators overflows the C stack](single/gen-close-chain.md)
- [x] P2 [x *= [1] raises TypeError for an int subclass, although x * [1] works](single/inplace-mul.md)
- [x] P2 [Use-after-free when a __kwdefaults__ key's __eq__ replaces __kwdefaults__ during a call](single/kwdefaults-uaf.md)
- [x] P2 [lru_cache: a cache hit from __eq__ during eviction corrupts the C cache's list, and the next gc.collect() hangs](single/lru-cache-cycle.md)
- [x] P1 [memoryview: a view released by __buffer__ or __index__ in the middle of == or item assignment is still used](single/memoryview-released.md)
- [ ] P1 [operator.methodcaller.__reduce__() exposes its private kwargs through partial.keywords, causing stale calls and a repr crash](single/methodcaller-shared-kwargs.md)
- [x] P2 [MRO conflict formatting reads a freed base MRO if metaclass __hash__ changes __bases__](single/mro-error-borrowed-tuples.md)
- [x] P1 [functools.partial.__setstate__ with a tuple subclass as args miscounts placeholders, then crashes when called](single/partial-setstate.md)
- [x] P1 [functools.partial: changing p.keywords during the call's keyword merge overflows a stack buffer (new in 3.15)](single/partial-vectorcall-kw.md)
- [x] P1 [dict.setdefault() segfaults on an instance dict with an absent shared key passed as a str subclass](single/setdefault-split-null.md)
- [ ] P2 [Reinitializing an active Struct lets iter_unpack read past its buffer or divide by zero](single/struct-reinit.md)
- [ ] P2 [Writable struct-sequence size attributes cause out-of-bounds access in copy.replace, __reduce__ and construction](single/structseq-size-attributes.md)
- [ ] P2 [Binding an uninitialized super object segfaults in supercheck](single/super-uninitialized.md)
- [x] P1 [ZoneInfo.clear_cache() crashes if a cache key's __del__ creates a ZoneInfo](single/zoneinfo-clear-cache.md)

## Still to write (0)

Each has a full record with a reproducer and the cause. Write the body as reports/issue_text/<name>.md (copy the three header lines of an existing one), then run this script again.


## Grouped issues (at most 8 findings each)

- [x] [Small inconsistencies in functools, enum, random and other core library modules found by a formal model (part 1 of 2)](group/corelibs-1.md)
- [x] [Small inconsistencies in functools, enum, random and other core library modules found by a formal model (part 2 of 2)](group/corelibs-2.md)
- [x] [Small inconsistencies in text and binary codecs found by a formal model (part 1 of 2)](group/textlibs-1.md)
- [x] [Small inconsistencies in text and binary codecs found by a formal model (part 2 of 2)](group/textlibs-2.md)
- [x] [Small inconsistencies in io and _pyio found by a formal model](group/pyio-1.md)
- [x] [Small inconsistencies in datetime found by a formal model](group/datetime-1.md)
- [x] [Small inconsistencies in type objects found by a formal model](group/typeobj-1.md)
- [x] [Small inconsistencies in bytes, bytearray and memoryview found by a formal model](group/bytesobj-1.md)
- [x] [Small inconsistencies in json found by a formal model](group/json-1.md)
- [x] [Small inconsistencies in array and collections found by a formal model](group/sequences-1.md)
- [x] [Small inconsistencies in decimal found by a formal model](group/decimal-1.md)
- [x] [Small inconsistencies in ipaddress found by a formal model](group/ipaddress-1.md)
- [x] [Small inconsistencies in the bytecode interpreter found by a formal model](group/bytecode-1.md)
- [x] [Small inconsistencies in the parser and grammar found by a formal model](group/pygrammar-1.md)
- [x] [Small inconsistencies in calendar and statistics found by a formal model](group/calstat-1.md)
- [ ] [Small inconsistencies in dict and set found by a formal model](group/dictset-1.md)
- [x] [Small inconsistencies in itertools found by a formal model](group/itertools-1.md)
- [x] [Small inconsistencies in int found by a formal model](group/longobj-1.md)
- [x] [Small inconsistencies in math found by a formal model](group/mathint-1.md)
- [x] [Small inconsistencies in range and slice found by a formal model](group/rangeslice-1.md)

## Held drafts (10)

| Draft | Reason |
|---|---|
| [single/array-e-overflow.md](single/array-e-overflow.md) | Confirmed duplicate of open gh-158345, which explicitly includes 3.15 e arrays; read-only GitHub check recorded in the YAML. |
| [single/array-fromlist-restore.md](single/array-fromlist-restore.md) | Reproduces; related to gh-152166 / PR gh-152167. Decide whether to add this error path to that report after reviewing its current patch. |
| [single/array-ins1-stale-size.md](single/array-ins1-stale-size.md) | Reproduces; gh-158345 / PR gh-158348 concerns the same helper and its proposed restructuring may cover this path. Needs related-report triage. |
| [single/buffered-detach.md](single/buffered-detach.md) | Reproduces; record explicitly marks it a duplicate of gh-154997. |
| [single/buffered-reinit-size0.md](single/buffered-reinit-size0.md) | Reproduces; both its reproducer and record link are now included in the approved buffered-reinit-free.md. Do not file twice. |
| [single/methodcaller-shared-kwargs.md](single/methodcaller-shared-kwargs.md) | Reproduces; record recommends coordinating with gh-155733 / PR gh-155779. Decide follow-up versus a new report after reviewing that patch. |
| [single/struct-reinit.md](single/struct-reinit.md) | Reproduces; overlaps the closed gh-158695 report and bugforge records. Needs related-report triage before a new filing. |
| [single/structseq-size-attributes.md](single/structseq-size-attributes.md) | Reproduces; same mutable-metadata cause as gh-155322 / PR gh-155361. Decide how to add the extra paths to that report. |
| [single/super-uninitialized.md](single/super-uninitialized.md) | Reproduces; confirmed duplicate in the record of gh-155376 / PR gh-155379. |
| [group/dictset-1.md](group/dictset-1.md) | Reproduces; its only finding bypasses OrderedDict with dict methods. The record acknowledges known desynchronization and the earlier gh-68914 closure; the expected supported behavior is insufficiently established for launch. |

## Previously waiting on main (37)

The saved `cb-main.log` confirms **27** and reports **10 not reproduced**. All 37 remain outside the launch checklist; confirmation alone does not approve a new draft. The per-record results are in the [review](../prelaunch_review.md#previously-waiting-on-main).

Do not file the 10 non-reproducing records: `bytecode-anext-default-restarts-await`, `bytecode-gen-athrow-awaitable-reusable`, `bytecode-posonly-keyword-borrowed-qualname`, `datetime-time-subminute-offset`, `longobj-complex-pow-infinite-base-overflow`, `longobj-complex-pow-infinite-phase-edom`, `pyio-bytesio-write-near-maxsize-systemerror`, `pyio-stringio-truncate-index-close-crash`, `sequences-array-float-narrowing`, `textlibs-csv-sniffer-unusable-dialect`.

## Not filed at launch (228 minor or possibly intended findings)

P4/P5 findings, and ones whose record says they are probably intended, stay in bugs/ and are offered in the Discourse post. Duplicates of existing issues and 3.14-only behaviour are not filed either; see reports/triage.tsv.
