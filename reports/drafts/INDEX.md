# Draft issues for python/cpython

Change `[ ]` to `[x]` for each draft you have read and can explain in your own words (CPython's AI-tools policy requires it). `python3 reports/file_issues.py` files only ticked drafts and does nothing without `--go`.

## Single issues

- [ ] P2 [array('e'): append() or insert() of an out-of-range float raises OverflowError but still grows the array (new in 3.15)](single/array-e-overflow.md)
- [ ] P1 [bytearray.strip() reads freed memory if the argument's __release_buffer__ resizes the bytearray](single/bytearray-strip-release.md)
- [ ] P2 [datetime == reads None as a timedelta when utcoffset() is None for only one fold](single/datetime-pep495-none.md)
- [ ] P2 [except* crashes when an ExceptionGroup subclass's split() returns a non-exception](single/eg-match-split.md)
- [ ] P2 [email: UnboundLocalError when a Message-ID's [domain literal] starts with a space](single/email-msgid-space.md)
- [ ] P2 [Setting frame.f_lineno can approve a jump to an incompatible stack and crash (three cases)](single/flineno-jumps.md)
- [ ] P2 [Closing a long chain of yield-from generators overflows the C stack](single/gen-close-chain.md)
- [ ] P2 [x *= [1] raises TypeError for an int subclass, although x * [1] works](single/inplace-mul.md)
- [ ] P2 [Use-after-free when a __kwdefaults__ key's __eq__ replaces __kwdefaults__ during a call](single/kwdefaults-uaf.md)
- [ ] P2 [lru_cache: a cache hit from __eq__ during eviction corrupts the C cache's list, and the next gc.collect() hangs](single/lru-cache-cycle.md)
- [ ] P1 [memoryview: a view released by __buffer__ or __index__ in the middle of == or item assignment is still used](single/memoryview-released.md)
- [ ] P1 [functools.partial.__setstate__ with a tuple subclass as args miscounts placeholders, then crashes when called](single/partial-setstate.md)
- [ ] P1 [functools.partial: changing p.keywords during the call's keyword merge overflows a stack buffer (new in 3.15)](single/partial-vectorcall-kw.md)
- [ ] P1 [ZoneInfo.clear_cache() crashes if a cache key's __del__ creates a ZoneInfo](single/zoneinfo-clear-cache.md)

## Still to write (17)

Each has a full record with a reproducer and the cause. Write the body as reports/issue_text/<name>.md (copy the three header lines of an existing one), then run this script again.

- P2 [dictset-fromkeys-frozendict-rewritten](../../bugs/dictset-fromkeys-frozendict-rewritten.yaml)
- P1 [dictset-fromkeys-gc-track-non-gc](../../bugs/dictset-fromkeys-gc-track-non-gc.yaml)
- P1 [dictset-setdefault-split-null](../../bugs/dictset-setdefault-split-null.yaml)
- P1 [operator-methodcaller-reduce-shares-kwargs](../../bugs/operator-methodcaller-reduce-shares-kwargs.yaml)
- P2 [pygrammar-check-none-in-list-segfault](../../bugs/pygrammar-check-none-in-list-segfault.yaml)
- P2 [pyio-buffered-reentrant-detach-crash](../../bugs/pyio-buffered-reentrant-detach-crash.yaml)
- P1 [pyio-buffered-reentrant-init-free](../../bugs/pyio-buffered-reentrant-init-free.yaml)
- P1 [pyio-buffered-reentrant-init-size0](../../bugs/pyio-buffered-reentrant-init-size0.yaml)
- P2 [sequences-array-fromlist-restore-stale](../../bugs/sequences-array-fromlist-restore-stale.yaml)
- P1 [sequences-array-ins1-stale-size](../../bugs/sequences-array-ins1-stale-size.yaml)
- P1 [textlibs-etree-slice-backward-dup](../../bugs/textlibs-etree-slice-backward-dup.yaml)
- P2 [textlibs-struct-reinit-memory-safety](../../bugs/textlibs-struct-reinit-memory-safety.yaml)
- P2 [typeobj-exc-getstate-borrowed-dict](../../bugs/typeobj-exc-getstate-borrowed-dict.yaml)
- P2 [typeobj-set-class-reentrant-slot-eq](../../bugs/typeobj-set-class-reentrant-slot-eq.yaml)
- P2 [typeobj-set-mro-error-borrowed-mro](../../bugs/typeobj-set-mro-error-borrowed-mro.yaml)
- P2 [typeobj-structseq-mutable-size-attrs](../../bugs/typeobj-structseq-mutable-size-attrs.yaml)
- P2 [typeobj-super-uninitialized-get](../../bugs/typeobj-super-uninitialized-get.yaml)

## Grouped issues (at most 8 findings each)

- [ ] [Small inconsistencies in functools, enum, random and other core library modules found by a formal model (part 1 of 2)](group/corelibs-1.md)
- [ ] [Small inconsistencies in functools, enum, random and other core library modules found by a formal model (part 2 of 2)](group/corelibs-2.md)
- [ ] [Small inconsistencies in text and binary codecs found by a formal model (part 1 of 2)](group/textlibs-1.md)
- [ ] [Small inconsistencies in text and binary codecs found by a formal model (part 2 of 2)](group/textlibs-2.md)
- [ ] [Small inconsistencies in bytes, bytearray and memoryview found by a formal model](group/bytesobj-1.md)
- [ ] [Small inconsistencies in io and _pyio found by a formal model](group/pyio-1.md)
- [ ] [Small inconsistencies in type objects found by a formal model](group/typeobj-1.md)
- [ ] [Small inconsistencies in datetime found by a formal model](group/datetime-1.md)
- [ ] [Small inconsistencies in json found by a formal model](group/json-1.md)
- [ ] [Small inconsistencies in array and collections found by a formal model](group/sequences-1.md)
- [ ] [Small inconsistencies in decimal found by a formal model](group/decimal-1.md)
- [ ] [Small inconsistencies in ipaddress found by a formal model](group/ipaddress-1.md)
- [ ] [Small inconsistencies in the bytecode interpreter found by a formal model](group/bytecode-1.md)
- [ ] [Small inconsistencies in the parser and grammar found by a formal model](group/pygrammar-1.md)
- [ ] [Small inconsistencies in calendar and statistics found by a formal model](group/calstat-1.md)
- [ ] [Small inconsistencies in dict and set found by a formal model](group/dictset-1.md)
- [ ] [Small inconsistencies in itertools found by a formal model](group/itertools-1.md)
- [ ] [Small inconsistencies in int found by a formal model](group/longobj-1.md)
- [ ] [Small inconsistencies in math found by a formal model](group/mathint-1.md)
- [ ] [Small inconsistencies in range and slice found by a formal model](group/rangeslice-1.md)

## Waiting on a re-run on main (37)

These are filed only after scripts/check_bugs.py confirms them on main: bytecode-anext-default-restarts-await, bytecode-gen-athrow-awaitable-reusable, bytecode-gen-throw-created-skips-pep479, bytecode-posonly-keyword-borrowed-qualname, datetime-time-subminute-offset, dictset-set-lookup-table-aba, dictset-setiter-negative-length-hint, ipaddress-subnets-host-network-skips-validation, ipaddress-supernet-zero-prefix-skips-validation, itertools-doc-combinatorics-negative-r, itertools-groupby-eq-reentry-null-currkey, longobj-complex-pow-infinite-base-overflow, longobj-complex-pow-infinite-phase-edom, pyio-bytesio-twin-argument-handling, pyio-bytesio-write-near-maxsize-systemerror, pyio-stringio-truncate-index-close-crash, sequences-array-float-narrowing, sequences-array-w-fromunicode-empty, textlibs-csv-sniffer-unusable-dialect, textlibs-etree-elementpath-errors, textlibs-etree-setstate-attrib-systemerror, textlibs-zoneinfo-before-first-transition, unicodeobj-codec-charmap-build-fffe, unicodeobj-codec-surrogateescape-error-span, unicodeobj-codec-unicode-escape-octal-chunks, unicodeobj-codecs-getencoder-raw-tuple, unicodeobj-codecs-namereplace-pua-names, unicodeobj-codecs-normalize-encoding-nul, unicodeobj-codecs-reraise-subclasscheck, unicodeobj-codecs-surrogate-handlers-systemerror, unicodeobj-format-grouping-width-loop, unicodeobj-format-nul-conversion, unicodeobj-format-nul-presentation-type, unicodeobj-fromformat-negative-precision, unicodeobj-text-dedent-negative-memcpy, unicodeobj-text-final-sigma-cased-ignorable, unicodeobj-text-translate-stateful-table.

## Not filed at launch (227 minor or possibly intended findings)

P4/P5 findings, and ones whose record says they are probably intended, stay in bugs/ and are offered in the Discourse post. Duplicates of existing issues and 3.14-only behaviour are not filed either; see reports/triage.tsv.
