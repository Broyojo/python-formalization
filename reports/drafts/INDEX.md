# Draft issues for python/cpython

Change `[ ]` to `[x]` for each draft you have read and can explain in your own words (CPython's AI-tools policy requires it). `python3 reports/file_issues.py` files only ticked drafts and does nothing without `--go`.

## Single issues (crashes and memory errors)

- [ ] P2 [except* trusts the items returned by an overridden split()](single/bytecode-eg-match-split-items-unchecked.md)
- [ ] P2 [Setting f_lineno to jump out of a for loop crashes](single/bytecode-flineno-iter-index-as-object.md)
- [ ] P2 [Setting f_lineno to jump into a with block leaves NULL on the stack](single/bytecode-flineno-null-on-stack.md)
- [ ] P2 [Setting f_lineno into deeply nested blocks corrupts the stack](single/bytecode-flineno-stack-swap-truncation.md)
- [ ] P2 [Closing a deep yield-from chain overflows the C stack](single/bytecode-gen-close-deep-chain-stack-overflow.md)
- [ ] P2 [Use-after-free when __eq__ replaces f.__kwdefaults__ during a call](single/bytecode-kwonly-defaults-borrowed-dict.md)
- [ ] P2 [bytearray.__init__ from an iterator can write past the buffer](single/bytesobj-bytearray-init-iterator-ignores-start.md)
- [ ] P1 [Use-after-free in bytearray.strip() when __release_buffer__ mutates self](single/bytesobj-bytearray-strip-release-uaf.md)
- [ ] P1 [memoryview == reads freed memory when __buffer__ releases the view](single/bytesobj-memoryview-eq-released-by-buffer.md) *(re-check a 3.14.7 citation)*
- [ ] P1 [memoryview item assignment writes through a view released by __index__](single/bytesobj-memoryview-setitem-c-released.md)
- [ ] P2 [x *= [1] raises TypeError where x * [1] works for __index__ objects](single/corelibs-inplace-mul-heap-left.md)
- [ ] P2 [lru_cache: a raising __eq__ during eviction makes gc.collect() hang](single/corelibs-lru-evicted-hit-gc-hang.md)
- [ ] P1 [functools.partial.__setstate__ with a tuple subclass reads out of bounds](single/corelibs-partial-setstate-phcount.md)
- [ ] P1 [Calling functools.partial writes out of bounds when a key's __eq__ re-enters](single/corelibs-partial-vectorcall-stale-kw-count.md)
- [ ] P2 [datetime == crashes when utcoffset() is None for one fold only](single/datetime-pep495-delta-cmp-none.md)
- [ ] P1 [datetime.astimezone() crashes when a subclass __new__ returns a non-datetime](single/datetime-subclass-arith-result-type-confusion.md)
- [ ] P1 [ZoneInfo.clear_cache() can free cache nodes that are still in use](single/datetime-zoneinfo-clear-cache-reentrant-free.md)
- [ ] P2 [frozendict.fromkeys() on a subclass can mutate a frozendict in place](single/dictset-fromkeys-frozendict-rewritten.md)
- [ ] P1 [dict.fromkeys() on a subclass GC-tracks a non-GC object](single/dictset-fromkeys-gc-track-non-gc.md)
- [ ] P1 [dict.setdefault() segfaults on an instance __dict__ with a str-subclass key](single/dictset-setdefault-split-null.md) *(re-check a 3.14.7 citation)*
- [ ] P1 [operator.methodcaller.__reduce__ exposes its private kwargs dict](single/operator-methodcaller-reduce-shares-kwargs.md)
- [ ] P2 [compile() segfaults on an AST with None in a list field](single/pygrammar-check-none-in-list-segfault.md)
- [ ] P2 [BufferedReader.read() crashes if raw.closed detaches the buffer](single/pyio-buffered-reentrant-detach-crash.md)
- [ ] P1 [BufferedReader.__init__ re-entered from the raw stream frees the buffer in use](single/pyio-buffered-reentrant-init-free.md)
- [ ] P1 [A failed re-entrant BufferedReader.__init__ leaves buffer_size 0](single/pyio-buffered-reentrant-init-size0.md)
- [ ] P2 [array('e').append(65536.0) raises but keeps an uninitialised item](single/sequences-array-e-ins1-overflow-keeps-slot.md)
- [ ] P2 [array.fromlist() exposes stale memory when __index__ clears the array](single/sequences-array-fromlist-restore-stale.md)
- [ ] P1 [array.append() exposes stale memory when __index__ clears the array](single/sequences-array-ins1-stale-size.md)
- [ ] P2 [email: Message-ID '<a@[ x]>' raises UnboundLocalError](single/textlibs-email-msgid-no-fold-literal-space.md)
- [ ] P1 [ElementTree slice assignment with start > stop corrupts the children](single/textlibs-etree-slice-backward-dup.md)
- [ ] P2 [Calling Struct.__init__ on a live Struct accesses freed memory](single/textlibs-struct-reinit-memory-safety.md)
- [ ] P2 [AttributeError.__reduce__ uses a __dict__ that __eq__ can free](single/typeobj-exc-getstate-borrowed-dict.md)
- [ ] P2 [__class__ assignment can free the old class while it is in use](single/typeobj-set-class-reentrant-slot-eq.md)
- [ ] P2 [The MRO conflict error message can read freed memory](single/typeobj-set-mro-error-borrowed-mro.md)
- [ ] P2 [Struct sequences trust size attributes that Python code can rebind](single/typeobj-structseq-mutable-size-attrs.md)
- [ ] P2 [super.__new__(super).__get__(1) segfaults](single/typeobj-super-uninitialized-get.md)

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
