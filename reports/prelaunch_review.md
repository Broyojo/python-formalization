# Prelaunch technical review

Reviewed 2026-11-05. No issues, comments, Discourse posts, or X posts were sent; no publication or hosting settings were changed.

## Decision

**41 drafts are technically approved: 22 single issues and 19 grouped issues. Ten remain unticked.** See [the checklist](drafts/INDEX.md). These ticks record technical review, not the human submitter's reading or policy certification.

The two buffered-initialization cases are combined in `single/buffered-reinit-free.md`. The separate zero-size draft remains local and unticked. All 37 records previously waiting on main remain unfiled; 27 now have main confirmation, while 10 do not.

## Reproduction evidence

- Read and cross-checked `scratch/final/drafts.log`, `cb-3.15.2.log`, and `cb-main.log` against the selected records.
- The saved 3.15.2 check has 418 REPRODUCED records, zero NOT REPRODUCED, and 18 skipped as GONE. Main has 402 REPRODUCED, 16 NOT REPRODUCED, and the same 18 GONE.
- The fresh full draft run tested 108 blocks on both interpreters: 216 executions. Three subsequent draft edits were checked in six more executions. After withholding the unsupported Random claim, the final documents contain 107 blocks, all tested byte-for-byte. Section numbering changed when that claim was removed; matches use code SHA-256, not section positions.
- Every grouped reproducer printed its conditional confirmation on both interpreters. Single-draft output was checked against each stated error, child signal, mutation, or hang. The LRU case reached the checker's 60-second timeout on both interpreters; the saved record checks independently confirm it.
- Tested Linux builds: CPython 3.15.2 (`5e58eaa`) and main 3.16.0a1+dev (`ef1fce0`). This is confirmation on that main snapshot, not a claim about future main commits.
- The saved build log ends with success (3084 jobs). The saved audit reports 4516 properties: 3834 proven, 588 refuted, 94 open, zero failing. Lean files were not changed or rebuilt during this review.

The current code hashes, interpreter exit statuses, and matching log labels are in [prelaunch_checks.tsv](prelaunch_checks.tsv). Exit zero can enclose a deliberately crashing child; negative signals and the LRU timeout are expected reproductions, not checker failures.

Full rerun (through the build-pod wrapper, with core dumps disabled):

```sh
scripts/r bash -c 'ulimit -c 0; python3 -VV && /home/sky/pf/vendor/cpython-main/python.exe -VV && python3 reports/check_drafts.py --python python3 --python /home/sky/pf/vendor/cpython-main/python.exe --full-output' > scratch/final/drafts-final.log 2>&1
```

The supplementary run used the same interpreters with `--draft single/datetime-pep495-none.md --draft single/email-msgid-space.md --draft single/inplace-mul.md`, saved as `scratch/final/drafts-supplement.log`. Raw logs remain in untracked `scratch/final/`.

## Corrections made

- Fixed the generator deleting the bodies of reproduction checks; nine Python blocks had syntax errors. Kept the conditional checks and a readable confirmation message.
- Fixed the checker ignoring `PYTHONMALLOC=debug` under `-I`. Allocator-specific blocks now use `-s -P` with other PYTHON environment variables removed. The keyword-defaults draft now segfaults on both interpreters.
- Added complete-output and selected-draft options, and unbuffered output, for reviewable reruns.
- Confirmed the AST draft on 3.15.2 and removed its obsolete validation-pending text.
- Labelled datetime twins explicitly; ran both email entry points and both int-subclass/IntEnum multiplication paths instead of stopping at the first expected exception.
- Corrected the struct-sequence draft: the constructor child aborted on 3.15.2 in this run; it did not always segfault.
- Excluded two known upstream duplicates from the bytes-object group: bytearray self-concatenation (gh-85269) and shrink failure (gh-160303). Removed the grouped multiplication report already covered by the single draft.
- Withheld the unseeded Random-subclass claim: its subclass bypasses base initialization and the supported expected behavior is not established. It remains in the bug records and minor/possibly-intended pool.
- Retained caveats from `maybe_intended` fields that the generator previously hid when they began with words such as "Partly" or "Unknown".
- Confirmed the array half-float draft is an exact duplicate of open gh-158345 using `gh issue view 158345 --repo python/cpython --json number,title,state,body`. Its body explicitly includes 3.15 e arrays. Updated the record and triage; this was a read-only query.
- Regenerated FINDINGS.md with the supplied command. Corrected two generated duplicate-column false positives whose source relations explicitly say "not a duplicate" (gh-151722 and gh-36723); the shared generator was left unchanged. A plain regeneration will restore those two false positives until its parser is fixed.
- Updated draft disclosures to distinguish completed technical checks from the human submitter's remaining review.

## Held drafts

| Draft | Reason |
|---|---|
| [single/array-e-overflow.md](drafts/single/array-e-overflow.md) | Confirmed duplicate of open gh-158345, which explicitly includes 3.15 e arrays; read-only GitHub check recorded in the YAML. |
| [single/array-fromlist-restore.md](drafts/single/array-fromlist-restore.md) | Reproduces; related to gh-152166 / PR gh-152167. Decide whether to add this error path to that report after reviewing its current patch. |
| [single/array-ins1-stale-size.md](drafts/single/array-ins1-stale-size.md) | Reproduces; gh-158345 / PR gh-158348 concerns the same helper and its proposed restructuring may cover this path. Needs related-report triage. |
| [single/buffered-detach.md](drafts/single/buffered-detach.md) | Reproduces; record explicitly marks it a duplicate of gh-154997. |
| [single/buffered-reinit-size0.md](drafts/single/buffered-reinit-size0.md) | Reproduces; both its reproducer and record link are now included in the approved buffered-reinit-free.md. Do not file twice. |
| [single/methodcaller-shared-kwargs.md](drafts/single/methodcaller-shared-kwargs.md) | Reproduces; record recommends coordinating with gh-155733 / PR gh-155779. Decide follow-up versus a new report after reviewing that patch. |
| [single/struct-reinit.md](drafts/single/struct-reinit.md) | Reproduces; overlaps the closed gh-158695 report and bugforge records. Needs related-report triage before a new filing. |
| [single/structseq-size-attributes.md](drafts/single/structseq-size-attributes.md) | Reproduces; same mutable-metadata cause as gh-155322 / PR gh-155361. Decide how to add the extra paths to that report. |
| [single/super-uninitialized.md](drafts/single/super-uninitialized.md) | Reproduces; confirmed duplicate in the record of gh-155376 / PR gh-155379. |
| [group/dictset-1.md](drafts/group/dictset-1.md) | Reproduces; its only finding bypasses OrderedDict with dict methods. The record acknowledges known desynchronization and the earlier gh-68914 closure; the expected supported behavior is insufficiently established for launch. |

Related-issue and patch states above, except the explicit live check of gh-158345, come from the existing records. Those cases are deliberately withheld rather than treated as freshly triaged new issues.

## Previously waiting on main

**10 NOT REPRODUCED on main: keep unfiled.**

- `bytecode-anext-default-restarts-await`
- `bytecode-gen-athrow-awaitable-reusable`
- `bytecode-posonly-keyword-borrowed-qualname`
- `datetime-time-subminute-offset`
- `longobj-complex-pow-infinite-base-overflow`
- `longobj-complex-pow-infinite-phase-edom`
- `pyio-bytesio-write-near-maxsize-systemerror`
- `pyio-stringio-truncate-index-close-crash`
- `sequences-array-float-narrowing`
- `textlibs-csv-sniffer-unusable-dialect`

**27 REPRODUCED on main: eligible for separate draft review, still unfiled.**

- `bytecode-gen-throw-created-skips-pep479`
- `dictset-set-lookup-table-aba`
- `dictset-setiter-negative-length-hint`
- `ipaddress-subnets-host-network-skips-validation`
- `ipaddress-supernet-zero-prefix-skips-validation`
- `itertools-doc-combinatorics-negative-r`
- `itertools-groupby-eq-reentry-null-currkey`
- `pyio-bytesio-twin-argument-handling`
- `sequences-array-w-fromunicode-empty`
- `textlibs-etree-elementpath-errors`
- `textlibs-etree-setstate-attrib-systemerror`
- `textlibs-zoneinfo-before-first-transition`
- `unicodeobj-codec-charmap-build-fffe`
- `unicodeobj-codec-surrogateescape-error-span`
- `unicodeobj-codec-unicode-escape-octal-chunks`
- `unicodeobj-codecs-getencoder-raw-tuple`
- `unicodeobj-codecs-namereplace-pua-names`
- `unicodeobj-codecs-normalize-encoding-nul`
- `unicodeobj-codecs-reraise-subclasscheck`
- `unicodeobj-codecs-surrogate-handlers-systemerror`
- `unicodeobj-format-grouping-width-loop`
- `unicodeobj-format-nul-conversion`
- `unicodeobj-format-nul-presentation-type`
- `unicodeobj-fromformat-negative-precision`
- `unicodeobj-text-dedent-negative-memcpy`
- `unicodeobj-text-final-sigma-cased-ignorable`
- `unicodeobj-text-translate-stateful-table`

## Saved log integrity

| Log | SHA-256 |
|---|---|
| `scratch/final/drafts.log` | `ca148ce2d7fb2ca4473451d1f64a3bc3d29d68ecf5c7ce4a7fd80bd6adfc7e6f` |
| `scratch/final/cb-3.15.2.log` | `4596f02b72f9548e6cc047ae71ddf6ae933d0b9b4d202182f1b1742859b70fe2` |
| `scratch/final/cb-main.log` | `29416c96e0596ee80e62da1f4a95c4d36f1f3b3be5ef6d75076a8efc880151a7` |
| `scratch/final/drafts-final.log` | `f7f6301437074f4093c5b70d005b6ebe61a26a022149f6118c11c73a64ae537b` |
| `scratch/final/drafts-supplement.log` | `74b602ad383caf3e705da55e72e04e8890c6c03171ef775287b9eb1225610a74` |

Regenerating drafts resets their approval boxes. Any later code edit needs a matching rerun before its approval is retained.
