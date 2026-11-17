# gh-XXXXXX: Raise ValueError for truncated TZif data in zoneinfo

`zoneinfo._common.load_data()` is shared by the C and pure-Python `ZoneInfo`. It let `struct.error` escape on short reads, and it used `assert` to check that the footer starts with a newline. Short reads now go through a small `_read_exact()` helper that raises `ValueError("Invalid TZif file: unexpected end of file")`, the message already used for a footer without a trailing newline. The `assert` becomes an explicit `ValueError`. That matters most under `-O`, where the check was skipped and the footer's first byte was dropped: on 3.15.2, a footer of `EST5` without its newline silently loads as the zone `ST5` (UTC-5, abbreviation `ST`).

Reviewer notes:

- Negative counts in the header are still accepted, as before (RFC 8536 defines them as unsigned). Depending on the count, they are ignored or make `seek()` raise `OSError` on a real file. They could be rejected in a follow-up.
- A short abbreviation block (`charcnt` larger than the remaining data) is also still accepted as before.
- Backporting to 3.15 and 3.14 needs a manual cherry-pick if gh-161096 is not there yet (the `">lbB"` context line and the neighbouring tests differ).
