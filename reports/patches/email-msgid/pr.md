# gh-XXXXXX: Fix UnboundLocalError in email._header_value_parser for a domain literal starting with whitespace

`_get_ptext_to_endchars` read `pos` before assigning it when its input started with whitespace, because the first word from `_wsp_splitter` was then empty and the loop body never ran. This could happen when a `Message-ID`, `References` or `In-Reply-To` header has a domain literal such as `<a@[ x]>`. The `if not value` guard added for gh-134152 is replaced by a check on the empty first word, which covers both cases. The header now parses the same way as `<a@[x ]>`, as an obsolete id-right with an `ObsoleteHeaderDefect`.

Note: the open refactor in gh-152710 edits the same lines, so whichever merges second will need a small rebase.

AI tools (Claude) helped find this and prepare the fix; I reviewed and tested it.
