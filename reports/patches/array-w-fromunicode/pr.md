# gh-XXXXXX: Fix SystemError from array('w').fromunicode('') on an empty array

`array.array.fromunicode()` passed `ob_item` to `PyUnicode_AsUCS4()` even when the string was empty. For an array without an item buffer, `ob_item` is `NULL`, so `PyUnicode_AsUCS4()` set an exception that the caller ignored, which surfaced as `SystemError` (or an assertion failure in a debug build). The function now returns early when there is nothing to copy, as the `'u'` branch in 3.15 already does. The test covers an array that never had a buffer and one whose buffer was freed by `del a[:]`, and then checks that later non-empty calls still work.

Reviewer notes:

- The early return is placed after the size overflow check and before `array_resize()`. For an empty string `array_resize(self, old_size)` was a no-op, so skipping it changes nothing else, including the `BufferError` check for exported buffers.
- Main no longer has the `'u'` type code, so the new test runs only for `'w'` here. On 3.15, `UCS4Test` inherits from `UnicodeTest`, so the same test runs for both `'u'` and `'w'`; the C change applies to the `else` (`'w'`) branch there with the same hunk.
- The open free-threading PR gh-161787 rewrites this function and adds an equivalent `ustr_length == 0` early return at the same place, so whichever merges second has a small, mechanical conflict. This fix is independent of that PR and is suitable for backport to 3.15 (and 3.14, which has the same code).
