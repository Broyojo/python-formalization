<!-- title: ElementTree slice assignment with start > stop corrupts the children -->
# Bug report

### Bug description

For e[i:j] = seq with step 1, element_ass_subscr uses the start and stop that PySlice_AdjustIndices returns without clipping stop up to start, as list_ass_subscript does (adjust_slice_indexes). When the clipped start lies past the clipped stop (e[5:2] = [x]), slicelen is 0, so the insert branch shifts children[stop:length] right by len(seq), and the replace loop then writes seq at start. The child at stop..start-1 that was shifted stays in its old slot as well, and the child that sat at start is overwritten. The duplicate gets no Py_INCREF, so the element holds two slots for one reference, and the overwritten child's reference leaks. When the element is released, the duplicated child is decref'd twice and freed while other references to it remain.

```python
import sys
import xml.etree.ElementTree as ET
kids = [ET.Element('a%d' % i) for i in range(7)]
e = ET.Element('r')
e[:] = kids
before = sys.getrefcount(kids[2])
e[5:2] = [ET.Element('X')]
tags = [c.tag for c in e]
print(tags, 'refcount change of a2:', sys.getrefcount(kids[2]) - before)
# list semantics: ['a0', 'a1', 'a2', 'a3', 'a4', 'X', 'a5', 'a6']
```

**Expected:** ['a0', 'a1', 'a2', 'a3', 'a4', 'X', 'a5', 'a6'], as for a list and for the pure-Python Element (xml.etree.ElementTree imported with _elementtree blocked).

**Actual:** python3 3.15.2: ['a0', 'a1', 'a2', 'a2', 'a3', 'X', 'a5', 'a6'], a2 in two slots with an unchanged refcount. main (cpython-main/python.exe): identical. Use after free, run once to rate severity and not developed further: keeping `kids`, then `del e` and allocating 100 new Elements, makes kids[2].tag read 'z0' (the freed object's memory now holds a new Element) on both 3.15.2 and main, with -X dev and no crash. A 200,000-case comparison of the C and pure-Python Element over random slices, steps and lengths found no other disagreement in slice assignment or deletion.

**Cause:** Modules/_elementtree.c:1976-1977 computes slicelen with PySlice_AdjustIndices, which for step > 0 and start > stop leaves stop < start (Objects/sliceobject.c:264-304). The insert loop at :2026-2030 then runs `for (i = length-1; i >= stop; i--)` from stop, and the replace loop at :2033-2037 writes from start. list_ass_subscript avoids this through adjust_slice_indexes (Objects/listobject.c), which sets stop = start for such slices.

**Possible fix:** After PySlice_AdjustIndices at :1976, clip as list does: `if (step > 0 && stop < start) stop = start;` (and the mirror for step < 0, which is harmless here because step != 1 requires newlen == slicelen). The deletion path is unaffected because it returns when slicelen <= 0.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/textlibs-etree-slice-backward-dup.yaml
