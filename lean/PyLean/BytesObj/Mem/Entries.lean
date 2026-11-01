import PyLean.Registry
import PyLean.BytesObj.Mem.Fallible
import PyLean.BytesObj.Mem.Effects
import PyLean.BytesObj.Mem.CmpTree
import PyLean.BytesObj.Mem.NDim
import PyLean.BytesObj.Mem.Fortran
import PyLean.BytesObj.Mem.Contig
import PyLean.BytesObj.Mem.Refuse

/-! Registry entries for memoryview (Objects/memoryobject.c). -/

namespace PyLean.BytesObj.Mem

open PyLean.Registry

def memFile : String := "Objects/memoryobject.c"

def entries : List Entry := [
  { id := "bytesobj-memoryview-struct-no-memory", pyFile := memFile
    pyFns := ["struct_get_unpacker", "fix_struct_error_int"]
    statement := "An item too large to allocate is MemoryError after the format is accepted, and fix_struct_error_int lets it out of ==."
    source := "memoryobject.c:2100-2104, :2917-2928", status := .proven
    prop := ``StructNoMemory, thm := some ``structNoMemory_proven },
  { id := "bytesobj-memoryview-item-eq-view", pyFile := memFile
    pyFns := ["memoryview_count_impl", "memoryview_index_impl"]
    statement := "An int, float or bool item never equals a memoryview and nothing equals a released one; a bytes item of format c compares through the reflected memory_richcompare, so against a view of format B it equals a view holding exactly that byte."
    source := "bytes_richcompare gives NotImplemented; do_richcompare tries the reflected memory_richcompare", status := .proven
    prop := ``ItemEqView, thm := some ``itemEqView_proven },
  { id := "bytesobj-memoryview-eq-truth", pyFile := memFile
    pyFns := ["memoryview_count_impl", "memoryview_index_impl"]
    statement := "What __eq__ returns is tested for truth, whatever it is: a str counts, None and [] do not."
    source := "PyObject_RichCompareBool, Objects/object.c:1119-1142", status := .proven
    prop := ``EqTruth, thm := some ``eqTruth_proven },
  { id := "bytesobj-memoryview-pack-bool-len", pyFile := memFile
    pyFns := ["pack_single"]
    statement := "Storing through ? an object with __len__ runs it: 0 stores 0, a positive length stores 1, a negative one and an exception raise, write nothing and keep their class."
    source := "PyObject_IsTrue, Objects/object.c; memoryobject.c:1988-1989", status := .proven
    prop := ``PackBoolLen, thm := some ``packBoolLen_proven },
  { id := "bytesobj-memoryview-pack-messages", pyFile := memFile
    pyFns := ["pack_single", "type_error_int", "value_error_int"]
    statement := "pack_single reports an item of the wrong type and a value out of range with the literal messages naming the format."
    source := "memoryobject.c:1634-1648", status := .proven
    prop := ``PackMessages, thm := some ``packMessages_proven },
  { id := "bytesobj-memoryview-getbuf-order", pyFile := memFile
    pyFns := ["memory_getbuf"]
    statement := "Each refusal of memory_getbuf with its message, in order, for every flag set, and the copy with the requested fields when none applies."
    source := "memoryobject.c:1538-1599", status := .proven
    prop := ``GetbufOrder, thm := some ``getbufOrder_proven },
  { id := "bytesobj-memoryview-getbuf-lift", pyFile := memFile
    pyFns := ["memory_getbuf"]
    statement := "A refusal changes nothing; a success counts one export and hands out the view as obj."
    source := "memoryobject.c:1601-1605", status := .proven
    prop := ``GetbufLift, thm := some ``getbufLift_proven },
  { id := "bytesobj-memoryview-copy-shape-rules", pyFile := memFile
    pyFns := ["copy_shape"]
    statement := "An element that is no int, does not fit Py_ssize_t, is not positive, or takes the product past SSIZE_MAX is refused with its own message, in that order; a good shape gives its product."
    source := "memoryobject.c:1338-1372", status := .proven
    prop := ``CopyShapeRules, thm := some ``copyShapeRules_proven },
  { id := "bytesobj-memoryview-multislice-spec", pyFile := memFile
    pyFns := ["is_multislice"]
    statement := "is_multislice is exactly a non-empty tuple of slices, and it decides between NotImplementedError and TypeError for a tuple key that is no index tuple."
    source := "memoryobject.c:2538-2553", status := .proven
    prop := ``MultisliceSpec, thm := some ``multisliceSpec_proven },
  { id := "bytesobj-memoryview-cast1d-refusals", pyFile := memFile
    pyFns := ["cast_to_1D"]
    statement := "cast_to_1D refuses a non-ASCII format, one that is no native single character, two non-byte formats and a length that is no multiple of the item size, in that order, leaving the state alone."
    source := "memoryobject.c:1275-1335", status := .proven
    prop := ``Cast1DRefusals, thm := some ``cast1DRefusals_proven },
  { id := "bytesobj-memoryview-ass-sub-rules", pyFile := memFile
    pyFns := ["memory_ass_sub"]
    statement := "m[key] = value refuses a bad format, read-only memory and deletion first, then stores through ... and () on a 0-dim view and through a full index tuple elsewhere, and refuses every other key."
    source := "memoryobject.c:2642-2743", status := .proven
    prop := ``AssSubRules, thm := some ``assSubRules_proven },
  { id := "bytesobj-memoryview-restricted-refuses", pyFile := memFile
    pyFns := ["PyMemoryView_FromObjectAndFlags", "memoryview_cast_impl", "memoryview_toreadonly_impl", "memory_getbuf", "memory_subscript"]
    statement := "A restricted view makes no new reference to the buffer: memoryview(m), cast, toreadonly, m[a:b] and __buffer__ raise ValueError and change nothing, while len(m) works."
    source := "memoryobject.c:198-210, :808, :1456, :1512, :1536, :2613", status := .proven
    prop := ``RestrictedRefuses, thm := some ``restrictedRefuses_proven },
  { id := "bytesobj-memoryview-restricted-made", pyFile := memFile
    pyFns := ["PyMemoryView_FromObjectAndFlags"]
    statement := "The view __release_buffer__ receives from a C exporter is live and restricted."
    source := "Objects/typeobject.c:10820-10833", status := .proven
    prop := ``RestrictedMade, thm := some ``restrictedMade_proven },
  { id := "bytesobj-memoryview-init-flags-bits", pyFile := memFile
    pyFns := ["init_flags"]
    statement := "A view with suboffsets is PIL and neither C nor Fortran; otherwise from two dimensions up the C and Fortran bits are the tests of PyBuffer_IsContiguous, and nothing starts released or restricted."
    source := "memoryobject.c:610-639", status := .proven
    prop := ``InitFlagsBits, thm := some ``initFlagsBits_proven },
  { id := "bytesobj-memoryview-fortran-bit", pyFile := memFile
    pyFns := ["init_flags"]
    statement := "A view with no suboffsets whose strides are the Fortran strides of its shape has the Fortran bit."
    source := "memoryobject.c:626-629; Objects/abstract.c:450-487", status := .proven
    prop := ``FortranBit, thm := some ``fortranBit_proven },
  { id := "bytesobj-memoryview-contig-getters", pyFile := memFile
    pyFns := ["memory_c_contiguous", "memory_f_contiguous", "memory_contiguous"]
    statement := "With the flags init_flags set, c_contiguous, f_contiguous and contiguous report the tests of PyBuffer_IsContiguous."
    source := "Doc/library/stdtypes.rst memoryview.c_contiguous", status := .proven
    prop := ``ContigGetters, thm := some ``contigGetters_proven },
  { id := "bytesobj-memoryview-getter-refusal", pyFile := memFile
    pyFns := ["memory_obj_get", "memory_nbytes_get", "memory_readonly_get", "memory_itemsize_get", "memory_format_get", "memory_ndim_get", "memory_shape_get", "memory_strides_get", "memory_suboffsets_get", "memory_c_contiguous", "memory_f_contiguous", "memory_contiguous"]
    statement := "Every getter of a released view raises ValueError and changes nothing."
    source := "CHECK_RELEASED, memoryobject.c:3291-3390", status := .proven
    prop := ``GetterRefusal, thm := some ``getterRefusal_proven },
  { id := "bytesobj-memoryview-int-tuple", pyFile := memFile
    pyFns := ["_IntTupleFromSsizet"]
    statement := "NULL is the empty tuple whatever the length; otherwise the first len values in order."
    source := "memoryobject.c:3268-3289", status := .proven
    prop := ``IntTupleSpec, thm := some ``intTupleSpec_proven },
  { id := "bytesobj-memoryview-clear-effect", pyFile := memFile
    pyFns := ["memory_clear"]
    statement := "With no exports memory_clear is the release and every later operation is refused; with exports it does nothing."
    source := "memoryobject.c:1171-1180", status := .proven
    prop := ``ClearEffect, thm := some ``clearEffect_proven },
  { id := "bytesobj-memoryview-repr-states", pyFile := memFile
    pyFns := ["memory_repr"]
    statement := "repr has two texts and the view own flag picks: released after release, the other before it."
    source := "memoryobject.c:2376-2383", status := .proven
    prop := ``ReprStates, thm := some ``reprStates_proven },
  { id := "bytesobj-memoryview-struct-too-long", pyFile := memFile
    pyFns := ["struct_get_unpacker", "fix_struct_error_int"]
    statement := "A repeat count past PY_SSIZE_T_MAX, or one whose item size takes the struct past it, is struct.error, which == reads as not equal."
    source := "Modules/_struct.c:1655-1660, :1703-1705, :1769-1772", status := .proven
    prop := ``StructSizeTooLong, thm := some ``structSizeTooLong_proven },
  { id := "bytesobj-memoryview-reentrant-release", pyFile := memFile
    pyFns := ["mbuf_release", "_memory_release", "memory_releasebuf"]
    statement := "When the hook of the last view of a buffer releases that view or a released one, nothing happens; when it releases the view the buffer gives an export back to, BufferError is swallowed and the export goes back."
    source := "memoryobject.c:106-117, :1108-1120; Objects/typeobject.c:10800-10850", status := .proven
    prop := ``ReentrantRelease, thm := some ``reentrantRelease_proven },
  { id := "bytesobj-memoryview-null-reachable", pyFile := memFile
    pyFns := ["memoryiter_next"]
    statement := "A stored pointer of 0 with suboffset 0 is NULL, which IterNull is about, and a positive suboffset never is."
    source := "memoryobject.c:3508-3510", status := .proven
    prop := ``NullReachable, thm := some ``nullReachable_proven },
  { id := "bytesobj-memoryview-pylong-failures", pyFile := "Objects/memoryobject.c", pyFns := ["pylong_as_ld", "pylong_as_lu", "pylong_as_lld", "pylong_as_llu", "pylong_as_zd", "pylong_as_zu"]
    statement := "Each pylong_as_* uses its own C conversion on the result of _PyNumber_Index, and for every __index__ that raises or returns a non-int it passes that failure up after the callback ran; an object with no __index__ raises TypeError without any callback."
    source := "memoryobject.c:1672-1760; Objects/abstract.c:1402-1440", status := .proven
    prop := ``PylongFailures, thm := some ``pylongFailures_proven },
  { id := "bytesobj-memoryview-fix-error-int", pyFile := "Objects/memoryobject.c", pyFns := ["fix_error_int", "type_error_int", "value_error_int"]
    statement := "fix_error_int turns TypeError into the invalid-type message and ValueError and OverflowError into the invalid-value message naming the format, and lets every other exception through unchanged."
    source := "memoryobject.c:1650-1665", status := .proven
    prop := ``FixErrorInt, thm := some ``fixErrorInt_proven },
  { id := "bytesobj-memoryview-pack-failures", pyFile := "Objects/memoryobject.c", pyFns := ["pack_single"]
    statement := "For every integer and float format, when the item's __index__ or __float__ raises or returns the wrong type, pack_single writes nothing and raises what fix_error_int makes of it; for format ? a failing __bool__ keeps its original exception."
    source := "memoryobject.c:1874-2026, the comment at :1988", status := .proven
    prop := ``PackFailures, thm := some ``packFailures_proven },
  { id := "bytesobj-memoryview-key-failures", pyFile := "Objects/memoryobject.c", pyFns := ["memory_subscript", "memory_ass_sub"]
    statement := "A failing __index__ in m[k] or m[k] = v, on a live view that is not 0-dimensional, raises that failure, and the assignment writes nothing."
    source := "memoryobject.c:2606-2609, :2684-2687", status := .proven
    prop := ``KeyFailures, thm := some ``keyFailures_proven },
  { id := "bytesobj-memoryview-tuple-failures", pyFile := "Objects/memoryobject.c", pyFns := ["ptr_from_tuple"]
    statement := "ptr_from_tuple rejects a tuple longer than ndim before any __index__ runs, and passes up a raising __index__."
    source := "memoryobject.c:2423-2448", status := .proven
    prop := ``TupleFailures, thm := some ``tupleFailures_proven },
  { id := "bytesobj-memoryview-buffer-failures", pyFile := "Objects/memoryobject.c", pyFns := ["memoryview_impl", "PyMemoryView_FromObject", "PyMemoryView_FromObjectAndFlags", "memoryview__from_flags_impl", "_PyManagedBuffer_FromObject"]
    statement := "A __buffer__ that raises or returns a non-memoryview makes memoryview(x), memoryview._from_flags(x, flags) and PyObject_GetBuffer raise that failure, after its callback ran, leaving the byte store alone."
    source := "memoryobject.c:801-825; Objects/typeobject.c:10718-10719", status := .proven
    prop := ``BufferFailures, thm := some ``bufferFailures_proven },
  { id := "bytesobj-memoryview-format-native", pyFile := memFile
    pyFns := ["get_native_fmtchar", "get_native_fmtstr", "memoryview_cast_impl"]
    statement := "For every string, get_native_fmtchar accepts it exactly when get_native_fmtstr does, the two name the same character, and its size is the size of that code in struct's native table."
    source := "memoryobject.c:1316 (NOT_REACHED comment), :1297 (error message); struct native table", status := .proven
    prop := ``NativeFormatAgree, thm := some ``nativeFormatAgree_proven },
  { id := "bytesobj-memoryview-cast-format-embedded-nul", pyFile := memFile
    pyFns := ["cast_to_1D", "get_native_fmtchar", "get_native_fmtstr"]
    statement := "memoryview.cast accepts only a format of the form [@]c."
    source := "error message at memoryobject.c:1297", status := .refuted
    prop := ``CastWholeFormat, thm := some ``castWholeFormat_refuted
    bug := some "bytesobj-memoryview-cast-format-embedded-nul" },
  { id := "bytesobj-memoryview-cast-1d", pyFile := memFile
    pyFns := ["memoryview_cast_impl", "cast_to_1D", "mbuf_add_incomplete_view", "memory_alloc", "init_shared_values", "zero_in_shape"]
    statement := "m.cast(format) on a live C-contiguous view, with a native format, when one side has byte size and the length divides, gives a new 1-D view registered with the same managed buffer, on the same memory, with shape * itemsize == len, and m unchanged."
    source := "memoryobject.c:1426-1437 ('All casts must result in views that will have the exact byte size of the original input'); Doc/library/stdtypes.rst memoryview.cast", status := .proven
    prop := ``Cast1DSpec, thm := some ``cast1DSpec_proven },
  { id := "bytesobj-memoryview-cast-nd", pyFile := memFile
    pyFns := ["cast_to_ND", "copy_shape", "init_strides_from_shape", "init_flags"]
    statement := "If cast_to_ND succeeds, the view has the given positive shape, C strides, product(shape) * itemsize == len, and reports c_contiguous; for every shape, the strides init_strides_from_shape computes are C-contiguous."
    source := "memoryobject.c:1374-1376 ('The result array will be C-contiguous')", status := .proven
    prop := ``CastNDSpec, thm := some ``castNDSpec_proven },
  { id := "bytesobj-memoryview-cast-rejections", pyFile := memFile
    pyFns := ["memoryview_cast_impl", "zero_in_shape"]
    statement := "cast refuses a view that is not C-contiguous, then a view with a zero in its shape when a shape is given or ndim != 1, leaving the state alone."
    source := "memoryobject.c:1458-1467; Doc/library/stdtypes.rst memoryview.cast", status := .proven
    prop := ``CastRejections, thm := some ``castRejections_proven },
  { id := "bytesobj-memoryview-pack-unpack-int", pyFile := memFile
    pyFns := ["pack_single", "unpack_single", "pylong_as_ld", "pylong_as_lu", "pylong_as_lld", "pylong_as_llu",
      "pylong_as_zd", "pylong_as_zu", "value_error_int", "fix_error_int"]
    statement := "For every native integer format and every int: an int in the format's range is stored and read back unchanged, with no other byte changed; any other int raises ValueError('memoryview: invalid value for format ...') and writes nothing."
    source := "invariant: m[i] = v; m[i] == v; memoryobject.c:1628-1633", status := .proven
    prop := ``PackUnpackInt, thm := some ``packUnpackInt_proven
    notes := "Float formats are in the model and the difftest with exact conversions; their round trips are open entries." },
  { id := "bytesobj-memoryview-pack-type-errors", pyFile := memFile
    pyFns := ["pack_single", "type_error_int", "value_error_int", "fix_error_int"]
    statement := "pack_single on a str in an integer format, on a non-bytes in format c, and on bytes of another length in format c raises the documented TypeError or ValueError and writes nothing."
    source := "memoryobject.c:1628-1633, :1995-1999", status := .proven
    prop := ``PackTypeErrors, thm := some ``packTypeErrors_proven },
  { id := "bytesobj-memoryview-setitem-c-released", pyFile := memFile
    pyFns := ["pack_single", "memory_ass_sub"]
    statement := "If key.__index__ releases m, m[key] = v writes nothing."
    source := "gh-92888, Lib/test/test_memoryview.py test_use_released_memory; Doc/library/stdtypes.rst memoryview.release", status := .refuted
    prop := ``ReleasedKeyNoWrite, thm := some ``releasedKeyNoWrite_refuted
    bug := some "bytesobj-memoryview-setitem-c-released" },
  { id := "bytesobj-memoryview-released-key-not-c", pyFile := memFile
    pyFns := ["pack_single", "memory_ass_sub"]
    statement := "For every format but c, every item and every conversion callback: if key.__index__ releases m, m[key] = v writes nothing."
    source := "gh-92888", status := .proven
    prop := ``ReleasedKeyNoWriteNotC, thm := some ``releasedKeyNoWriteNotC_proven },
  { id := "bytesobj-memoryview-release-rules", pyFile := memFile
    pyFns := ["memoryview_release_impl", "_memory_release", "get_exports", "memory_exit", "mbuf_release"]
    statement := "release() with exported buffers raises BufferError('memoryview has N exported buffer(s)') and changes nothing; with none it releases the view, decrements the managed buffer's count, the managed buffer is released exactly when the count reaches zero, and a second call changes nothing."
    source := "Doc/library/stdtypes.rst memoryview.release; memoryobject.c:1104-1148", status := .proven
    prop := ``ReleaseRules, thm := some ``releaseRules_proven },
  { id := "bytesobj-memoryview-released-forbids", pyFile := memFile
    pyFns := ["memory_enter", "memoryview_tolist_impl", "memoryview_tobytes_impl", "memoryview_hex_impl",
      "memoryview_cast_impl", "memoryview_toreadonly_impl", "memory_subscript", "memory_ass_sub", "memory_length",
      "memory_iter", "memoryview_count_impl", "memoryview_index_impl", "memory_getbuf",
      "PyMemoryView_FromObjectAndFlags"]
    statement := "Once the base is inaccessible, every operation raises ValueError('operation forbidden on released memoryview object') before touching the buffer, for all arguments."
    source := "Doc/library/stdtypes.rst memoryview.release: 'any further operation on the view raises a ValueError'", status := .proven
    prop := ``ReleasedForbids, thm := some ``releasedForbids_proven },
  { id := "bytesobj-memoryview-getters", pyFile := memFile
    pyFns := ["memory_obj_get", "memory_nbytes_get", "memory_format_get", "memory_itemsize_get", "memory_shape_get",
      "memory_strides_get", "memory_suboffsets_get", "memory_readonly_get", "memory_ndim_get", "memory_c_contiguous",
      "memory_f_contiguous", "memory_contiguous", "_IntTupleFromSsizet"]
    statement := "For a live view each attribute is the field it names, a NULL array is an empty tuple, and the three contiguity attributes read the flags."
    source := "Doc/library/stdtypes.rst memoryview attributes", status := .proven
    prop := ``GettersReport, thm := some ``gettersReport_proven },
  { id := "bytesobj-memoryview-eq-released-by-buffer", pyFile := memFile
    pyFns := ["memory_richcompare"]
    statement := "A view released while == obtains the other operand's buffer compares by identity, so unequal."
    source := "memoryobject.c:3113-3116; Doc/library/stdtypes.rst memoryview.release", status := .refuted
    prop := ``CmpReleasedIdentity, thm := some ``cmpReleasedIdentity_refuted
    bug := some "bytesobj-memoryview-eq-released-by-buffer" },
  { id := "bytesobj-memoryview-empty-step-not-contiguous", pyFile := memFile
    pyFns := ["init_flags"]
    statement := "For every 1-D view, m.c_contiguous is what PyBuffer_IsContiguous(view, 'C') says."
    source := "Objects/abstract.c:498-499; the name of MV_CONTIGUOUS_NDIM1 ('Fast contiguity test')", status := .refuted
    prop := ``Ndim1ContigAgree, thm := some ``ndim1ContigAgree_refuted
    bug := some "bytesobj-memoryview-empty-step-not-contiguous" },
  { id := "bytesobj-memoryview-contig-nonempty", pyFile := memFile
    pyFns := ["init_flags"]
    statement := "For every non-empty 1-D view, c_contiguous and f_contiguous are what PyBuffer_IsContiguous says."
    source := "Fast path against general path", status := .proven
    prop := ``Ndim1ContigNonempty, thm := some ``ndim1ContigNonempty_proven },
  { id := "bytesobj-memoryview-buffer-noformat-itemsize", pyFile := memFile
    pyFns := ["_PyMemoryView_FromBufferProc", "memory_getbuf", "init_shared_values"]
    statement := "For every view of a native format and all flags, m.__buffer__(flags) has a format whose size is the view's itemsize."
    source := "Doc/library/stdtypes.rst memoryview.itemsize", status := .refuted
    prop := ``BufferKeepsItemsize, thm := some ``bufferKeepsItemsize_refuted
    bug := some "bytesobj-memoryview-buffer-noformat-itemsize" },
  { id := "bytesobj-memoryview-slice-stride-overflow", pyFile := memFile
    pyFns := ["init_slice"]
    statement := "The stride of m[::k] is m.strides[0] * k, for every step, with no Py_ssize_t overflow."
    source := "invariant: no signed overflow in C", status := .refuted
    prop := ``SliceStrideExact, thm := some ``sliceStrideExact_refuted
    bug := some "bytesobj-memoryview-slice-stride-overflow" },
  { id := "bytesobj-memoryview-slice-items", pyFile := memFile
    pyFns := ["memory_subscript", "init_slice", "init_len", "mbuf_add_view", "init_shape_strides", "init_suboffsets"]
    statement := "For every slice with a non-zero step and every view of any number of dimensions, m[s] slices dimension 0: a new view on the same memory whose k-th row is row range(*s.indices(n))[k] of m, whose length is that of the range, and nbytes is len * itemsize; every position is in [0, n)."
    source := "slice semantics; list agreement (RangeSlice.ListSliceIndices)", status := .proven
    prop := ``SliceItems, thm := some ``sliceItems_proven },
  { id := "bytesobj-memoryview-index-item", pyFile := memFile
    pyFns := ["memory_subscript", "memory_item", "ptr_from_index", "lookup_dimension", "adjust_fmt"]
    statement := "m[i] of a 1-D view, for every int i: IndexError outside Py_ssize_t, the item at buf + stride * position for -n <= i < n, IndexError('index out of bounds on dimension 1') otherwise; nothing changes."
    source := "Doc/library/stdtypes.rst memoryview; sequence indexing", status := .proven
    prop := ``IndexItem, thm := some ``indexItem_proven },
  { id := "bytesobj-memoryview-ass-item-int", pyFile := memFile
    pyFns := ["memory_ass_sub", "ptr_from_index", "lookup_dimension", "pack_single"]
    statement := "m[i] = v; m[i] gives v back for a writable 1-D view of a native integer format, for every in-range index and value, and no other byte changes."
    source := "invariant: item assignment", status := .proven
    prop := ``AssItemInt, thm := some ``assItemInt_proven },
  { id := "bytesobj-memoryview-key-rejections", pyFile := memFile
    pyFns := ["memory_subscript", "is_multislice", "is_multiindex", "memory_item_multi", "memory_item"]
    statement := "A 0-dim view takes only () and ...; m[i] on two or more dimensions, a tuple of slices, a short tuple of indices, and a key that is neither index nor slice are refused with their exact messages."
    source := "memoryobject.c:2573-2578, :2588-2639", status := .proven
    prop := ``KeyRejections, thm := some ``keyRejections_proven },
  { id := "bytesobj-memoryview-tobytes-c", pyFile := memFile
    pyFns := ["buffer_to_contiguous", "copy_buffer", "copy_rec", "copy_base", "equiv_structure", "equiv_format",
      "equiv_shape", "last_dim_is_contiguous", "init_strides_from_shape"]
    statement := "For every view with full information, of any number of dimensions, strides and suboffsets, buffer_to_contiguous in order C gives the items in row-major order, itemsize bytes each, at the addresses tolist reads."
    source := "Doc/library/stdtypes.rst memoryview.tobytes", status := .proven
    prop := ``TobytesC, thm := some ``tobytesC_proven },
  { id := "bytesobj-memoryview-tolist-flat", pyFile := memFile
    pyFns := ["memoryview_tolist_impl", "tolist_base", "tolist_rec", "unpack_single"]
    statement := "m.tolist() for every view of a native format, of any dimension, shape, strides and suboffsets: its flattened items are the native items at the addresses of the row-major walk."
    source := "Doc/library/stdtypes.rst memoryview.tolist", status := .proven
    prop := ``TolistFlat, thm := some ``tolistFlat_proven },
  { id := "bytesobj-memoryview-tobytes-1d", pyFile := memFile
    pyFns := ["memoryview_tobytes_impl", "PyBuffer_ToContiguous"]
    statement := "m.tobytes() of a 1-D view, for every stride, is the items in order: the memcpy branch and the copy branch of PyBuffer_ToContiguous give the same bytes."
    source := "Fast path against general path; Doc/library/stdtypes.rst memoryview.tobytes", status := .proven
    prop := ``Tobytes1D, thm := some ``tobytes1D_proven },
  { id := "bytesobj-memoryview-cmp-eq-ne", pyFile := memFile
    pyFns := ["memory_richcompare"]
    statement := "!= is the negation of == in every state, with the same effects; an ordering is NotImplemented with no effect."
    source := "Doc/reference/datamodel.rst __ne__; memoryobject.c:3109-3110, :3180-3190", status := .proven
    prop := ``CmpEqNe, thm := some ``cmpEqNe_proven },
  { id := "bytesobj-memoryview-cmp-special", pyFile := memFile
    pyFns := ["memory_richcompare"]
    statement := "A released view compares by identity, and a non-exporter gives NotImplemented."
    source := "memoryobject.c:3113-3130", status := .proven
    prop := ``CmpSpecialCases, thm := some ``cmpSpecialCases_proven },
  { id := "bytesobj-memoryview-cmp-reflexive", pyFile := memFile
    pyFns := ["memory_richcompare", "unpack_cmp", "cmp_base", "cmp_rec", "equiv_shape", "get_native_fmtchar"]
    statement := "m == m for every view of a native format other than f, d, e, of any shape, strides and suboffsets."
    source := "Doc/library/stdtypes.rst memoryview.__eq__", status := .proven
    prop := ``CmpReflexive, thm := some ``cmpReflexive_proven },
  { id := "bytesobj-memoryview-cmp-fast-struct", pyFile := memFile
    pyFns := ["unpack_cmp", "struct_unpack_cmp", "struct_unpack_single", "struct_get_unpacker"]
    statement := "For every native format and all memory, the fast switch of unpack_cmp gives what comparing the values unpacked by struct gives."
    source := "memoryobject.c:2958-2963 (fast path only for speed)", status := .proven
    prop := ``CmpFastStruct, thm := some ``cmpFastStruct_proven },
  { id := "bytesobj-memoryview-hex-groups", pyFile := memFile
    pyFns := ["memoryview_hex_impl"]
    statement := "hex() is two lower-case digits per byte, and with a separator that is not a hex digit, removing the separators gives the same text, for every group size of either sign."
    source := "memoryview.hex docstring, memoryobject.c:2314-2335", status := .proven
    prop := ``HexGroups, thm := some ``hexGroups_proven },
  { id := "bytesobj-memoryview-hex-tobytes", pyFile := memFile
    pyFns := ["memoryview_hex_impl"]
    statement := "m.hex(sep, n) is the hex of m.tobytes(), for every view, contiguous or not: the two paths of memoryview_hex_impl are one behaviour."
    source := "Fast path against general path", status := .proven
    prop := ``HexIsTobytes, thm := some ``hexIsTobytes_proven },
  { id := "bytesobj-memoryview-clear-release", pyFile := memFile
    pyFns := ["memory_clear"]
    statement := "A view in a reference cycle is released like any other if it has no exports and left alone if it has."
    source := "memoryobject.c:178-179, :1171-1180", status := .proven
    prop := ``ClearIsRelease, thm := some ``clearIsRelease_proven },
  { id := "bytesobj-memoryview-repr", pyFile := memFile
    pyFns := ["memory_repr"]
    statement := "repr says whether the view is released."
    source := "memoryobject.c:2375-2383", status := .proven
    prop := ``ReprReleased, thm := some ``reprReleased_proven },
  { id := "bytesobj-memoryview-fortran-strides", pyFile := memFile
    pyFns := ["init_fortran_strides_from_shape"]
    statement := "For every shape, the strides init_fortran_strides_from_shape computes are Fortran-contiguous."
    source := "memoryobject.c:479-490", status := .proven
    prop := ``FortranStrides, thm := some ``fortranStrides_proven },
  { id := "bytesobj-memoryview-toreadonly", pyFile := memFile
    pyFns := ["memoryview_toreadonly_impl", "mbuf_add_view"]
    statement := "m.toreadonly() is a new read-only view of the same buffer; m is unchanged and the managed buffer's count goes up."
    source := "Doc/library/stdtypes.rst memoryview.toreadonly", status := .proven
    prop := ``ToReadonlySpec, thm := some ``toReadonlySpec_proven },
  { id := "bytesobj-memoryview-new-view", pyFile := memFile
    pyFns := ["PyMemoryView_FromObjectAndFlags", "PyMemoryView_FromObject", "memoryview_impl",
      "memoryview__from_flags_impl", "mbuf_add_view"]
    statement := "memoryview(m) shares m's managed buffer; a non-buffer raises TypeError naming its type."
    source := "memoryobject.c:796-825", status := .proven
    prop := ``NewViewRules, thm := some ``newViewRules_proven },
  { id := "bytesobj-memoryview-iter", pyFile := memFile
    pyFns := ["memory_iter", "memoryiter_next", "memory_length"]
    statement := "list(m) is m.tolist() for every 1-D view of a native format, every stride, with or without a suboffset."
    source := "Doc/library/stdtypes.rst memoryview", status := .proven
    prop := ``IterYields, thm := some ``iterYields_proven },
  { id := "bytesobj-memoryview-count", pyFile := memFile
    pyFns := ["memoryview_count_impl", "memoryiter_next", "memory_iter"]
    statement := "m.count(x) is m.tolist().count(x) for every 1-D view of a native format, every x with no Python __eq__ and every stride, with or without a suboffset."
    source := "Doc/library/stdtypes.rst memoryview.count", status := .proven
    prop := ``CountIsList, thm := some ``countIsList_proven },
  { id := "bytesobj-memoryview-index", pyFile := memFile
    pyFns := ["memoryview_index_impl", "memory_item"]
    statement := "m.index(x, start, stop) searches exactly the clipped range and returns the first match or raises ValueError, like list.index on tolist()."
    source := "Doc/library/stdtypes.rst memoryview.index", status := .proven
    prop := ``IndexIsSearch, thm := some ``indexIsSearch_proven },
  { id := "bytesobj-memoryview-hash", pyFile := memFile
    pyFns := ["memory_hash"]
    statement := "hash(m) == hash(m.tobytes()) for every read-only view of a byte format, of any number of dimensions, strides and suboffsets, and the value is cached across release()."
    source := "Doc/library/stdtypes.rst memoryview.__hash__", status := .proven
    prop := ``HashIsTobytes, thm := some ``hashIsTobytes_proven },
  { id := "bytesobj-memoryview-hash-rejections", pyFile := memFile
    pyFns := ["memory_hash"]
    statement := "hash refuses a writable view, then a non-byte format, with their messages."
    source := "memoryobject.c:3217-3227", status := .proven
    prop := ``HashRejections, thm := some ``hashRejections_proven },
  { id := "bytesobj-memoryview-getbuf", pyFile := memFile
    pyFns := ["memory_getbuf", "memory_releasebuf"]
    statement := "A failed buffer request changes nothing; a successful one adds one export and hands out the same memory with obj set to the view, format NULL without PyBUF_FORMAT, 1-D with no shape without PyBUF_ND; releasing restores the view; a write request on a read-only view is refused first."
    source := "memoryobject.c:1528-1615; PEP 3118", status := .proven
    prop := ``GetbufRules, thm := some ``getbufRules_proven },
  { id := "bytesobj-memoryview-new-exporter", pyFile := memFile
    pyFns := ["mbuf_alloc", "_PyManagedBuffer_FromObject", "PyMemoryView_FromObjectAndFlags", "PyMemoryView_FromObject",
      "memoryview_impl", "mbuf_add_view"]
    statement := "memoryview(x) of an exporter of any number of dimensions makes a new managed buffer with one registered view on x's buffer."
    source := "memoryobject.c:31-68", status := .proven
    prop := ``NewFromExporter, thm := some ``newFromExporter_proven },
  { id := "bytesobj-memoryview-from-memory", pyFile := memFile
    pyFns := ["PyMemoryView_FromMemory", "PyMemoryView_FromBuffer"]
    statement := "PyMemoryView_FromMemory gives a byte view with no exporter, read-only or writable as asked, C-contiguous; PyMemoryView_FromBuffer refuses a NULL buf."
    source := "memoryobject.c:737-794; Doc/c-api/memoryview.rst", status := .proven
    prop := ``FromMemorySpec, thm := some ``fromMemorySpec_proven },
  { id := "bytesobj-memoryview-cmp-bad-format", pyFile := memFile
    pyFns := ["fix_struct_error_int", "memory_richcompare", "struct_get_unpacker"]
    statement := "A format struct rejects compares unequal with no exception, when the shapes are equivalent."
    source := "memoryobject.c:2925 ('StructError: invalid or unknown format -> not equal')", status := .proven
    prop := ``CmpBadFormat, thm := some ``cmpBadFormat_proven },
  { id := "bytesobj-memoryview-tuple-item", pyFile := memFile
    pyFns := ["ptr_from_tuple", "memory_item_multi", "memory_subscript", "is_multiindex", "lookup_dimension"]
    statement := "m[i, j, ...] with one index per dimension, each -n <= i < n, is the item of m.tolist() at those positions, a negative index counting from the end, for every view of a native format, any number of dimensions, any strides and suboffsets."
    source := "memoryobject.c:2573-2578; Doc/library/stdtypes.rst memoryview", status := .proven
    prop := ``TupleItem, thm := some ``tupleItem_proven },
  { id := "bytesobj-memoryview-copy-single", pyFile := memFile
    pyFns := ["copy_single", "copy_base", "equiv_structure", "equiv_format", "equiv_shape", "last_dim_is_contiguous",
      "memory_ass_sub"]
    statement := "After copy_single, each item of the destination holds what the corresponding item of the source held before the copy, in either branch of copy_base, also when the views overlap."
    source := "memoryobject.c:341-370; Doc/library/stdtypes.rst (memoryview slice assignment)", status := .proven
    prop := ``CopySingleSpec, thm := some ``copySingleSpec_proven },
  { id := "bytesobj-memoryview-get-contiguous", pyFile := memFile
    pyFns := ["PyMemoryView_GetContiguous", "PyMemoryView_FromObject"]
    statement := "PyMemoryView_GetContiguous refuses a write request on a read-only view and on a non-contiguous view with BufferError, and returns a view on the same memory when it is already contiguous in the requested order."
    source := "memoryobject.c:948-964 (comment)", status := .proven
    prop := ``GetContiguousRules, thm := some ``getContiguousRules_proven },
  { id := "bytesobj-memoryview-contig-copy", pyFile := memFile
    pyFns := ["memory_from_contiguous_copy", "mbuf_copy_format", "mbuf_add_incomplete_view", "copy_buffer", "copy_rec"]
    statement := "memory_from_contiguous_copy in order C gives a new view over a new bytes object with the source's shape and format, C strides, no suboffsets, holding the source's items in row-major order."
    source := "memoryobject.c:948-964: 'tolist(input) == tolist(output)'", status := .proven
    prop := ``FromContigCopy, thm := some ``fromContigCopy_proven },
  { id := "bytesobj-memoryview-from-buffer", pyFile := memFile
    pyFns := ["PyMemoryView_FromBuffer", "init_shape_strides", "init_shared_values", "mbuf_add_view"]
    statement := "PyMemoryView_FromBuffer on a Py_buffer with only buf, len and itemsize reconstructs a 1-D view of len / itemsize items, stride itemsize, format B, no exporter."
    source := "memoryobject.c:764-768", status := .proven
    prop := ``FromBufferReconstructs, thm := some ``fromBufferReconstructs_proven },
  { id := "bytesobj-memoryview-tobytes-order", pyFile := memFile
    pyFns := ["memoryview_tobytes_impl"]
    statement := "tobytes(None) is tobytes('C'), and any order but C, F, A raises ValueError('order must be 'C', 'F' or 'A')."
    source := "memoryview.tobytes docstring, memoryobject.c:2263-2276", status := .proven
    prop := ``TobytesOrderArg, thm := some ``tobytesOrderArg_proven },
  { id := "bytesobj-memoryview-dealloc-weakrefs", pyFile := memFile
    pyFns := ["memory_dealloc"]
    statement := "memory_dealloc releases the view first; only then does PyObject_ClearWeakRefs run a weakref callback, on a view already released, and a release the callback asks for of a view with exports is refused."
    source := "memoryobject.c:1150-1161", status := .proven
    prop := ``DeallocRules, thm := some ``deallocRules_proven },
  { id := "bytesobj-memoryview-dealloc-on-fail", pyFile := memFile
    pyFns := ["mbuf_dealloc", "PyMemoryView_FromObjectAndFlags", "mbuf_add_view"]
    statement := "When mbuf_add_view refuses a buffer of more than 64 dimensions, memoryview(x) raises ValueError, and mbuf_dealloc releases the master that no view ever kept, running __release_buffer__."
    source := "memoryobject.c:120-128, :811-819", status := .proven
    prop := ``MbufDeallocOnFail, thm := some ``mbufDeallocOnFail_proven },
  { id := "bytesobj-memoryview-mbuf-release", pyFile := memFile
    pyFns := ["mbuf_release", "mbuf_clear"]
    statement := "The first release of a managed buffer marks it and gives back the master, running __release_buffer__ or taking back an export of the view it came from; later releases do nothing."
    source := "memoryobject.c:107-117, :139-145", status := .proven
    prop := ``MbufReleaseRules, thm := some ``mbufReleaseRules_proven },
  { id := "bytesobj-memoryview-hex-holds-export", pyFile := memFile
    pyFns := ["memoryview_hex_impl"]
    statement := "With a sep whose __len__ calls self.release(), hex raises, and a contiguous view refuses the release because it holds an export over the call, while a non-contiguous view, hexing a private copy, is released."
    source := "memoryobject.c:2352-2354, gh-143195", status := .proven
    prop := ``HexHoldsExport, thm := some ``hexHoldsExport_proven },
  { id := "bytesobj-memoryview-hash-holds-export", pyFile := memFile
    pyFns := ["memory_hash"]
    statement := "memory_hash holds an export around PyObject_Hash: an exporter __hash__ calling self.release() is refused, one that raises passes its exception with no effect and no cached hash, one that releases another view succeeds."
    source := "memoryobject.c:3231-3233, gh-142664", status := .proven
    prop := ``HashHoldsExport, thm := some ``hashHoldsExport_proven },
  { id := "bytesobj-memoryview-compare-releases", pyFile := memFile
    pyFns := ["memory_richcompare"]
    statement := "v == w releases w's buffer after the result is known: the result is the comparison of the buffers even when __release_buffer__ releases v, and that release has happened when == returns."
    source := "memoryobject.c:3192-3199", status := .proven
    prop := ``CompareReleases, thm := some ``compareReleases_proven },
  { id := "bytesobj-memoryview-eq-failures", pyFile := memFile
    pyFns := ["memoryview_count_impl", "memoryview_index_impl"]
    statement := "An exception from __eq__ passes out of count and index at once; an __eq__ that calls self.release() succeeds, and the next step raises the released error, except on a view of one item, where count returns."
    source := "memoryobject.c:2797-2816, :2872-2895", status := .proven
    prop := ``EqFailures, thm := some ``eqFailures_proven },
  { id := "bytesobj-memoryview-slice-tolist", pyFile := memFile
    pyFns := ["memory_subscript", "init_slice", "init_len"]
    statement := "m[s].tolist() is m.tolist()[s] for a view of any number of dimensions, native format, strides and suboffsets, and every slice with a non-zero step."
    source := "Doc/library/stdtypes.rst memoryview; memoryobject.c:2509-2530, :2614-2628", status := .proven
    prop := ``SliceTolist, thm := some ``sliceTolist_proven },
  { id := "bytesobj-memoryview-tuple-refusals", pyFile := memFile
    pyFns := ["ptr_from_tuple", "memory_item_multi", "lookup_dimension"]
    statement := "m[i, j, ...] with more indices than dimensions is a TypeError before any index is looked at; otherwise the first index out of bounds is an IndexError naming its dimension."
    source := "memoryobject.c:2424-2448", status := .proven
    prop := ``TupleRefusals, thm := some ``tupleRefusals_proven },
  { id := "bytesobj-memoryview-zero-dim", pyFile := memFile
    pyFns := ["memoryview_tolist_impl", "memory_subscript"]
    statement := "On a 0-dim view m.tolist() is one item and not a list, and m[()] is that same item, the native item at buf."
    source := "memoryobject.c:2248-2250, :2592-2596", status := .proven
    prop := ``ZeroDimItem, thm := some ``zeroDimItem_proven },
  { id := "bytesobj-memoryview-hash-view-exporter", pyFile := memFile
    pyFns := ["memory_hash"]
    statement := "When the exporter is another memoryview, hash runs memory_hash on it under the held export: a cached hash lets this view go on, and a view that cannot be hashed passes its ValueError up with no effect."
    source := "memoryobject.c:3228-3237", status := .proven
    prop := ``HashViewExporter, thm := some ``hashViewExporter_proven },
  { id := "bytesobj-memoryview-cast-shape", pyFile := memFile
    pyFns := ["memoryview_cast_impl", "cast_to_ND", "cast_to_1D"]
    statement := "memoryview.cast(format, shape) gives a new view of the same buffer and byte size, with ndim == len(shape), the given shape, the new format and C strides, and m unchanged."
    source := "memoryobject.c:1377-1411, :1447-1499", status := .proven
    prop := ``CastShapeSpec, thm := some ``castShapeSpec_proven },
  { id := "bytesobj-memoryview-context", pyFile := memFile
    pyFns := ["memory_enter", "memory_exit"]
    statement := "__enter__ returns the view itself and a released view refuses; __exit__ is release, so with no exports the view is released and a second __enter__ refuses."
    source := "memoryobject.c:1182-1193", status := .proven
    prop := ``ContextRules, thm := some ``contextRules_proven },
  { id := "bytesobj-memoryview-get-contiguous-copy", pyFile := memFile
    pyFns := ["PyMemoryView_GetContiguous", "memory_from_contiguous_copy"]
    statement := "A read request in C order on a view that is not contiguous gives a new view over a new bytes object, with C strides and no suboffsets, holding the view's items in row-major order, and the temporary view is dropped."
    source := "memoryobject.c:889-946, :998-1000", status := .proven
    prop := ``GetContiguousCopy, thm := some ``getContiguousCopy_proven },
  { id := "bytesobj-memoryview-ass-slice", pyFile := memFile
    pyFns := ["memory_ass_sub", "copy_single", "init_slice"]
    statement := "m[s] = x on a 1-D writable view puts item k of x at item range(*s.indices(n))[k] of m, for every slice with a non-zero step and every x of the same structure, also when they overlap, and gives x's buffer back."
    source := "memoryobject.c:2694-2719", status := .proven
    prop := ``AssSliceSpec, thm := some ``assSliceSpec_proven },
  { id := "bytesobj-memoryview-init-arrays", pyFile := memFile
    pyFns := ["init_shape_strides", "init_suboffsets"]
    statement := "A view copies its arrays: none for 0 dimensions, a missing 1-D shape or stride rebuilt from len and itemsize, N-D arrays as given, and missing N-D strides filled in in C order, as the buffer protocol defines NULL strides."
    source := "memoryobject.c:555-593", status := .proven
    prop := ``InitArrays, thm := some ``initArrays_proven },
  { id := "bytesobj-memoryview-from-buffer-full", pyFile := memFile
    pyFns := ["PyMemoryView_FromBuffer", "mbuf_add_view"]
    statement := "PyMemoryView_FromBuffer on a Py_buffer with all its arrays, of any number of dimensions, gives that buffer with no exporter, as the only view of a new managed buffer."
    source := "memoryobject.c:769-794", status := .proven
    prop := ``FromBufferFull, thm := some ``fromBufferFull_proven },
  { id := "bytesobj-memoryview-from-flags-exporter", pyFile := memFile
    pyFns := ["memoryview__from_flags_impl", "_PyManagedBuffer_FromObject"]
    statement := "memoryview._from_flags gives flags to an exporter: a writable request on a read-only exporter is refused with no view made, and without PyBUF_FORMAT the master has no format and the view reads B."
    source := "memoryobject.c:88-104, :550, :1031-1036", status := .proven
    prop := ``FromFlagsExporter, thm := some ``fromFlagsExporter_proven },
  { id := "bytesobj-memoryview-buffer-proc", pyFile := memFile
    pyFns := ["_PyMemoryView_FromBufferProc"]
    statement := "For every buffer proc: one that fails passes its exception up and releases nothing, one that succeeds gives a new view on a new managed buffer, and a buffer mbuf_add_view refuses is released."
    source := "memoryobject.c:831-848", status := .proven
    prop := ``BufferProcRules, thm := some ``bufferProcRules_proven },
  { id := "bytesobj-memoryview-fortran-copy", pyFile := memFile
    pyFns := ["buffer_to_contiguous", "copy_buffer", "copy_rec", "copy_base", "init_fortran_strides_from_shape"]
    statement := "buffer_to_contiguous in order F, for every view of any number of dimensions, strides and suboffsets, leaves each item at its place in column-major order, the first index running fastest."
    source := "Doc/library/stdtypes.rst memoryview.tobytes; memoryobject.c:374-401, :495-534", status := .proven
    prop := ``FortranCopy, thm := some ``fortranCopy_proven },
  { id := "bytesobj-memoryview-tobytes-orders", pyFile := memFile
    pyFns := ["memoryview_tobytes_impl", "PyBuffer_ToContiguous"]
    statement := "m.tobytes(order) for every live view of any shape: C and no order are row-major, F is column-major, A is the memory if it is contiguous in either order and row-major otherwise, and any other length is refused."
    source := "memoryobject.c:1048-1087, :2278-2312", status := .proven
    prop := ``TobytesOrders, thm := some ``tobytesOrders_proven },
  { id := "bytesobj-memoryview-from-contig-copy-f", pyFile := memFile
    pyFns := ["memory_from_contiguous_copy"]
    statement := "memory_from_contiguous_copy in order F gives a new view over a new bytes object with the source's shape and format, Fortran strides and no suboffsets, each item at its place in column-major order."
    source := "memoryobject.c:889-946", status := .proven
    prop := ``FromContigCopyF, thm := some ``fromContigCopyF_proven },
  { id := "bytesobj-memoryview-get-contiguous-copy-f", pyFile := memFile
    pyFns := ["PyMemoryView_GetContiguous", "memory_from_contiguous_copy"]
    statement := "A read request in Fortran order on a view that is not Fortran-contiguous gives a new view with Fortran strides holding the items in column-major order, and the temporary view is dropped."
    source := "memoryobject.c:889-946, :998-1000", status := .proven
    prop := ``GetContiguousCopyF, thm := some ``getContiguousCopyF_proven },
  { id := "bytesobj-memoryview-cast-cleanup", pyFile := memFile
    pyFns := ["memoryview_cast_impl"]
    statement := "When a cast fails after the new view is made, its export of the managed buffer is given back."
    source := "memoryobject.c:1496-1498", status := .proven
    prop := ``CastCleanup, thm := some ``castCleanup_proven },
  { id := "bytesobj-memoryview-copy-single-sub", pyFile := memFile
    pyFns := ["copy_single", "copy_base", "last_dim_is_contiguous"]
    statement := "m[s] = x on a view with suboffsets writes each item at the address its pointer gives, through the scratch buffer, because last_dim_is_contiguous is false there; the source may have suboffsets too."
    source := "memoryobject.c:272-279, :345-371, :405-432", status := .proven
    prop := ``CopySingleSub, thm := some ``copySingleSub_proven },
  { id := "bytesobj-memoryview-pack-unpack-other", pyFile := memFile
    pyFns := ["pack_single", "unpack_single"]
    statement := "For the formats other than the integers, pack then unpack: ? gives the truth of the item, c the byte, P the pointer, d the double exactly, f and e the pattern they stored; a released view refuses to unpack."
    source := "memoryobject.c:1776-1863, :1875-2026", status := .proven
    prop := ``PackUnpackOther, thm := some ``packUnpackOther_proven },
  { id := "bytesobj-memoryview-fix-struct", pyFile := memFile
    pyFns := ["fix_struct_error_int"]
    statement := "A struct error means not equal and is cleared; a failed import of struct and a MemoryError pass through."
    source := "memoryobject.c:2917-2928", status := .proven
    prop := ``FixStructRules, thm := some ``fixStructRules_proven },
  { id := "bytesobj-memoryview-cmp-import", pyFile := memFile
    pyFns := ["struct_get_unpacker", "fix_struct_error_int", "memory_richcompare"]
    statement := "With struct not importable, two views of one native format still compare by the switch, and any comparison needing struct raises ModuleNotFoundError out of ==."
    source := "memoryobject.c:2084-2086, :3144-3158", status := .proven
    prop := ``CmpImportFails, thm := some ``cmpImportFails_proven },
  { id := "bytesobj-memoryview-rank-rules", pyFile := memFile
    pyFns := ["memory_length", "memory_iter", "memory_item", "memoryview_count_impl", "memoryview_index_impl"]
    statement := "len(m) is shape[0] on every view with dimensions. A 0-dim view has no length, iterator, items or lookup, and a view of two or more dimensions refuses iteration, count, index and m[i] as not implemented, each with the source's message."
    source := "memoryobject.c:2466-2478, :2746-2756, :2847-2850, :2900-2903, :3529-3537", status := .proven
    prop := ``RankRules, thm := some ``rankRules_proven },
  { id := "bytesobj-memoryview-iter-null", pyFile := memFile
    pyFns := ["memoryiter_next"]
    statement := "An item at NULL ends the iteration with no exception, though the iterator has not reached its length and keeps its view, stepped past that item."
    source := "memoryobject.c:3508-3510", status := .proven
    prop := ``IterNull, thm := some ``iterNull_proven },
  { id := "bytesobj-memoryview-slice-failures", pyFile := memFile
    pyFns := ["init_slice"]
    statement := "A slice key is unpacked in the order step, zero test, start, stop: a failing step comes first, a zero step stops the __index__ of start and stop from running, and otherwise the failing part's error is raised."
    source := "Objects/sliceobject.c:218-258", status := .proven
    prop := ``SliceFailures, thm := some ``sliceFailures_proven },
  { id := "bytesobj-memoryview-slice-cleanup", pyFile := memFile
    pyFns := ["memory_subscript", "memory_ass_sub"]
    statement := "When a slice key fails, m[s] raises and gives back the export the sliced view took on the managed buffer, and m[s] = x raises and gives back x's buffer, running __release_buffer__."
    source := "memoryobject.c:2616-2623, :2699-2718", status := .proven
    prop := ``SliceCleanup, thm := some ``sliceCleanup_proven },
  { id := "bytesobj-memoryview-cmp-is-tolist", pyFile := memFile
    pyFns := ["memory_richcompare", "cmp_base", "cmp_rec", "unpack_cmp", "struct_unpack_cmp", "struct_unpack_single"]
    statement := "v == w is v.tolist() == w.tolist() for any two live views of native formats, the same or different, of any shape, strides and suboffsets, floats included; with a different ndim v == w is False, though the lists can be equal."
    source := "Doc/library/stdtypes.rst memoryview.__eq__; fast path against struct path", status := .proven
    prop := ``CmpIsTolist, thm := some ``cmpIsTolist_proven },
  { id := "bytesobj-memoryview-cmp-non-native", pyFile := memFile
    pyFns := ["memory_richcompare", "cmp_base", "struct_unpack_cmp", "struct_unpack_single"]
    statement := "With a format that is not native, 1-D views are equal exactly when every pair of items agrees under struct_unpack_cmp, which compares one-value tuples by that value and longer tuples as tuples."
    source := "memoryobject.c:2128-2144, :2931-2956, :3140-3158", status := .proven
    prop := ``CmpNonNative, thm := some ``cmpNonNative_proven },
  { id := "bytesobj-memoryview-equiv-rules", pyFile := memFile
    pyFns := ["equiv_format", "equiv_shape", "equiv_structure"]
    statement := "A slice assignment goes ahead exactly if the formats agree apart from a leading @, the item sizes and dimensions are equal, and the shapes are equal up to the first dimension of length 0; otherwise ValueError."
    source := "memoryobject.c:287-339", status := .proven
    prop := ``EquivRules, thm := some ``equivRules_proven },
  { id := "bytesobj-memoryview-copy-single-refuses", pyFile := memFile
    pyFns := ["copy_single"]
    statement := "copy_single re-checks the view after the Python code that got the source's buffer, then refuses a source of another structure, writing nothing."
    source := "memoryobject.c:404-432", status := .proven
    prop := ``CopySingleRefuses, thm := some ``copySingleRefuses_proven },
  { id := "bytesobj-memoryview-adjust-fmt", pyFile := memFile
    pyFns := ["adjust_fmt"]
    statement := "After an optional @ the format must be one character; anything else raises NotImplementedError naming the whole format."
    source := "memoryobject.c:2152-2164", status := .proven
    prop := ``AdjustFmtRules, thm := some ``adjustFmtRules_proven },
  { id := "bytesobj-memoryview-float32-round-trip", pyFile := memFile
    pyFns := ["pack_single", "unpack_single"]
    statement := "Storing a double read from a float item stores the same float: narrow32 (widen32 x) = x for every non-NaN 32-bit pattern."
    source := "invariant; IEEE 754", status := .open
    prop := ``Float32RoundTrip
    notes := "narrow32 and widen32 agree with hardware on the difftest. A proof needs reasoning about log2 and the rounding of exact values; no Mathlib here." },
  { id := "bytesobj-memoryview-float16-round-trip", pyFile := memFile
    pyFns := ["pack_single", "unpack_single"]
    statement := "pack2 (unpack2 x) = .ok x for every non-NaN 16-bit pattern."
    source := "invariant; IEEE 754", status := .open
    prop := ``Float16RoundTrip
    notes := "Same as the 32-bit case. 65536 patterns, but `decide` cannot run through the log2 and pow here within limits." },
  { id := "bytesobj-memoryview-tobytes-contig-nd", pyFile := memFile
    pyFns := ["PyBuffer_ToContiguous"]
    statement := "For a C-contiguous view with no suboffsets and any number of dimensions, the memcpy branch of PyBuffer_ToContiguous gives the same bytes as the row-major walk."
    source := "Fast path against general path", status := .proven
    prop := ``TobytesContigND, thm := some ``tobytesContigND_proven },
  { id := "bytesobj-memoryview-tobytes-fortran", pyFile := memFile
    pyFns := ["buffer_to_contiguous", "init_fortran_strides_from_shape"]
    statement := "tobytes('F') of a 2-D view lists the items column by column."
    source := "Doc/library/stdtypes.rst memoryview.tobytes", status := .open
    prop := ``TobytesFortran2D
    notes := "copy_rec into Fortran strides interleaves the writes, so the concatenation argument of TobytesC does not apply; agreement with CPython is on the difftest." }
]

end PyLean.BytesObj.Mem
