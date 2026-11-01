p='lean/PyLean/Bytecode/Protocol.lean'
s=open(p).read()
s=s.replace('''    match ← asIndex om ctx k with
    | some n =>
      let i := if n < 0 then n + b.length else n
      if i < 0 || i ≥ b.length then raiseS "IndexError" "index out of range"''','''    match ← asIndex om ctx k with
    | some n =>
      let n ← indexSsize n
      let i := if n < 0 then n + b.length else n
      if i < 0 || i ≥ b.length then raiseS "IndexError" "index out of range"''')
open(p,'w').write(s)
p='lean/PyLean/Bytecode/Builtins.lean'
s=open(p).read()
s=s.replace('''  | 5, .str a, _ =>
    match intOf r with
    | some n => pure (some (.str (pyStrRepeat a n)))
    | none => pure none''','''  | 5, .bytes a, _ =>
    match intOf r with
    | some n => pure (some (.bytes (List.flatten (List.replicate n.toNat a))))
    | none => pure none
  | 5, _, .bytes b =>
    match intOf l with
    | some n => pure (some (.bytes (List.flatten (List.replicate n.toNat b))))
    | none => pure none
  | 5, .str a, _ =>
    match intOf r with
    | some n => pure (some (.str (pyStrRepeat a n)))
    | none => pure none''')
s=s.replace('''  | .str s =>
    match item with
    | .str t => pure ((s.splitOn t).length > 1 || t == "")
    | _ => typeError s!"'in <string>' requires string as left operand, not {← tpName item}"
  | .ref a =>
    match ← getObj a with
    | .dict _ => do''','''  | .str s =>
    match item with
    | .str t => pure ((s.splitOn t).length > 1 || t == "")
    | _ => typeError s!"'in <string>' requires string as left operand, not {← tpName item}"
  | .bytes b =>
    match item with
    | .int i =>
      if i < 0 || i > 255 then valueError "byte must be in range(0, 256)"
      pure (b.contains (UInt8.ofNat i.toNat))
    | .bool x => pure (b.contains (if x then 1 else 0))
    | .bytes t =>
      let n := t.length
      pure ((List.range (b.length + 1)).any fun i => (b.drop i).take n == t)
    | _ => typeError s!"a bytes-like object is required, not '{← tpName item}'"
  | .ref a =>
    match ← getObj a with
    | .dict _ => do''')
s=s.replace('''      | .dict _, 7 =>
        om.dictUpdate ctx l r
        return l''','''      | .dict _, 7 =>
        dictUpdateArgFwd om ctx l r
        return l''')
a=s.index('/-- `dict_update_arg`, `Objects/dictobject.c`: a mapping, or a sequence of pairs. -/')
b=s.index('/-- First position of an element equal to `x`. -/')
block=s[a:b]
s=s[:a]+s[b:]
seq=s.index('/-- `list(iterable)`/`PySequence_List`. -/')
seqend=s.index('/-- `str.split(sep)`, whitespace form. -/')
seqblock=s[seq:seqend]
s=s[:seq]+s[seqend:]
c=s.index('/-- The concatenation errors of `PyNumber_Add`')
s=s[:c]+seqblock+block+s[c:]
open(p,'w').write(s)
p='difftest/bytecode_diff.py'
s=open(p).read()
s=s.replace('''    buf = io.StringIO()
    exc = None
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        co = compile(case["src"], "<prog>", "exec")
        with contextlib.redirect_stdout(buf):
            try:
                exec(co, {"__name__": "__main__"})
            except BaseException as e:
                exc = [type(e).__name__, str(e)]
    return {"ok": {"out": buf.getvalue(), "exc": exc}}
''','''    buf = io.StringIO()
    exc = None
    g = {"__name__": "__main__"}
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        co = compile(case["src"], "<prog>", "exec")
        with contextlib.redirect_stdout(buf):
            try:
                exec(co, g)
            except BaseException as e:
                exc = [type(e).__name__, str(e)]
    # Finalizers of objects still alive at the end are not part of the program's
    # output, and must not run during a later case.
    with contextlib.redirect_stdout(io.StringIO()):
        g.clear()
        e = None
        gc.collect()
    return {"ok": {"out": buf.getvalue(), "exc": exc}}
''')
s=s.replace('''import contextlib
import dis
import io
''','''import contextlib
import dis
import gc
import io
''')
s=s.replace('''from common import main
''','''from common import main

sys.unraisablehook = lambda u: None
''')
open(p,'w').write(s)
