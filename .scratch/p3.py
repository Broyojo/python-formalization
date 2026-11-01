p='lean/PyLean/Bytecode/Protocol.lean'
s=open(p).read()
s=s.replace('''  match v with
  | .bool b => pure b
  | .none => pure false
  | .int i => pure (i != 0)''','''  match v with
  | .bool b => pure b
  | .none => pure false
  | .notImpl => typeError "NotImplemented should not be used in a boolean context"
  | .int i => pure (i != 0)''')
open(p,'w').write(s)
p='difftest/bytecode_diff.py'
s=open(p).read()
s=s.replace('''    out = [sub, f"def f():\\n{indented}", "g = f()"]
    for o in ops:
''','''    out = [sub, f"def f():\\n{indented}", "g = f()"]
    # `throw(1)` on a delegating generator drops the subiterator, and what its
    # finalizer prints depends on reference counts, which the model does not have.
    if "sub()" in body:
        ops = [o for o in ops if o != "g.throw(1)"]
    for o in ops:
''')
open(p,'w').write(s)
