p='lean/PyLean/Bytecode/SpecHeap.lean'
s=open(p).read()
s=s.replace('''  store_dict : ∀ ctx d k v, (∃ a o, d = .ref a ∧ o = 0) →
    om.setItem ctx d k v = fun rt =>
      if (isExactDict d rt).isOk then dictSet om ctx d k v rt else om.setItem ctx d k v rt
''','''  store_dict : ∀ ctx a k v d rt, rt.heap[a]? = some (.dict d) →
    om.setItem ctx (.ref a) k v rt = dictSet om ctx (.ref a) k v rt
''')
open(p,'w').write(s)
