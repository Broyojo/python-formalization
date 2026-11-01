p='lean/PyLean/Bytecode/SpecBasic.lean'
s=open(p).read()
s=s.replace('''    · left
      exact ⟨_, by simp [bind, EStateM.bind, K.tos_eval, hr]⟩
''','''    · left
      refine ⟨⟨regs, r :: l :: rest⟩, ?_⟩
      simp [bind, EStateM.bind, K.tos_eval, hr]
''')
s=s.replace('''      · left
        refine ⟨_, ?_⟩
        simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl]
        rfl
''','''      · left
        refine ⟨⟨regs, r :: l :: rest⟩, ?_⟩
        simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl]
''')
s=s.replace('''    BM.lift, RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]
  rfl

/-- The fast half''','''    BM.lift, RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]

/-- The fast half''')
open(p,'w').write(s)
