cd lean
lake build ${1:-PyLean.Bytecode.SpecBasic} 2>&1 | grep -v "^⚠\|^✔\|^trace\|^warning\|linter\|^$\|Hint:\|\[apply\]\|^  pure\|^  bind\|EStateM.pure\|simp only \[\|^  [A-Za-z_.]*$\|^    List\.\|^    [A-Za-z_.]*,\|^  show\|omit \|unused\|this linter\|Note: This" | cut -c1-${2:-460} | head -${3:-70}
