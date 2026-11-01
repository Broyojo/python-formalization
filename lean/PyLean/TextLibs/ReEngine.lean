import PyLean.TextLibs.ReCompile

/-!
Model of `Modules/_sre/sre_lib.h`, CPython 3.14.7: `SRE(at)`, `SRE(charset)`, `SRE(count)`,
`SRE(match)` and `SRE(search)`, run on the code words of `TextLibs/ReCompile.lean`.

`SRE(match)` is one C function that fakes recursion with `DO_JUMP`. Here `DO_JUMP` is a recursive
call of `matchAt` and each C loop that spans a `DO_JUMP` is a function of the mutual block. All
state that the C keeps across a failure is threaded through `SSt`: a failed call may leave marks
set, and `LASTMARK_RESTORE` only moves `lastmark`. `fuel` bounds the recursion; running out is
`none`, which is never a Python outcome.

`LOCALE` is the C locale: `sre_isalnum`, `sre_tolower` and `sre_toupper` act on ASCII only.
-/

namespace PyLean.TextLibs.Re

open PyLean

/-- `SRE_REPEAT`. `pat` is the index of `<skip>`, as `ctx->u.rep->pattern`. -/
structure Rep where
  count : Int
  pat : Nat
  prev : Option Nat
  lastPtr : Option Nat
  deriving Repr, Inhabited

/-- The `SRE_STATE` fields that change during a match. -/
structure SSt where
  ptr : Nat
  start : Nat
  mark : Array (Option Nat)
  lastmark : Int := -1
  lastindex : Int := -1
  repeat_ : Option Nat := none
  reps : Array Rep := #[]
  mustAdvance : Bool := false
  deriving Repr, Inhabited

/-- What never changes during a match. `endp` is `state->end`. -/
structure Env where
  code : Array Nat
  s : Array Nat
  endp : Nat
  matchAll : Bool

abbrev R := Option (Bool × SSt)

def Env.c (e : Env) (i : Nat) : Nat := e.code.getD i 0
def Env.ch (e : Env) (i : Nat) : Nat := e.s.getD i 0

/-- `Py_ISALNUM`. -/
def isAlnumAscii (c : Nat) : Bool := c < 128 && (isDigit c || isLetter c)

/-- `SRE_IS_WORD`, `Modules/_sre/sre.c:141-142`. -/
def isWordAscii (c : Nat) : Bool := isAlnumAscii c || c == 95

/-- `SRE_LOC_IS_WORD`, `Modules/_sre/sre.c:152-153`, in the C locale. -/
def isWordLoc (c : Nat) : Bool := (c < 256 && isAlnumAscii c) || c == 95

/-- `SRE_UNI_IS_WORD`, `Modules/_sre/sre.c:171`. -/
def isWordUni (c : Nat) : Bool := PyLean.UnicodeObj.isAlnum c || c == 95

/-- `Py_ISSPACE`. -/
def isSpaceAscii (c : Nat) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- `sre_lower_locale`, `sre_upper_locale`, `Modules/_sre/sre.c:155-163`, in the C locale. -/
def lowerLocale (c : Nat) : Nat := lowerAscii c
def upperLocale (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- `sre_category`, `Modules/_sre/sre.c:183-228`. -/
def sreCategory (cat ch : Nat) : Bool :=
  match cat with
  | 0 => isDigit ch
  | 1 => !isDigit ch
  | 2 => isSpaceAscii ch
  | 3 => !isSpaceAscii ch
  | 4 => isWordAscii ch
  | 5 => !isWordAscii ch
  | 6 => ch == 10
  | 7 => ch != 10
  | 8 => isWordLoc ch
  | 9 => !isWordLoc ch
  | 10 => PyLean.UnicodeObj.isDecimalDigit ch
  | 11 => !PyLean.UnicodeObj.isDecimalDigit ch
  | 12 => PyLean.UnicodeObj.isSpace ch
  | 13 => !PyLean.UnicodeObj.isSpace ch
  | 14 => isWordUni ch
  | 15 => !isWordUni ch
  | 16 => PyLean.UnicodeObj.isLinebreak ch
  | 17 => !PyLean.UnicodeObj.isLinebreak ch
  | _ => false

/-- `char_loc_ignore`, `Modules/_sre/sre.c:230-236`. -/
def charLocIgnore (pat ch : Nat) : Bool :=
  ch == pat || lowerLocale ch == pat || upperLocale ch == pat

/-- `SRE(at)`, `Modules/_sre/sre_lib.h:15-89`. -/
def sreAt (e : Env) (ptr at_ : Nat) : Bool :=
  let boundary (word : Nat → Bool) : Bool × Bool :=
    (ptr > 0 && word (e.ch (ptr - 1)), ptr < e.endp && word (e.ch ptr))
  match at_ with
  | 0 | 2 => ptr == 0
  | 1 => ptr == 0 || e.ch (ptr - 1) == 10
  | 5 => (e.endp - ptr == 1 && ptr < e.endp && e.ch ptr == 10) || ptr == e.endp
  | 6 => ptr == e.endp || e.ch ptr == 10
  | 7 => ptr == e.endp
  | 3 => let (a, b) := boundary isWordAscii; b != a
  | 4 => let (a, b) := boundary isWordAscii; b == a
  | 8 => let (a, b) := boundary isWordLoc; b != a
  | 9 => let (a, b) := boundary isWordLoc; b == a
  | 10 => let (a, b) := boundary isWordUni; b != a
  | 11 => let (a, b) := boundary isWordUni; b == a
  | _ => false

/-- `SRE(charset)`, `Modules/_sre/sre_lib.h:91-176`. -/
def sreCharset (e : Env) (ch : Nat) : (fuel : Nat) → (set : Nat) → (ok : Bool) → Bool
  | 0, _, _ => false
  | fuel + 1, set, ok =>
    let word (i : Nat) := e.c i
    let op := e.c set
    let set := set + 1
    if op == OP_FAILURE then !ok
    else if op == OP_LITERAL then
      if ch == word set then ok else sreCharset e ch fuel (set + 1) ok
    else if op == OP_CATEGORY then
      if sreCategory (word set) ch then ok else sreCharset e ch fuel (set + 1) ok
    else if op == OP_CHARSET then
      if ch < 256 && (word (set + ch / 32) / 2 ^ (ch % 32)) % 2 == 1 then ok
      else sreCharset e ch fuel (set + 8) ok
    else if op == OP_RANGE then
      if word set ≤ ch ∧ ch ≤ word (set + 1) then ok else sreCharset e ch fuel (set + 2) ok
    else if op == OP_RANGE_UNI_IGNORE then
      let uch := upperUnicode ch
      if (word set ≤ ch ∧ ch ≤ word (set + 1)) ∨ (word set ≤ uch ∧ uch ≤ word (set + 1)) then ok
      else sreCharset e ch fuel (set + 2) ok
    else if op == OP_NEGATE then sreCharset e ch fuel set (!ok)
    else if op == OP_BIGCHARSET then
      let count := word set
      let set := set + 1
      let hit :=
        if ch < 0x10000 then
          let hi := ch / 256
          let block := (word (set + hi / 4) / 256 ^ (hi % 4)) % 256
          let set2 := set + 64
          (word (set2 + (block * 256 + ch % 256) / 32) / 2 ^ (ch % 32)) % 2 == 1
        else false
      if hit then ok else sreCharset e ch fuel (set + 64 + count * 8) ok
    else false

def Env.charset (e : Env) (set ch : Nat) : Bool := sreCharset e ch (e.code.size + 1) set true

/-- `SRE(charset_loc_ignore)`, `Modules/_sre/sre_lib.h:183-243`. -/
def Env.charsetLoc (e : Env) (set ch : Nat) : Bool :=
  let lo := lowerLocale ch
  e.charset set lo || (let up := upperLocale ch; up != lo && e.charset set up)

/-- A simple `while (ptr < end && cond(*ptr)) ptr++` of `SRE(count)`. -/
def Env.countWhile (e : Env) (cond : Nat → Bool) (lim : Nat) : (fuel ptr : Nat) → Nat
  | 0, ptr => ptr
  | fuel + 1, ptr =>
    if ptr < lim && cond (e.ch ptr) then e.countWhile cond lim fuel (ptr + 1) else ptr

/-- The cases of `SRE(count)`, `Modules/_sre/sre_lib.h:261-359`, that run no `SRE(match)`: the new
`ptr`, or `none` for the `default:`. `pc` is the item, `lim` the adjusted `end`. -/
def Env.countSimple (e : Env) (pc ptr lim : Nat) : Option Nat :=
  let op := e.c pc
  let a := e.c (pc + 1)
  let scan (cond : Nat → Bool) : Option Nat := some (e.countWhile cond lim (lim + 1 - ptr) ptr)
  if op == OP_IN then scan (e.charset (pc + 2))
  else if op == OP_ANY then scan (· != 10)
  else if op == OP_ANY_ALL then some (max ptr lim)
  else if op == OP_LITERAL then scan (· == a)
  else if op == OP_LITERAL_IGNORE then scan (fun c => lowerAscii c == a)
  else if op == OP_LITERAL_UNI_IGNORE then scan (fun c => lowerUnicode c == a)
  else if op == OP_LITERAL_LOC_IGNORE then scan (charLocIgnore a)
  else if op == OP_NOT_LITERAL then scan (· != a)
  else if op == OP_NOT_LITERAL_IGNORE then scan (fun c => lowerAscii c != a)
  else if op == OP_NOT_LITERAL_UNI_IGNORE then scan (fun c => lowerUnicode c != a)
  else if op == OP_NOT_LITERAL_LOC_IGNORE then scan (fun c => !charLocIgnore a c)
  else none

/-- The `end` of `SRE(count)` after `/* adjust end */`, `Modules/_sre/sre_lib.h:258-259`. -/
def Env.countEnd (e : Env) (ptr maxcount : Nat) : Nat :=
  if maxcount < e.endp - ptr ∧ maxcount ≠ MAXREPEAT then ptr + maxcount else e.endp

/-- `LASTMARK_SAVE` and `MARK_PUSH`: the first `lastmark + 1` marks. -/
def markSnap (st : SSt) (lastmark : Int) : Array (Option Nat) :=
  if lastmark ≥ 0 then st.mark.extract 0 (lastmark + 1).toNat else #[]

/-- `MARK_POP`, `MARK_POP_KEEP`: write the first marks back. -/
def markPop (st : SSt) (snap : Array (Option Nat)) : SSt :=
  { st with mark := snap ++ st.mark.extract snap.size st.mark.size }

/-- `LASTMARK_RESTORE`. -/
def lastRestore (st : SSt) (lm li : Int) : SSt := { st with lastmark := lm, lastindex := li }

def SSt.rep (st : SSt) : Rep := st.reps[st.repeat_.getD 0]!

/-- Update the current `SRE_REPEAT`. -/
def SSt.setRep (st : SSt) (i : Nat) (f : Rep → Rep) : SSt :=
  { st with reps := st.reps.modify i f }

/-- `repeat_pool_malloc` with its initialisation. -/
def SSt.newRep (st : SSt) (pat : Nat) : SSt × Nat :=
  let i := st.reps.size
  ({ st with reps := st.reps.push ⟨-1, pat, st.repeat_, none⟩, repeat_ := some i }, i)

/-- The `SRE_OP_MARK` body, `Modules/_sre/sre_lib.h:709-722`. -/
def doMark (st : SSt) (i ptr : Nat) : SSt :=
  let li := if i % 2 == 1 then ((i / 2 + 1 : Nat) : Int) else st.lastindex
  let (mark, lm) :=
    if (i : Int) > st.lastmark then
      let j0 := (st.lastmark + 1).toNat
      ((List.range (i - j0)).foldl (fun m k => m.set! (j0 + k) none) st.mark, (i : Int))
    else (st.mark, st.lastmark)
  { st with lastindex := li, lastmark := lm, mark := mark.set! i (some ptr) }

/-- A group reference, `Modules/_sre/sre_lib.h:1495-1592`: the span, if it can be used. -/
def groupSpan (st : SSt) (g : Nat) : Option (Nat × Nat) :=
  let groupref := g * 2
  if (groupref : Int) ≥ st.lastmark then none
  else
    match st.mark[groupref]!, st.mark[groupref + 1]! with
    | some p, some q => if q < p then none else some (p, q)
    | _, _ => none

/-- The compare loop of a group reference. `norm` is the case mapping. -/
def Env.refMatch (e : Env) (norm : Nat → Nat) : (fuel p q ptr : Nat) → Option Nat
  | 0, _, _, ptr => some ptr
  | fuel + 1, p, q, ptr =>
    if p < q then
      if ptr ≥ e.endp || norm (e.ch ptr) != norm (e.ch p) then none
      else e.refMatch norm fuel (p + 1) q (ptr + 1)
    else some ptr

mutual
  /-- `SRE(match)` from `entrance:`, `Modules/_sre/sre_lib.h:678-692`. -/
  def matchAt (e : Env) : (fuel : Nat) → (pc : Nat) → (top : Bool) → SSt → R
    | 0, _, _, _ => none
    | fuel + 1, pc, top, st =>
      let ptr := st.ptr
      if e.c pc == OP_INFO then
        if e.c (pc + 3) != 0 ∧ ptr ≤ e.endp ∧ e.endp - ptr < e.c (pc + 3) then some (false, st)
        else exec e fuel (pc + 1 + e.c (pc + 1) + 0) ptr top st
      else exec e fuel pc ptr top st

  /-- The dispatch loop, `Modules/_sre/sre_lib.h:701-1672`. -/
  def exec (e : Env) : (fuel : Nat) → (pc ptr : Nat) → (top : Bool) → SSt → R
    | 0, _, _, _, _ => none
    | fuel + 1, pc, ptr, top, st =>
      let op := e.c pc
      let p := pc + 1
      let fail : R := some (false, st)
      let more := ptr < e.endp
      let cur := e.ch ptr
      if op == OP_MARK then exec e fuel (p + 1) ptr top (doMark st (e.c p) ptr)
      else if op == OP_LITERAL then
        if !more || cur != e.c p then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_NOT_LITERAL then
        if !more || cur == e.c p then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_SUCCESS then
        if top && ((e.matchAll && ptr != e.endp) || (st.mustAdvance && ptr == st.start)) then fail
        else some (true, { st with ptr })
      else if op == OP_AT then
        if !sreAt e ptr (e.c p) then fail else exec e fuel (p + 1) ptr top st
      else if op == OP_CATEGORY then
        if !more || !sreCategory (e.c p) cur then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_ANY then
        if !more || cur == 10 then fail else exec e fuel p (ptr + 1) top st
      else if op == OP_ANY_ALL then
        if !more then fail else exec e fuel p (ptr + 1) top st
      else if op == OP_IN then
        if !more || !e.charset (p + 1) cur then fail else exec e fuel (p + e.c p) (ptr + 1) top st
      else if op == OP_LITERAL_IGNORE then
        if !more || lowerAscii cur != e.c p then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_LITERAL_UNI_IGNORE then
        if !more || lowerUnicode cur != e.c p then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_LITERAL_LOC_IGNORE then
        if !more || !charLocIgnore (e.c p) cur then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_NOT_LITERAL_IGNORE then
        if !more || lowerAscii cur == e.c p then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_NOT_LITERAL_UNI_IGNORE then
        if !more || lowerUnicode cur == e.c p then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_NOT_LITERAL_LOC_IGNORE then
        if !more || charLocIgnore (e.c p) cur then fail else exec e fuel (p + 1) (ptr + 1) top st
      else if op == OP_IN_IGNORE then
        if !more || !e.charset (p + 1) (lowerAscii cur) then fail
        else exec e fuel (p + e.c p) (ptr + 1) top st
      else if op == OP_IN_UNI_IGNORE then
        if !more || !e.charset (p + 1) (lowerUnicode cur) then fail
        else exec e fuel (p + e.c p) (ptr + 1) top st
      else if op == OP_IN_LOC_IGNORE then
        if !more || !e.charsetLoc (p + 1) cur then fail
        else exec e fuel (p + e.c p) (ptr + 1) top st
      else if op == OP_JUMP || op == OP_INFO then exec e fuel (p + e.c p) ptr top st
      else if op == OP_BRANCH then
        let lm := st.lastmark
        let li := st.lastindex
        let snap := if st.repeat_.isSome then markSnap st lm else #[]
        branchLoop e fuel p ptr top lm li snap st
      else if op == OP_REPEAT_ONE then
        let mn := e.c (p + 1)
        if (mn : Int) > (e.endp : Int) - ptr then fail
        else
          match countFn e fuel (p + 3) (e.c (p + 2)) { st with ptr } with
          | none => none
          | some (cnt, st) =>
            let ptr2 := ptr + cnt
            let next := p + e.c p
            if cnt < mn then some (false, st)
            else if e.c next == OP_SUCCESS ∧ ptr2 == e.endp ∧
                !(top && st.mustAdvance && ptr2 == st.start) then
              some (true, { st with ptr := ptr2 })
            else
              let lm := st.lastmark
              let li := st.lastindex
              let snap := if st.repeat_.isSome then markSnap st lm else #[]
              if e.c next == OP_LITERAL then
                repOneLit e fuel next (e.c (next + 1)) mn ptr ptr2 top lm li snap st
              else repOneGen e fuel next mn ptr ptr2 top lm li snap st
      else if op == OP_MIN_REPEAT_ONE then
        let mn := e.c (p + 1)
        if (mn : Int) > (e.endp : Int) - ptr then fail
        else
          let st1 := { st with ptr }
          let counted :=
            if mn == 0 then some (0, st1)
            else
              match countFn e fuel (p + 3) mn st1 with
              | none => none
              | some (c, s) => if c < mn then some (c, s) else some (c, s)
          match counted with
          | none => none
          | some (cnt, st) =>
            if mn != 0 && cnt < mn then some (false, st)
            else
              let ptr2 := ptr + cnt
              let next := p + e.c p
              if e.c next == OP_SUCCESS ∧
                  !(top && ((e.matchAll && ptr2 != e.endp) || (st.mustAdvance && ptr2 == st.start))) then
                some (true, { st with ptr := ptr2 })
              else
                let lm := st.lastmark
                let li := st.lastindex
                let snap := if st.repeat_.isSome then markSnap st lm else #[]
                minRepOne e fuel p next cnt ptr2 top lm li snap st
      else if op == OP_POSSESSIVE_REPEAT_ONE then
        let mn := e.c (p + 1)
        if ptr + mn > e.endp then fail
        else
          match countFn e fuel (p + 3) (e.c (p + 2)) { st with ptr } with
          | none => none
          | some (cnt, st) =>
            let ptr2 := ptr + cnt
            if cnt < mn then some (false, st)
            else
              let next := p + e.c p
              if e.c next == OP_SUCCESS ∧ ptr2 == e.endp ∧
                  !(top && st.mustAdvance && ptr2 == st.start) then
                some (true, { st with ptr := ptr2 })
              else exec e fuel next ptr2 top st
      else if op == OP_REPEAT then
        let st1 := { st with ptr }
        let (st1, i) := st1.newRep p
        match matchAt e fuel (p + e.c p) top st1 with
        | none => none
        | some (ret, st2) =>
          some (ret, { st2 with repeat_ := st2.reps[i]!.prev })
      else if op == OP_MAX_UNTIL then
        match st.repeat_ with
        | none => none
        | some i =>
          let st := { st with ptr }
          let rep := st.reps[i]!
          let count := rep.count + 1
          let mn : Int := e.c (rep.pat + 1)
          let mx := e.c (rep.pat + 2)
          if count < mn then
            let st := st.setRep i (fun r => { r with count })
            match matchAt e fuel (rep.pat + 3) top st with
            | none => none
            | some (true, st) => some (true, st)
            | some (false, st) =>
              some (false, { (st.setRep i (fun r => { r with count := count - 1 })) with ptr })
          else if (count < mx ∨ mx == MAXREPEAT) ∧ some st.ptr != rep.lastPtr then
            let st := st.setRep i (fun r => { r with count })
            let lm := st.lastmark
            let li := st.lastindex
            let snap := markSnap st lm
            let saved := st.reps[i]!.lastPtr
            let st := st.setRep i (fun r => { r with lastPtr := some st.ptr })
            match matchAt e fuel (rep.pat + 3) top st with
            | none => none
            | some (ret, st) =>
              let st := st.setRep i (fun r => { r with lastPtr := saved })
              if ret then some (true, st)
              else
                let st := lastRestore (markPop st snap) lm li
                let st := { (st.setRep i (fun r => { r with count := count - 1 })) with ptr }
                maxTail e fuel p ptr top i st
          else maxTail e fuel p ptr top i st
      else if op == OP_MIN_UNTIL then
        match st.repeat_ with
        | none => none
        | some i =>
          let st := { st with ptr }
          let rep := st.reps[i]!
          let count := rep.count + 1
          let mn : Int := e.c (rep.pat + 1)
          let mx := e.c (rep.pat + 2)
          if count < mn then
            let st := st.setRep i (fun r => { r with count })
            match matchAt e fuel (rep.pat + 3) top st with
            | none => none
            | some (true, st) => some (true, st)
            | some (false, st) =>
              some (false, { (st.setRep i (fun r => { r with count := count - 1 })) with ptr })
          else
            let st := { st with repeat_ := rep.prev }
            let lm := st.lastmark
            let li := st.lastindex
            let snap := if st.repeat_.isSome then markSnap st lm else #[]
            match matchAt e fuel p top st with
            | none => none
            | some (ret, st) =>
              let tailRep := st.repeat_
              let st := { st with repeat_ := some i }
              if ret then some (true, st)
              else
                let st := if tailRep.isSome then markPop st snap else st
                let st := { (lastRestore st lm li) with ptr }
                let rep2 := st.reps[i]!
                if (count ≥ (mx : Int) ∧ mx != MAXREPEAT) ∨ some st.ptr == rep2.lastPtr then
                  some (false, st)
                else
                  let st := st.setRep i (fun r => { r with count })
                  let saved := st.reps[i]!.lastPtr
                  let st := st.setRep i (fun r => { r with lastPtr := some st.ptr })
                  match matchAt e fuel (rep.pat + 3) top st with
                  | none => none
                  | some (ret, st) =>
                    let st := st.setRep i (fun r => { r with lastPtr := saved })
                    if ret then some (true, st)
                    else some (false, { (st.setRep i (fun r => { r with count := count - 1 })) with ptr })
      else if op == OP_POSSESSIVE_REPEAT then
        let (st1, _) := ({ st with ptr } : SSt).newRep 0
        let prev := st.repeat_
        possMin e fuel p ptr top 0 prev st1
      else if op == OP_ATOMIC_GROUP then
        match matchAt e fuel (p + 1) false { st with ptr } with
        | none => none
        | some (false, st) => some (false, { st with ptr })
        | some (true, st) => exec e fuel (p + e.c p) st.ptr top st
      else if op == OP_GROUPREF || op == OP_GROUPREF_IGNORE || op == OP_GROUPREF_UNI_IGNORE
          || op == OP_GROUPREF_LOC_IGNORE then
        let norm : Nat → Nat :=
          if op == OP_GROUPREF then id
          else if op == OP_GROUPREF_IGNORE then lowerAscii
          else if op == OP_GROUPREF_UNI_IGNORE then lowerUnicode
          else lowerLocale
        match groupSpan st (e.c p) with
        | none => fail
        | some (a, b) =>
          match e.refMatch norm (b - a + 1) a b ptr with
          | none => fail
          | some ptr2 => exec e fuel (p + 1) ptr2 top st
      else if op == OP_GROUPREF_EXISTS then
        match groupSpan st (e.c p) with
        | none => exec e fuel (p + e.c (p + 1)) ptr top st
        | some _ => exec e fuel (p + 2) ptr top st
      else if op == OP_ASSERT then
        if ptr < e.c (p + 1) then fail
        else
          match matchAt e fuel (p + 2) false { st with ptr := ptr - e.c (p + 1) } with
          | none => none
          | some (false, st) => some (false, st)
          | some (true, st) => exec e fuel (p + e.c p) ptr top st
      else if op == OP_ASSERT_NOT then
        if ptr ≥ e.c (p + 1) then
          let lm := st.lastmark
          let li := st.lastindex
          let snap := if st.repeat_.isSome then markSnap st lm else #[]
          let hadRep := st.repeat_.isSome
          match matchAt e fuel (p + 2) false { st with ptr := ptr - e.c (p + 1) } with
          | none => none
          | some (true, st) => some (false, st)
          | some (false, st) =>
            let st := if hadRep then markPop st snap else st
            exec e fuel (p + e.c p) ptr top (lastRestore st lm li)
        else exec e fuel (p + e.c p) ptr top st
      else if op == OP_FAILURE then fail
      else none

  /-- The tail of `MAX_UNTIL`, `Modules/_sre/sre_lib.h:1259-1267`. -/
  def maxTail (e : Env) : (fuel : Nat) → (p ptr : Nat) → (top : Bool) → (i : Nat) → SSt → R
    | 0, _, _, _, _, _ => none
    | fuel + 1, p, ptr, top, i, st =>
      let st := { st with repeat_ := st.reps[i]!.prev }
      match matchAt e fuel p top st with
      | none => none
      | some (ret, st) =>
        let st := { st with repeat_ := some i }
        if ret then some (true, st) else some (false, { st with ptr })

  /-- The `for` loop of `SRE_OP_BRANCH`, `Modules/_sre/sre_lib.h:915-939`. -/
  def branchLoop (e : Env) : (fuel : Nat) → (p ptr : Nat) → (top : Bool) → (lm li : Int) →
      Array (Option Nat) → SSt → R
    | 0, _, _, _, _, _, _, _ => none
    | fuel + 1, p, ptr, top, lm, li, snap, st =>
      if e.c p == 0 then some (false, st)
      else
        let skip :=
          (e.c (p + 1) == OP_LITERAL && (ptr ≥ e.endp || e.ch ptr != e.c (p + 2))) ||
          (e.c (p + 1) == OP_IN && (ptr ≥ e.endp || !e.charset (p + 3) (e.ch ptr)))
        if skip then branchLoop e fuel (p + e.c p) ptr top lm li snap st
        else
          match matchAt e fuel (p + 1) top { st with ptr } with
          | none => none
          | some (true, st) => some (true, st)
          | some (false, st) =>
            let st := if st.repeat_.isSome then markPop st snap else st
            branchLoop e fuel (p + e.c p) ptr top lm li snap (lastRestore st lm li)

  /-- `SRE(count)`, `Modules/_sre/sre_lib.h:247-378`: the count and the state, whose `ptr` the
  `default:` case moves. -/
  def countFn (e : Env) : (fuel : Nat) → (pc maxcount : Nat) → SSt → Option (Nat × SSt)
    | 0, _, _, _ => none
    | fuel + 1, pc, maxcount, st =>
      let ptr := st.ptr
      let lim := e.countEnd ptr maxcount
      match e.countSimple pc ptr lim with
      | some q => some (q - ptr, st)
      | none =>
        match countLoop e fuel pc lim st with
        | none => none
        | some st => some (st.ptr - ptr, st)

  /-- The `default:` of `SRE(count)`, `Modules/_sre/sre_lib.h:360-372`. -/
  def countLoop (e : Env) : (fuel : Nat) → (pc lim : Nat) → SSt → Option SSt
    | 0, _, _, _ => none
    | fuel + 1, pc, lim, st =>
      if st.ptr < lim then
        match matchAt e fuel pc false st with
        | none => none
        | some (true, st) => countLoop e fuel pc lim st
        | some (false, st) => some st
      else some st

  /-- The `for (;;)` of `REPEAT_ONE` with a literal tail, `Modules/_sre/sre_lib.h:990-1013`. -/
  def repOneLit (e : Env) : (fuel : Nat) → (next chr mn start ptr : Nat) → (top : Bool) → (lm li : Int) →
      Array (Option Nat) → SSt → R
    | 0, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, next, chr, mn, start, ptr, top, lm, li, snap, st =>
      let cnt := ptr - start
      if ptr < start + mn then some (false, st)
      else if ptr ≥ e.endp || e.ch ptr != chr then
        if ptr == 0 then some (false, st)
        else repOneLit e fuel next chr mn start (ptr - 1) top lm li snap st
      else
        let _ := cnt
        match matchAt e fuel next top { st with ptr } with
        | none => none
        | some (true, st) => some (true, st)
        | some (false, st) =>
          let st := if st.repeat_.isSome then markPop st snap else st
          if ptr == 0 then some (false, lastRestore st lm li)
          else repOneLit e fuel next chr mn start (ptr - 1) top lm li snap (lastRestore st lm li)

  /-- The general `while` of `REPEAT_ONE`, `Modules/_sre/sre_lib.h:1018-1034`. -/
  def repOneGen (e : Env) : (fuel : Nat) → (next mn start ptr : Nat) → (top : Bool) → (lm li : Int) →
      Array (Option Nat) → SSt → R
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, next, mn, start, ptr, top, lm, li, snap, st =>
      if ptr < start + mn then some (false, st)
      else
        match matchAt e fuel next top { st with ptr } with
        | none => none
        | some (true, st) => some (true, st)
        | some (false, st) =>
          let st := if st.repeat_.isSome then markPop st snap else st
          if ptr == 0 then some (false, lastRestore st lm li)
          else repOneGen e fuel next mn start (ptr - 1) top lm li snap (lastRestore st lm li)

  /-- The `while` of `MIN_REPEAT_ONE`, `Modules/_sre/sre_lib.h:1088-1112`. -/
  def minRepOne (e : Env) : (fuel : Nat) → (p next cnt ptr : Nat) → (top : Bool) → (lm li : Int) →
      Array (Option Nat) → SSt → R
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, p, next, cnt, ptr, top, lm, li, snap, st =>
      let mx := e.c (p + 2)
      if !(mx == MAXREPEAT || cnt ≤ mx) then some (false, st)
      else
        match matchAt e fuel next top { st with ptr } with
        | none => none
        | some (true, st) => some (true, st)
        | some (false, st) =>
          let st := if st.repeat_.isSome then markPop st snap else st
          let st := lastRestore st lm li
          match countFn e fuel (p + 3) 1 { st with ptr } with
          | none => none
          | some (ret, st) =>
            if ret == 0 then some (false, st)
            else minRepOne e fuel p next (cnt + 1) (ptr + 1) top lm li snap st

  /-- The first `while` of `POSSESSIVE_REPEAT`, `Modules/_sre/sre_lib.h:1367-1382`. -/
  def possMin (e : Env) : (fuel : Nat) → (p ptr : Nat) → (top : Bool) → (count : Nat) →
      Option Nat → SSt → R
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, p, ptr, top, count, prev, st =>
      if count < e.c (p + 1) then
        match matchAt e fuel (p + 3) false st with
        | none => none
        | some (true, st) => possMin e fuel p ptr top (count + 1) prev st
        | some (false, st) => some (false, { st with ptr, repeat_ := prev })
      else possMore e fuel p top count none prev st

  /-- The second `while` of `POSSESSIVE_REPEAT`, `Modules/_sre/sre_lib.h:1391-1461`. -/
  def possMore (e : Env) : (fuel : Nat) → (p : Nat) → (top : Bool) → (count : Nat) →
      Option Nat → Option Nat → SSt → R
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, p, top, count, ptr, prev, st =>
      let mx := e.c (p + 2)
      let done_ (st : SSt) : R :=
        exec e fuel (p + e.c p + 1) st.ptr top { st with repeat_ := prev }
      if (count < mx ∨ mx == MAXREPEAT) ∧ some st.ptr != ptr then
        let lm := st.lastmark
        let li := st.lastindex
        let snap := markSnap st lm
        let here := st.ptr
        match matchAt e fuel (p + 3) false st with
        | none => none
        | some (true, st) => possMore e fuel p top (count + 1) (some here) prev st
        | some (false, st) =>
          let st := lastRestore (markPop st snap) lm li
          done_ { st with ptr := here }
      else done_ st
end

/-- `RESET_CAPTURE_GROUP`. -/
def resetGroups (st : SSt) : SSt := { st with lastmark := -1, lastindex := -1 }

/-- The result of `SRE(search)`: `status` and the state. `none` is the model's fuel. -/
abbrev SR := Option (Bool × SSt)

/-- Enough fuel for one `SRE(match)`: every step along a path spends one. -/
def Env.mfuel (e : Env) : Nat := 4096 + 64 * (e.code.size + 1) * (e.s.size + 2)

/-- The `while (ptr < end)` of the one-character prefix, `Modules/_sre/sre_lib.h:1810-1826`. -/
def searchLit (e : Env) (code c skip fl : Nat) : (fuel ptr : Nat) → SSt → SR
  | 0, _, _ => none
  | fuel + 1, ptr, st =>
    if ptr ≥ e.endp then some (false, st)
    else if e.ch ptr != c then searchLit e code c skip fl fuel (ptr + 1) st
    else
      let st := { st with start := ptr, ptr := ptr + skip }
      if fl &&& 2 != 0 then some (true, st)
      else
        match matchAt e e.mfuel (code + 2 * skip) false st with
        | none => none
        | some (true, st) => some (true, st)
        | some (false, st) => searchLit e code c skip fl fuel (ptr + 1) (resetGroups st)

mutual
  /-- The outer `while (ptr < end)` of the longer prefix, `Modules/_sre/sre_lib.h:1842-1876`. -/
  def searchOuter (e : Env) (code plen skip fl pfx : Nat) : (fuel ptr : Nat) → SSt → SR
    | 0, _, _ => none
    | fuel + 1, ptr, st =>
      if ptr ≥ e.endp then some (false, st)
      else
        let c := e.c pfx
        let hit := e.ch ptr == c
        let ptr := ptr + 1
        if !hit then
          if ptr ≥ e.endp then some (false, st)
          else searchOuter e code plen skip fl pfx fuel ptr st
        else if ptr ≥ e.endp then some (false, st)
        else searchInner e code plen skip fl pfx fuel ptr 1 { st with mustAdvance := false }

  /-- The `do ... while (i != 0)`, `Modules/_sre/sre_lib.h:1853-1875`. `overlap[i]` is the word
  `prefix + prefix_len - 1 + i`. -/
  def searchInner (e : Env) (code plen skip fl pfx : Nat) : (fuel ptr i : Nat) → SSt → SR
    | 0, _, _, _ => none
    | fuel + 1, ptr, i, st =>
      let next (ptr i : Nat) (st : SSt) : SR :=
        let i := e.c (pfx + plen - 1 + i)
        if i != 0 then searchInner e code plen skip fl pfx fuel ptr i st
        else searchOuter e code plen skip fl pfx fuel ptr st
      if e.ch ptr == e.c (pfx + i) then
        let i := i + 1
        if i != plen then
          let ptr := ptr + 1
          if ptr ≥ e.endp then some (false, st)
          else searchInner e code plen skip fl pfx fuel ptr i st
        else
          let st := { st with start := ptr + 1 - plen, ptr := ptr + 1 + skip - plen }
          if fl &&& 2 != 0 then some (true, st)
          else
            match matchAt e e.mfuel (code + 2 * skip) false st with
            | none => none
            | some (true, st) => some (true, st)
            | some (false, st) =>
              let ptr := ptr + 1
              if ptr ≥ e.endp then some (false, st)
              else next ptr i (resetGroups st)
      else next ptr i st
end

/-- The `for (;;)` of the charset prefix, `Modules/_sre/sre_lib.h:1884-1897`. -/
def searchSet (e : Env) (code set : Nat) : (fuel ptr : Nat) → SSt → SR
  | 0, _, _ => none
  | fuel + 1, ptr, st =>
    if ptr ≥ e.endp then some (false, st)
    else if !e.charset set (e.ch ptr) then searchSet e code set fuel (ptr + 1) st
    else
      match matchAt e e.mfuel code false { st with start := ptr, ptr } with
      | none => none
      | some (true, st) => some (true, st)
      | some (false, st) => searchSet e code set fuel (ptr + 1) (resetGroups st)

/-- The general `while`, `Modules/_sre/sre_lib.h:1912-1918`. -/
def searchGen (e : Env) (code lim : Nat) : (fuel ptr : Nat) → SSt → SR
  | 0, _, _ => none
  | fuel + 1, ptr, st =>
    if ptr < lim then
      let ptr := ptr + 1
      let st := resetGroups st
      match matchAt e e.mfuel code false { st with start := ptr, ptr } with
      | none => none
      | some (true, st) => some (true, st)
      | some (false, st) => searchGen e code lim fuel ptr st
    else some (false, st)

/-- `SRE(search)`, `Modules/_sre/sre_lib.h:1746-1922`. -/
def sreSearch (e : Env) (st : SSt) : SR :=
  let ptr := st.start
  if ptr > e.endp then some (false, st)
  else
    let fuel := e.s.size + e.endp + 8
    let hasInfo := e.c 0 == OP_INFO
    let fl := if hasInfo then e.c 2 else 0
    let mn := if hasInfo then e.c 3 else 0
    if hasInfo ∧ mn != 0 ∧ e.endp - ptr < mn then some (false, st)
    else
      let lim := if mn > 1 then max ptr (e.endp - (mn - 1)) else e.endp
      let code := if hasInfo then 1 + e.c 1 else 0
      if fl &&& 1 != 0 then
        let plen := e.c 5
        let skip := e.c 6
        if plen == 1 then
          searchLit e code (e.c 7) skip fl (2 * fuel) ptr { st with mustAdvance := false }
        else if plen > e.endp - ptr then some (false, st)
        else searchOuter e code plen skip fl 7 (4 * fuel + 4 * e.code.size) ptr st
      else if fl &&& 4 != 0 then
        searchSet e code 5 fuel ptr { st with mustAdvance := false }
      else
        match matchAt e e.mfuel code true { st with start := ptr, ptr } with
        | none => none
        | some (true, st) => some (true, { st with mustAdvance := false })
        | some (false, st) =>
          let st := { st with mustAdvance := false }
          if e.c code == OP_AT ∧ (e.c (code + 1) == 0 ∨ e.c (code + 1) == 2) then
            some (false, { st with start := e.endp, ptr := e.endp })
          else searchGen e code lim fuel ptr st

end PyLean.TextLibs.Re
