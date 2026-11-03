import PyLean.UnicodeObj.CodecsErrProps

/-!
The buffers the handlers fill, and the round trips: `surrogateescape` and `surrogatepass` give
back what they replaced, and `backslashreplace` writes escapes that `unicode_escape` decodes back.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## Buffers -/

def repLen : Rep → Nat
  | .str s => s.length
  | .bytes b => b.length

theorem decFill_length : ∀ (k ch : Nat) (acc : List Nat), (decFill k ch acc).length = k + acc.length
  | 0, _, _ => by simp [decFill]
  | k + 1, ch, acc => by simp [decFill, decFill_length k]; omega

theorem writeUnicodeHex_length (c : Nat) : (writeUnicodeHex c).length = hexWidth c := by
  unfold writeUnicodeHex hexWidth
  split <;> (try split) <;> simp

theorem foldl_flat (f : Nat → Nat) (g : Nat → List Nat) (hfg : ∀ x, (g x).length = f x) :
    ∀ (l : List Nat) (acc : Nat), l.foldl (fun acc x => acc + f x) acc = acc + (l.flatMap g).length
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.flatMap_cons, List.length_append]
    rw [foldl_flat f g hfg xs, hfg]; omega

theorem nameBlock_length (g : Nat → Option Str) (c : Nat) : (nameBlock g c).length = nameSize g c := by
  unfold nameBlock nameSize
  cases g c <;> simp [writeUnicodeHex_length]; omega

theorem nameSizeLoop_sum (g : Nat → Option Str) : ∀ (l : List Nat) (imax r : Nat),
    (nameSizeLoop g l imax r).2 =
      r + ((l.take ((nameSizeLoop g l imax r).1 - imax)).flatMap (nameBlock g)).length ∧
    imax ≤ (nameSizeLoop g l imax r).1 ∧ (nameSizeLoop g l imax r).1 - imax ≤ l.length
  | [], imax, r => by simp [nameSizeLoop]
  | c :: cs, imax, r => by
    simp only [nameSizeLoop]
    split
    · simp
    · have ih := nameSizeLoop_sum g cs (imax + 1) (r + nameSize g c)
      have he : (nameSizeLoop g cs (imax + 1) (r + nameSize g c)).1 - imax =
          ((nameSizeLoop g cs (imax + 1) (r + nameSize g c)).1 - (imax + 1)) + 1 := by omega
      refine ⟨?_, by omega, by simp; omega⟩
      rw [he, List.take_succ_cons, List.flatMap_cons, List.length_append, nameBlock_length, ih.1]
      omega

theorem passBytes_length (code : EncCode) (ch : Nat) : (passBytes code ch).length = code.bytelength := by
  cases code <;> rfl

theorem flatMap_const_length (f : Nat → List Nat) (k : Nat) (hf : ∀ x, (f x).length = k) :
    ∀ l : List Nat, (l.flatMap f).length = k * l.length
  | [] => by simp
  | x :: xs => by
    simp [List.flatMap_cons, hf, flatMap_const_length f k hf xs, Nat.mul_succ]; omega

/-- **Every handler fills exactly the buffer it allocated.** The size loops and the write
loops agree, for every object, so the asserts of codecs.c:770, :837, :955, :1003, :1036 and
:1132 hold and nothing is written past the allocation; the decode body of `surrogateescape`
writes at most the four slots of its stack array (:1463). -/
def BuffersExact : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj) (b : Body),
    bodyOf H capi h e = .ok b →
    if h = .surrogateescape ∧ H.isEnc e.cls = false then repLen b.out ≤ b.alloc
    else repLen b.out = b.alloc

theorem params_facts (e : ExcObj) (ab : Bool) (p : Params) (hp : getParams e ab = .ok p) :
    p.stop ≤ p.objlen ∧ p.start ≤ p.objlen ∧ p.objlen = p.obj.length ∧ p.slen = p.stop - p.start := by
  obtain ⟨l, _, rfl⟩ := getParams_ok e ab p hp
  exact ⟨enOf_le e l.length, stOf_le e l.length, rfl, rfl⟩

theorem goal_of_eq {C : Prop} [Decidable C] {x y : Nat} (h : x = y) :
    if C then x ≤ y else x = y := by
  split <;> omega

theorem slice_prefix (l : List Nat) (a i c : Nat) (h : i - a ≤ c - a) :
    slice l a i = (slice l a c).take (i - a) := by
  unfold slice; rw [List.take_take]; congr 1; omega

theorem buffersExact_proven : BuffersExact := by
  intro H capi h e b hb
  have S : ∀ (x : HErr), (Except.error x : HPy Body) = .ok b → False := by
    intro x h; cases h
  cases h with
  | strict => simp [bodyOf] at hb
  | ignore =>
    apply goal_of_eq
    simp only [bodyOf, ignoreErrors] at hb
    split at hb
    · cases hp : getParams e false <;> simp [ignoreError, hp, bind, Except.bind, pure, Except.pure] at hb
      subst hb; simp [repLen]
    · split at hb
      · cases hp : getParams e true <;> simp [ignoreError, hp, bind, Except.bind, pure, Except.pure] at hb
        subst hb; simp [repLen]
      · simp [wrongType, raiseT] at hb
  | replace =>
    apply goal_of_eq
    simp only [bodyOf, replaceErrors] at hb
    split at hb
    · cases hp : getParams e false <;> simp [replaceEncode, hp, bind, Except.bind, pure, Except.pure] at hb
      subst hb; simp [repLen]
    · split at hb
      · cases hc : decodeGetEnd H e <;> simp [replaceDecode, hc, bind, Except.bind, pure, Except.pure] at hb
        subst hb; simp [repLen, replacementChars]
      · split at hb
        · cases hp : getParams e false <;> simp [replaceTranslate, hp, bind, Except.bind, pure, Except.pure] at hb
          subst hb; simp [repLen, replacementChars]
        · simp [wrongType, raiseT] at hb
  | xmlcharrefreplace =>
    apply goal_of_eq
    simp only [bodyOf, xmlCharRefReplaceErrors] at hb
    split at hb
    · simp [wrongType, raiseT] at hb
    · cases hp : getParams e false <;> simp [hp, bind, Except.bind, pure, Except.pure] at hb
      subst hb
      simp only [repLen]
      rw [foldl_flat (fun ch => 2 + nDecimalDigits ch + 1) xmlBlock
        (fun x => by simp [xmlBlock, decFill_length]; omega)]
      simp
  | backslashreplace =>
    apply goal_of_eq
    simp only [bodyOf, backslashReplaceErrors] at hb
    have enc : ∀ b, backslashEncode e = .ok b → repLen b.out = b.alloc := by
      intro b hb
      cases hp : getParams e false <;> simp [backslashEncode, hp, bind, Except.bind, pure, Except.pure] at hb
      subst hb
      simp only [repLen]
      rw [foldl_flat hexWidth writeUnicodeHex writeUnicodeHex_length]
      simp
    split at hb
    · exact enc b hb
    · split at hb
      · cases hp : getParams e true <;> simp [backslashDecode, hp, bind, Except.bind, pure, Except.pure] at hb
        subst hb
        obtain ⟨h1, h2, h3, h4⟩ := params_facts e true _ hp
        simp only [repLen]
        rw [flatMap_const_length byteHex 4 (fun _ => rfl), slice_length _ _ _ (by omega), h4]
      · split at hb
        · exact enc b hb
        · simp [wrongType, raiseT] at hb
  | namereplace =>
    apply goal_of_eq
    simp only [bodyOf, nameReplaceErrors] at hb
    split at hb
    · simp [wrongType, raiseT] at hb
    · cases hcap : capi with
      | error x => rw [hcap] at hb; simp [bind, Except.bind] at hb
      | ok g =>
        rw [hcap] at hb
        cases hp : getParams e false <;> simp [hp, bind, Except.bind, pure, Except.pure] at hb
        rename_i p
        subst hb
        obtain ⟨h1, h2, h3, h4⟩ := params_facts e false _ hp
        simp only [repLen]
        have hs := nameSizeLoop_sum g (slice p.obj p.start p.stop) p.start 0
        have hl := slice_length p.obj p.start p.stop (by omega)
        rw [hs.1, slice_prefix p.obj p.start _ p.stop (by omega)]
        simp
  | surrogatepass =>
    apply goal_of_eq
    simp only [bodyOf, surrogatePassErrors] at hb
    split at hb
    · simp only [surrogatePassEncode] at hb
      cases hc : encCodeOf H e "UnicodeEncodeError" <;> rw [hc] at hb <;> simp only [err_bind, ok_bind] at hb
      · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
      · rename_i code
        split at hb
        · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
        · cases hp : getParams e false <;> rw [hp] at hb <;> simp only [err_bind, ok_bind] at hb
          · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
          · rename_i p
            obtain ⟨h1, h2, h3, h4⟩ := params_facts e false _ hp
            rw [passWrite_eq] at hb
            split at hb
            · simp [bind, Except.bind, pure, Except.pure, bailOn_ok] at hb
              subst hb
              simp only [repLen]
              rw [flatMap_const_length _ code.bytelength (passBytes_length code)]
              have hg : (guardRange code.bytelength p).1 ≤ p.objlen ∧
                  (guardRange code.bytelength p).2 = (guardRange code.bytelength p).1 - p.start := by
                unfold guardRange; split <;> simp <;> omega
              rw [slice_length _ _ _ (by omega), hg.2]
            · rw [bailOn_reraise] at hb
              obtain ⟨x, hx⟩ := bail_isError (α := List Nat) H e
              rw [hx] at hb; simp [bind, Except.bind] at hb
    · split at hb
      · simp only [surrogatePassDecode] at hb
        cases hc : encCodeOf H e "UnicodeDecodeError" <;> rw [hc] at hb <;> simp only [err_bind, ok_bind] at hb
        · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
        · split at hb
          · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
          · cases hp : getParams e true <;> rw [hp] at hb <;> simp only [err_bind, ok_bind] at hb
            · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
            · split at hb <;> split at hb
              all_goals first
                | first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
                | (simp [pure, Except.pure] at hb; subst hb; simp [repLen])
      · simp [wrongType, raiseT] at hb
  | surrogateescape =>
    simp only [bodyOf, surrogateEscapeErrors] at hb
    split at hb
    · rename_i hE
      apply goal_of_eq
      simp only [surrogateEscapeEncode] at hb
      cases hp : getParams e false <;> rw [hp] at hb <;> simp only [err_bind, ok_bind] at hb
      · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
      · rename_i p
        obtain ⟨h1, h2, h3, h4⟩ := params_facts e false _ hp
        rw [escWrite_eq] at hb
        split at hb
        · simp [bind, Except.bind, pure, Except.pure, bailOn_ok] at hb
          subst hb
          simp only [repLen, List.length_map]
          rw [slice_length _ _ _ (by omega), h4]
        · rw [bailOn_reraise] at hb
          obtain ⟨x, hx⟩ := bail_isError (α := List Nat) H e
          rw [hx] at hb; simp [bind, Except.bind] at hb
    · split at hb
      · rename_i hE hD
        simp only [surrogateEscapeDecode] at hb
        cases hp : getParams e true <;> rw [hp] at hb <;> simp only [err_bind, ok_bind] at hb
        · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
        · rename_i p
          split at hb
          · first | exact (S _ hb).elim | exact absurd hb (bail_ne_ok _ _ _)
          · simp [pure, Except.pure] at hb
            subst hb
            have hE' : H.isEnc e.cls = false := by simpa using hE
            simp only [repLen, hE', and_self, if_true]
            have := escConsume_length (min 4 p.slen) (p.obj.drop p.start)
            omega
      · simp [wrongType, raiseT] at hb

end PyLean.UnicodeObj.Codecs
