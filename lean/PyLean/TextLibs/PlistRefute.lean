import PyLean.TextLibs.PlistRoundTrip5

/-! Refutations: the unbounded readings of the reader and round-trip theorems. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-- An XML parser and writer that are never reached (the inputs below are binary). -/
def unusedXml : XmlParse := fun _ _ _ => .error invalidFile
def unusedXmlW : XmlWrite := fun _ _ _ _ => .error invalidFile

/-- `n` nested one-element arrays around the string `"seed"`, as `test_plistlib.test_deep_nesting`
builds them (references and offsets of one byte). -/
def deepChain (n : Nat) : List Nat :=
  let objs : List (List Nat) :=
    (List.range n).map (fun i => [0xA1, i + 1]) ++ [[0x54] ++ asciiBytes "seed"]
  let offs := (objs.foldl (fun (acc : List Nat × Nat) o => (acc.1 ++ [acc.2], acc.2 + o.length)) ([], 8)).1
  let body := objs.flatten
  asciiBytes "bplist00" ++ body ++ offs ++ [0, 0, 0, 0, 0, 0, 1, 1] ++ beBytes (n + 1) 8 ++
    beBytes 0 8 ++ beBytes (8 + body.length) 8

/-- The unbounded reading of `LoadsBinaryInvalidOnly`: sixteen frames (more than any plist without
nested containers needs) suffice for every binary plist. -/
def LoadsBinaryAnyDepth : Prop :=
  ∀ (xml : XmlParse) (buf : List Nat) (aware : Bool) (e : PyExc),
    loadsR xml 16 (.bytes buf) .binary aware = .error e → e = invalidFile

theorem loadsBinaryAnyDepth_refuted : ¬ LoadsBinaryAnyDepth := by
  intro h
  have := h unusedXml (deepChain 11) false recErr (by decide)
  exact absurd this (by decide)

def cfg0 : WCfg := ⟨true, false, false, fun u => .ok u⟩

/-- A naive datetime within `datetime.min..datetime.max` written alone in the binary format is
read back as the same datetime. -/
def BinaryDateRoundTrip : Prop :=
  ∀ (xml : XmlParse) (xmlw : XmlWrite) (us : Int) (b : List Nat), dtMinUs ≤ us → us ≤ dtMaxUs →
    dumpsR xmlw 50 [.date us none] 0 .binary cfg0 = .ok b →
    ∃ res, loadsR xml 50 (.bytes b) .none false = .ok res ∧
      res.objs[res.root]? = some (some (.date us false))

/-- What `dumps(datetime.datetime.max, fmt=FMT_BINARY)` writes. -/
def dmaxBytes : List Nat :=
  [98, 112, 108, 105, 115, 116, 48, 48, 51, 66, 77, 98, 210, 60, 128, 0, 0, 8, 0, 0, 0, 0, 0, 0, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17]

theorem binaryDateRoundTrip_refuted : ¬ BinaryDateRoundTrip := by
  intro h
  obtain ⟨res, hres, _⟩ := h unusedXml unusedXmlW dtMaxUs dmaxBytes (by decide) (by decide)
    (by decide +kernel)
  have : loadsR unusedXml 50 (.bytes dmaxBytes) .none false = .error invalidFile := by decide +kernel
  rw [this] at hres
  cases hres

/-- The bits of every float survive the binary round trip (`BinaryRoundTrip` only promises an equal
float): two floats in a list come back with their bits. -/
def BinaryFloatBits : Prop :=
  ∀ (xml : XmlParse) (xmlw : XmlWrite) (x y : Nat) (b : List Nat), x < 2 ^ 64 → y < 2 ^ 64 →
    dumpsR xmlw 50 [.list [1, 2], .float x, .float y] 0 .binary cfg0 = .ok b →
    ∃ res r1 r2, loadsR xml 50 (.bytes b) .none false = .ok res ∧
      res.objs[res.root]? = some (some (.arr [r1, r2])) ∧
      res.objs[r1]? = some (some (.real x)) ∧ res.objs[r2]? = some (some (.real y))

/-- What `dumps([0.0, -0.0], fmt=FMT_BINARY)` writes: one float object, referenced twice. -/
def negZeroBytes : List Nat :=
  [98, 112, 108, 105, 115, 116, 48, 48, 162, 1, 1, 35, 0, 0, 0, 0, 0, 0, 0, 0, 8, 11, 0, 0, 0, 0, 0, 0,
   1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20]

theorem binaryFloatBits_refuted : ¬ BinaryFloatBits := by
  intro h
  obtain ⟨res, r1, r2, hres, hroot, _, h2⟩ := h unusedXml unusedXmlW 0 (2 ^ 63) negZeroBytes
    (by decide) (by decide) (by decide +kernel)
  have hl : loadsR unusedXml 50 (.bytes negZeroBytes) .none false =
      .ok ⟨[some (.arr [1, 1]), some (.real 0)], 0⟩ := by decide +kernel
  rw [hl] at hres
  cases hres
  simp at hroot
  obtain ⟨rfl, rfl⟩ := hroot
  simp at h2

/-- `_count_to_size(count)` is the smallest of 1, 2, 4 and 8 bytes that holds `count`, for every
`count < 2**64`. -/
def CountToSizeMinimal : Prop :=
  ∀ n, n < 2 ^ 64 → n < 256 ^ countToSize n ∧
    (countToSize n = 1 ∨ countToSize n = 2 ∨ countToSize n = 4 ∨ countToSize n = 8) ∧
    ∀ s, (s = 1 ∨ s = 2 ∨ s = 4) → s < countToSize n → 256 ^ s ≤ n

theorem countToSizeMinimal_proven : CountToSizeMinimal := by
  intro n hn
  refine ⟨countToSize_lt n hn, ?_, ?_⟩
  · rcases countToSize_cases n with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;> simp [h]
  · intro s hs hlt
    unfold countToSize at hlt
    by_cases h1 : n < 2 ^ 8
    · rw [if_pos h1] at hlt; omega
    · rw [if_neg h1] at hlt
      by_cases h2 : n < 2 ^ 16
      · rw [if_pos h2] at hlt
        rcases hs with rfl | rfl | rfl <;> simp at hlt ⊢ <;> omega
      · rw [if_neg h2] at hlt
        by_cases h3 : n < 2 ^ 32
        · rw [if_pos h3] at hlt
          rcases hs with rfl | rfl | rfl <;> simp at hlt ⊢ <;> omega
        · rw [if_neg h3] at hlt
          rcases hs with rfl | rfl | rfl <;> simp at hlt ⊢ <;> omega

end PyLean.TextLibs.Plist
