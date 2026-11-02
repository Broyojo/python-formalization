import PyLean.Ipaddress.Parse4

/-! The IPv4 text format is a bijection: `IPv4Address(s)` accepts exactly the strings
`str(IPv4Address(n))`, and gives `n` back. -/

namespace PyLean.Ipaddress

open PyLean

/-- For every int `n` in `[0, 2**32)`, `IPv4Address(str(IPv4Address(n)))` stores `n`: the documented
`IPv4Address(int(IPv4Address('192.0.2.1'))) == IPv4Address('192.0.2.1')`, from the other side. -/
def V4RoundTrip : Prop :=
  ∀ n : Nat, n < 2 ^ 32 → ipv4Init (.str (ipv4Str n)) = .ok n

/-- For every string `s`, if `IPv4Address(s)` succeeds with `n` then `s` is exactly `str` of that
address: the parser accepts no second spelling (no leading zeros, signs, spaces or non-ASCII
digits), as the comment at ipaddress.py:1229-1230 ("as strict as glibc's inet_pton()") intends. -/
def V4Canonical : Prop :=
  ∀ (s : List Char) (n : Nat), ipv4Init (.str s) = .ok n → n < 2 ^ 32 ∧ ipv4Str n = s

/-! ## Octets, by evaluation -/

def dc (k : Nat) : Char := Char.ofNat (48 + k)

def okEq (r : Except OctetErr Nat) (d : Nat) : Bool :=
  match r with | .ok v => v == d | .error _ => false

/-- A character of a dotted quad: a digit or the dot. -/
def quadC (c : Char) : Bool := isDigitC c || c == '.'

def reprB (d : Nat) : Bool :=
  okEq (parseOctet (toString d).toList) d && (toString d).toList.all isDigitC &&
    !(toString d).toList.isEmpty

set_option maxRecDepth 20000 in
theorem reprB_all : ∀ d, d < 256 → reprB d = true := by decide

theorem octet_repr (d : Nat) (h : d < 256) :
    parseOctet (toString d).toList = .ok d ∧ (toString d).toList.all isDigitC = true ∧
      (toString d).toList ≠ [] := by
  have := reprB_all d h
  simp only [reprB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨?_, h2, h3⟩
  unfold okEq at h1
  split at h1
  · rename_i v hv; simp at h1; rw [hv, h1]
  · simp at h1

theorem nodot_of_digits (p : List Char) (h : p.all isDigitC = true) : '.' ∉ p := by
  intro m
  have := List.all_eq_true.mp h '.' m
  revert this; decide

def canonB (s : List Char) : Bool :=
  match parseOctet s with
  | .ok v => decide (v < 256) && (toString v).toList == s
  | .error _ => true

set_option maxRecDepth 20000 in
theorem canon1 : ∀ a, a < 10 → canonB [dc a] = true := by decide
set_option maxRecDepth 20000 in
theorem canon2 : ∀ a, a < 10 → ∀ b, b < 10 → canonB [dc a, dc b] = true := by decide
set_option maxRecDepth 20000 in
theorem canon3 : ∀ a, a < 10 → ∀ b, b < 10 → ∀ c, c < 10 → canonB [dc a, dc b, dc c] = true := by
  decide

theorem digit_dc (c : Char) (h : isDigitC c = true) : c = dc (c.toNat - 48) ∧ c.toNat - 48 < 10 := by
  simp only [isDigitC, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, by omega⟩
  unfold dc
  rw [show 48 + (c.toNat - 48) = c.toNat by omega, Char.ofNat_toNat]

theorem canonB_all (s : List Char) : canonB s = true := by
  by_cases hd : s.all isDigitC = true
  · match s, hd with
    | [], _ => decide
    | [a], hd =>
      have ha := digit_dc a (by simpa using hd)
      rw [ha.1]; exact canon1 _ ha.2
    | [a, b], hd =>
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
      have ha := digit_dc a hd.1
      have hb := digit_dc b hd.2
      rw [ha.1, hb.1]; exact canon2 _ ha.2 _ hb.2
    | [a, b, c], hd =>
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
      have ha := digit_dc a hd.1
      have hb := digit_dc b hd.2.1
      have hc := digit_dc c hd.2.2
      rw [ha.1, hb.1, hc.1]; exact canon3 _ ha.2 _ hb.2 _ hc.2
    | a :: b :: c :: d :: rest, hd =>
      have hl : (a :: b :: c :: d :: rest).length > 3 := by simp
      simp [canonB, parseOctet, hd, hl]
  · cases s with
    | nil => decide
    | cons x xs => simp [canonB, parseOctet, hd]

theorem octet_canon (s : List Char) (v : Nat) (h : parseOctet s = .ok v) :
    v < 256 ∧ (toString v).toList = s := by
  have := canonB_all s
  simp only [canonB, h, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this

/-! ## Splitting and joining -/

theorem split_ne_nil (sep : Char) (s : List Char) : splitOn1 sep s ≠ [] := by
  cases s with
  | nil => simp [splitOn1]
  | cons c cs =>
    unfold splitOn1
    split
    · simp
    · split <;> simp

theorem join_cons_cons (sep c : Char) (p : List Char) (ps : List (List Char)) :
    joinOn1 sep ((c :: p) :: ps) = c :: joinOn1 sep (p :: ps) := by
  cases ps <;> simp [joinOn1]

theorem join_split (sep : Char) (s : List Char) : joinOn1 sep (splitOn1 sep s) = s := by
  induction s with
  | nil => simp [splitOn1, joinOn1]
  | cons c cs ih =>
    unfold splitOn1
    by_cases hc : c = sep
    · subst hc
      simp only [if_true]
      cases hsp : splitOn1 c cs with
      | nil => exact absurd hsp (split_ne_nil c cs)
      | cons p ps => rw [hsp] at ih; simp [joinOn1, ih]
    · simp only [hc, if_false]
      cases hsp : splitOn1 sep cs with
      | nil => exact absurd hsp (split_ne_nil sep cs)
      | cons p ps => rw [hsp] at ih; simp only; rw [join_cons_cons, ih]

theorem split_nosep (sep : Char) (p : List Char) (h : sep ∉ p) : splitOn1 sep p = [p] := by
  induction p with
  | nil => simp [splitOn1]
  | cons c cs ih =>
    have hc : c ≠ sep := by intro e; subst e; simp at h
    have h' : sep ∉ cs := by intro m; exact h (by simp [m])
    simp [splitOn1, hc, ih h']

theorem split_append (sep : Char) (p t : List Char) (h : sep ∉ p) :
    splitOn1 sep (p ++ sep :: t) = p :: splitOn1 sep t := by
  induction p with
  | nil => simp [splitOn1]
  | cons c cs ih =>
    have hc : c ≠ sep := by intro e; subst e; simp at h
    have h' : sep ∉ cs := by intro m; exact h (by simp [m])
    simp [splitOn1, hc, ih h']

theorem split_join (sep : Char) (parts : List (List Char)) (hne : parts ≠ [])
    (h : ∀ p ∈ parts, sep ∉ p) : splitOn1 sep (joinOn1 sep parts) = parts := by
  induction parts with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases ps with
    | nil => simp [joinOn1, split_nosep sep p (h p (by simp))]
    | cons q qs =>
      simp only [joinOn1]
      rw [split_append sep p _ (h p (by simp)), ih (by simp) (fun r hr => h r (by simp [hr]))]

/-! ## Bytes -/

theorem from_to_bytes (n : Nat) (h : n < 2 ^ 32) : fromBytesBig (toBytes4 n) = n := by
  simp [fromBytesBig, toBytes4]; omega

theorem to_from_bytes (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    toBytes4 (fromBytesBig [a, b, c, d]) = [a, b, c, d] ∧ fromBytesBig [a, b, c, d] < 2 ^ 32 := by
  simp [fromBytesBig, toBytes4]; omega

/-! ## The two directions -/

theorem all_join (f : Char → Bool) (sep : Char) (parts : List (List Char)) (hs : f sep = true)
    (h : ∀ p ∈ parts, p.all f = true) : (joinOn1 sep parts).all f = true := by
  induction parts with
  | nil => simp [joinOn1]
  | cons p ps ih =>
    cases ps with
    | nil => simpa [joinOn1] using h p (by simp)
    | cons q qs =>
      simp only [joinOn1, List.all_append, List.all_cons, Bool.and_eq_true]
      exact ⟨h p (by simp), hs, ih (fun r hr => h r (by simp [hr]))⟩

theorem digits_quad (p : List Char) (h : p.all isDigitC = true) : p.all quadC = true := by
  simp only [List.all_eq_true] at h ⊢
  intro c hc; simp [quadC, h c hc]

theorem v4RoundTrip_proven : V4RoundTrip := by
  intro n hn
  obtain ⟨p1, d1, e1⟩ := octet_repr (n / 2 ^ 24 % 256) (Nat.mod_lt _ (by decide))
  obtain ⟨p2, d2, e2⟩ := octet_repr (n / 2 ^ 16 % 256) (Nat.mod_lt _ (by decide))
  obtain ⟨p3, d3, e3⟩ := octet_repr (n / 2 ^ 8 % 256) (Nat.mod_lt _ (by decide))
  obtain ⟨p4, d4, e4⟩ := octet_repr (n % 256) (Nat.mod_lt _ (by decide))
  have hsplit := split_join '.' [(toString (n / 2 ^ 24 % 256)).toList, (toString (n / 2 ^ 16 % 256)).toList,
      (toString (n / 2 ^ 8 % 256)).toList, (toString (n % 256)).toList] (by simp)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl)
      · exact nodot_of_digits _ d1
      · exact nodot_of_digits _ d2
      · exact nodot_of_digits _ d3
      · exact nodot_of_digits _ d4)
  have hall := all_join quadC '.' [(toString (n / 2 ^ 24 % 256)).toList, (toString (n / 2 ^ 16 % 256)).toList,
      (toString (n / 2 ^ 8 % 256)).toList, (toString (n % 256)).toList] (by decide)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl)
      · exact digits_quad _ d1
      · exact digits_quad _ d2
      · exact digits_quad _ d3
      · exact digits_quad _ d4)
  have hslash : '/' ∉ joinOn1 '.' [(toString (n / 2 ^ 24 % 256)).toList, (toString (n / 2 ^ 16 % 256)).toList,
      (toString (n / 2 ^ 8 % 256)).toList, (toString (n % 256)).toList] := by
    intro m
    have := List.all_eq_true.mp hall '/' m
    revert this; decide
  have hne : (joinOn1 '.' [(toString (n / 2 ^ 24 % 256)).toList, (toString (n / 2 ^ 16 % 256)).toList,
      (toString (n / 2 ^ 8 % 256)).toList, (toString (n % 256)).toList]).isEmpty = false := by
    simp [joinOn1]
  have hb := from_to_bytes n hn
  simp only [toBytes4] at hb
  simp only [ipv4Init, ipv4Str, stringFromIpInt4, toBytes4, List.map_cons, List.map_nil]
  rw [if_neg hslash]
  unfold ipIntFromString4
  rw [if_neg (by simp only [hne]; decide), hsplit]
  simp only [parseOctets, p1, p2, p3, p4, Except.map]
  simp [hb]

theorem v4Canonical_proven : V4Canonical := by
  intro s n h
  simp only [ipv4Init] at h
  split at h
  · simp at h
  · unfold ipIntFromString4 at h
    split at h
    · simp at h
    · dsimp only at h
      split at h
      · simp at h
      · rename_i hlen
        split at h
        · rename_i bs hbs
          simp only [Except.ok.injEq] at h
          subst h
          have hjs := join_split '.' s
          generalize splitOn1 '.' s = parts at hbs hlen hjs
          match parts, hlen, hbs, hjs with
          | [o1, o2, o3, o4], _, hbs, hjs =>
            cases e1 : parseOctet o1 <;> simp [parseOctets, e1, Except.map] at hbs
            rename_i b1
            cases e2 : parseOctet o2 <;> simp [e2] at hbs
            rename_i b2
            cases e3 : parseOctet o3 <;> simp [e3] at hbs
            rename_i b3
            cases e4 : parseOctet o4 <;> simp [e4] at hbs
            rename_i b4
            subst hbs
            obtain ⟨l1, r1⟩ := octet_canon o1 b1 e1
            obtain ⟨l2, r2⟩ := octet_canon o2 b2 e2
            obtain ⟨l3, r3⟩ := octet_canon o3 b3 e3
            obtain ⟨l4, r4⟩ := octet_canon o4 b4 e4
            obtain ⟨tb, lt⟩ := to_from_bytes b1 b2 b3 b4 l1 l2 l3 l4
            refine ⟨lt, ?_⟩
            simp only [ipv4Str, stringFromIpInt4, tb, List.map_cons, List.map_nil, r1, r2, r3, r4]
            exact hjs
          | [], h, _, _ | [_], h, _, _ | [_, _], h, _, _ | [_, _, _], h, _, _ => simp at h
          | _ :: _ :: _ :: _ :: _ :: _, h, _, _ => simp at h
        · simp at h

/-- The other two arguments of `IPv4Address`: an int is accepted exactly in `[0, 2**32)` and
stored as is; four bytes `ip.to_bytes(4, 'big')` give `ip` back, and any other length raises
`AddressValueError`. -/
def V4InitIntBytes : Prop :=
  (∀ (v : Int) (n : Nat), ipv4Init (.int v) = .ok n ↔ (0 ≤ v ∧ v < 2 ^ 32 ∧ (n : Int) = v)) ∧
  (∀ n : Nat, n < 2 ^ 32 → ipv4Init (.bytes (toBytes4 n)) = .ok n) ∧
  (∀ b : List Nat, b.length ≠ 4 →
    ipv4Init (.bytes b) = .error (.named "AddressValueError" "~(len != 4) is not permitted as an IPv4 address"))

theorem v4InitIntBytes_proven : V4InitIntBytes := by
  refine ⟨fun v n => ?_, fun n hn => ?_, fun b hb => ?_⟩
  · have hA : ((allOnes 32 : Nat) : Int) = 4294967295 := by simp [allOnes]
    simp only [ipv4Init, checkIntAddress, hA]
    by_cases h0 : v < 0
    · simp [h0]; omega
    · by_cases h1 : v > 4294967295
      · simp [h0, h1]; omega
      · simp [h0, h1]; omega
  · have := from_to_bytes n hn
    simp only [ipv4Init, toBytes4, List.length_cons, List.length_nil] at this ⊢
    simp [this]
  · simp [ipv4Init, hb]

end PyLean.Ipaddress
