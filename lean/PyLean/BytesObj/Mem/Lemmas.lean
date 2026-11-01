import PyLean.BytesObj.Mem.Model

/-!
Facts about the byte store and the state monad used by the memoryview properties.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## Reading and writing -/

theorem rdBytes_length (m : Mem) (p : Int) (n : Nat) : (rdBytes m p n).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [rdBytes, ih]

theorem encLE_length (x k : Nat) : (encLE x k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [encLE, ih]

theorem decLE_encLE (x k : Nat) : decLE (encLE x k) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [encLE, decLE, Nat.mod_one]
  | succ k ih =>
    simp only [encLE, decLE, ih]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

theorem wrBytes_length (m : Mem) (p : Int) (bs : List Nat) : (wrBytes m p bs).length = m.length := by
  induction bs generalizing m p with
  | nil => rfl
  | cons b bs ih => simp [wrBytes, ih]

/-- A write leaves the bytes outside its range alone. -/
theorem wrBytes_getD_out (m : Mem) (p : Int) (bs : List Nat) (i : Nat) (d : Nat) (hp : 0 ≤ p)
    (h : (i : Int) < p ∨ p + bs.length ≤ i) : (wrBytes m p bs).getD i d = m.getD i d := by
  induction bs generalizing m p with
  | nil => rfl
  | cons b bs ih =>
    simp only [wrBytes]
    rw [ih _ _ (by omega) (by simp only [List.length_cons] at h; omega)]
    have : p.toNat ≠ i := by simp only [List.length_cons] at h; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_set, this]

theorem rdByte_wrBytes_out (m : Mem) (p q : Int) (bs : List Nat) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : q < p ∨ p + bs.length ≤ q) : rdByte (wrBytes m p bs) q = rdByte m q := by
  unfold rdByte
  exact wrBytes_getD_out m p bs q.toNat 0 hp (by omega)

/-- What a write puts in its range, for a range inside the store. -/
theorem rdBytes_wrBytes (m : Mem) (p : Int) (bs : List Nat) (hp : 0 ≤ p)
    (h : p + bs.length ≤ m.length) : rdBytes (wrBytes m p bs) p bs.length = bs := by
  induction bs generalizing m p with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at h
    simp only [wrBytes, List.length_cons, rdBytes]
    have hlen : (m.set p.toNat b).length = m.length := by simp
    rw [ih _ _ (by omega) (by rw [hlen]; omega)]
    congr 1
    rw [rdByte_wrBytes_out _ _ _ _ (by omega) hp (by omega)]
    unfold rdByte
    have : p.toNat < m.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_set, this]

/-- Reading past a write. -/
theorem rdBytes_out (m : Mem) (p q : Int) (bs : List Nat) (n : Nat) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : q + n ≤ p ∨ p + bs.length ≤ q) : rdBytes (wrBytes m p bs) q n = rdBytes m q n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [rdBytes]
    rw [rdByte_wrBytes_out _ _ _ _ hp hq (by omega), ih _ (by omega) (by omega)]

theorem rdBytes_append (m : Mem) (p : Int) (a b : Nat) :
    rdBytes m p (a + b) = rdBytes m p a ++ rdBytes m (p + a) b := by
  induction a generalizing p with
  | zero => simp [rdBytes]
  | succ a ih =>
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this]
    simp only [rdBytes, List.cons_append]
    rw [ih (p + 1)]
    congr 2
    congr 1
    omega

/-- Writes compose. -/
theorem wrBytes_append (m : Mem) (p : Int) (a b : List Nat) :
    wrBytes (wrBytes m p a) (p + a.length) b = wrBytes m p (a ++ b) := by
  induction a generalizing m p with
  | nil => simp [wrBytes]
  | cons x a ih =>
    simp only [wrBytes, List.cons_append, List.length_cons]
    rw [← ih]
    congr 1
    omega

/-! ## The state monad -/

@[simp] theorem checkReleased_ok (st : St) (i : Nat) (h : baseInaccessible st i = false) :
    checkReleased i st = (.ok (), st) := by
  simp [checkReleased, h]

theorem checkReleased_err (st : St) (i : Nat) (h : baseInaccessible st i = true) :
    checkReleased i st = (.error releasedError, st) := by
  simp [checkReleased, h]

theorem checkRestricted_ok (st : St) (i : Nat) (h : (st.mv i).flags.restricted = false) :
    checkRestricted i st = (.ok (), st) := by
  simp [checkRestricted, h]

theorem bind_err {α β : Type} (x : M α) (f : α → M β) (st st' : St) (e : PyExc)
    (h : x st = (.error e, st')) : (x >>= f) st = (.error e, st') := by
  rw [M.bind_app, h]

theorem bind_ok {α β : Type} (x : M α) (f : α → M β) (st st' : St) (a : α)
    (h : x st = (.ok a, st')) : (x >>= f) st = f a st' := by
  rw [M.bind_app, h]

/-! ## Handles -/

theorem St.mv_setMv (st : St) (i : Nat) (x : MV) (h : i < st.mvs.length) :
    (st.setMv i x).mv i = x := by
  simp [St.mv, St.setMv, List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem St.mv_setMv_ne (st : St) (i j : Nat) (x : MV) (h : i ≠ j) :
    (st.setMv i x).mv j = st.mv j := by
  simp [St.mv, St.setMv, List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem St.mb_setMb (st : St) (i : Nat) (x : MBuf) (h : i < st.mbufs.length) :
    (st.setMb i x).mb i = x := by
  simp [St.mb, St.setMb, List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem St.mb_setMb_ne (st : St) (i j : Nat) (x : MBuf) (h : i ≠ j) :
    (st.setMb i x).mb j = st.mb j := by
  simp [St.mb, St.setMb, List.getD_eq_getElem?_getD, List.getElem?_set, h]

@[simp] theorem St.mv_setMb (st : St) (i j : Nat) (x : MBuf) : (st.setMb i x).mv j = st.mv j := rfl
@[simp] theorem St.mb_setMv (st : St) (i j : Nat) (x : MV) : (st.setMv i x).mb j = st.mb j := rfl
@[simp] theorem St.mem_setMv (st : St) (i : Nat) (x : MV) : (st.setMv i x).mem = st.mem := rfl
@[simp] theorem St.mem_setMb (st : St) (i : Nat) (x : MBuf) : (st.setMb i x).mem = st.mem := rfl

end PyLean.BytesObj.Mem
