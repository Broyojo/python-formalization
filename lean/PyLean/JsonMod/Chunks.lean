import PyLean.JsonMod.Enc

/-!
`_make_iterencode` as the generator it is (Lib/json/encoder.py@3.14.7:265-461), for
`JSONEncoder.iterencode` and `json.dump`, which use the pure-Python generators
even when `_json` is present (`c_make_encoder` is taken only with `_one_shot`,
encoder.py:253).

`pyEnc` in `Enc.lean` computes the joined text; here the chunks are kept, in the
order they are yielded, with the exception that ended the generator: `json.dump`
writes every chunk produced before an exception. `pyIter_join` in
`ChunkProps.lean` relates the two.

With `check_circular=False` a cycle recurses until `RecursionError`, after a
number of chunks that depends on the recursion limit, which is out of scope: the
chunks of that case (`.back`, and a repeated `other`) stop at the first repeat.
-/

namespace PyLean.JsonMod

open PyLean

/-- What a generator produced: the chunks, and the exception that ended it. -/
abbrev Yield := List PStr × Option PyExc

def yRaise (e : PyExc) : Yield := ([], some e)
def yOne (t : PStr) : Yield := ([t], none)
def yCons (t : PStr) (y : Yield) : Yield := (t :: y.1, y.2)

/-- `yield from a`, then `b` unless `a` raised. -/
def yThen (a b : Yield) : Yield :=
  match a.2 with
  | some e => (a.1, some e)
  | none => (a.1 ++ b.1, b.2)

/-- The joined text, or the exception. -/
def yRes : Yield → ER
  | (cs, none) => .ok cs.flatten
  | (_, some e) => .error e

/-- The text of a scalar, computed before anything is yielded: the
`isinstance` chain of `_iterencode_list`, encoder.py:289-307 (`none`: anything
else). -/
def pyScalar (cfg : ECfg) : EVal → Option ER
  | .str s => some (.ok (pyStrEnc cfg s))
  | .none => some (.ok (cs "null"))
  | .bool true => some (.ok (cs "true"))
  | .bool false => some (.ok (cs "false"))
  | .int n => some (intRepr n)
  | .flt b r => some (pyFloatStr cfg b r)
  | _ => none

/-- `if newline_indent is not None: yield newline_indent`, encoder.py:374-375. -/
def nlChunks : Option PStr → List PStr
  | some n => [n]
  | none => []

mutual
/-- `_iterencode(o, _current_indent_level)`, encoder.py:415-449, inlining the
opening of `_iterencode_list` and `_iterencode_dict`. -/
def pyIter (cfg : ECfg) : Nat → Nat → List Nat → EVal → Yield
  | 0, _, _, _ => yRaise .modelFuel
  | f + 1, lvl, seen, v =>
    match v with
    | .str s => yOne (pyStrEnc cfg s)
    | .none => yOne (cs "null")
    | .bool true => yOne (cs "true")
    | .bool false => yOne (cs "false")
    | .int n =>
      match intRepr n with
      | .ok t => yOne t
      | .error e => yRaise e
    | .flt b r =>
      match pyFloatStr cfg b r with
      | .ok t => yOne t
      | .error e => yRaise e
    | .list xs =>
      -- `_iterencode_list`, encoder.py:269-326
      if xs = [] then yOne (cs "[]")
      else
        match cfg.indent with
        | some ind =>
          let nl : PStr := [10] ++ rep ind (lvl + 1)
          yThen (pyIterList cfg f (lvl + 1) seen (cfg.itemSep ++ nl) ([91] ++ nl) 0 xs)
            ([[10] ++ rep ind lvl, [93]], none)
        | none => yThen (pyIterList cfg f lvl seen cfg.itemSep [91] 0 xs) ([[93]], none)
    | .dict kvs =>
      -- `_iterencode_dict`, encoder.py:328-413: `{` is yielded before `sorted`.
      if kvs = [] then yOne (cs "{}")
      else
        yCons [123] <|
        let (lvl', nl, sep) : Nat × Option PStr × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, some ([10] ++ rep ind (lvl + 1)), cfg.itemSep ++ [10] ++ rep ind (lvl + 1))
          | none => (lvl, none, cfg.itemSep)
        match (if cfg.sortKeys then sortItems kvs else .ok kvs) with
        | .error e => yRaise e
        | .ok items =>
          let (y, first) := pyIterItems cfg f lvl' seen nl sep true items
          let close : List PStr :=
            match cfg.indent with
            | some ind => if !first then [[10] ++ rep ind lvl] else []
            | none => []
          yThen y (close ++ [[125]], none)
    | .back _ => yRaise (if cfg.checkCircular then circularErr else recursionErr)
    | .other n t =>
      -- encoder.py:435-449
      if n ∈ seen then yRaise (if cfg.checkCircular then circularErr else recursionErr)
      else
        match cfg.dflt n t with
        | .error e => yRaise e
        | .ok v' => pyIter cfg f lvl (n :: seen) v'
termination_by f _ _ v => (f, sizeOf v)

/-- The `for i, value in enumerate(lst)` loop, encoder.py:286-321: a scalar is
yielded with `buf` in one chunk, a container after `yield buf`. -/
def pyIterList (cfg : ECfg) : Nat → Nat → List Nat → PStr → PStr → Nat → List EVal → Yield
  | _, _, _, _, _, _, [] => ([], none)
  | f, lvl, seen, sep, buf, i, x :: xs =>
    let buf' : PStr := if i ≠ 0 then sep else buf
    let item : Yield :=
      if f = 0 then yRaise .modelFuel
      else
        match pyScalar cfg x with
        | some (.ok t) => yOne (buf' ++ t)
        | some (.error e) => yRaise e
        | none => yCons buf' (pyIter cfg f lvl seen x)
    yThen item (pyIterList cfg f lvl seen sep buf (i + 1) xs)
termination_by f _ _ _ _ _ xs => (f, sizeOf xs)

/-- The `for key, value in items` loop, encoder.py:350-407; also returns `first`. -/
def pyIterItems (cfg : ECfg) : Nat → Nat → List Nat → Option PStr → PStr → Bool → List (EKey × EVal) → Yield × Bool
  | _, _, _, _, _, first, [] => (([], none), first)
  | f, lvl, seen, nl, sep, first, (k, x) :: xs =>
    match pyKeyStr cfg k with
    | .error e => (yRaise e, first)
    | .ok none => pyIterItems cfg f lvl seen nl sep first xs
    | .ok (some ks) =>
      let pre : List PStr := if first then nlChunks nl else [sep]
      let head : Yield := (pre ++ [pyStrEnc cfg ks, cfg.keySep], none)
      let r := pyIterItems cfg f lvl seen nl sep false xs
      (yThen head (yThen (pyIter cfg f lvl seen x) r.1), r.2)
termination_by f _ _ _ _ _ items => (f, sizeOf items)
end

/-- `JSONEncoder.iterencode(o)` (`_one_shot=False`), encoder.py:207-263. -/
def iterencode (cfg : ECfg) (v : EVal) : Yield := pyIter cfg (encFuel cfg v) 0 [] v

/-- `for chunk in iterable: fp.write(chunk)`, Lib/json/__init__.py:180-181:
`wr k c` is what the `k`-th write of `c` raises. Returns the chunks written. -/
def writeAll (wr : Nat → PStr → Option PyExc) : Nat → List PStr → List PStr × Option PyExc
  | _, [] => ([], none)
  | k, c :: cs =>
    match wr k c with
    | some e => ([], some e)
    | none =>
      let r := writeAll wr (k + 1) cs
      (c :: r.1, r.2)

/-- A generator consumed by `writeAll`: a failing write stops it before the
generator's own exception is reached. -/
def dumpTo (wr : Nat → PStr → Option PyExc) (y : Yield) : Yield :=
  let r := writeAll wr 0 y.1
  match r.2 with
  | some e => (r.1, some e)
  | none => (r.1, y.2)

end PyLean.JsonMod
