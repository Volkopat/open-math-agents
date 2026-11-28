import OMAStatements.S_oeis_a271804

open OMA.S_oeis_a271804 PowerSeries

namespace Scale401

def transitions : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 1, 1, 2, 3, 3, 4], #[1, 1, 1, 1, 4, 4, 4, 4], #[0, 5, 6, 1, 3, 7, 8, 9], #[0, 1, 1, 1, 2, 3, 3, 4], #[1, 1, 1, 1, 4, 4, 4, 4], #[1, 5, 1, 1, 10, 11, 4, 10], #[1, 1, 6, 1, 12, 4, 13, 12], #[1, 5, 1, 14, 10, 15, 16, 8], #[1, 1, 6, 14, 12, 16, 17, 7], #[1, 5, 6, 1, 9, 11, 13, 9], #[1, 5, 1, 1, 10, 11, 4, 10], #[0, 5, 1, 14, 17, 10, 18, 8], #[1, 1, 6, 1, 12, 4, 13, 12], #[0, 1, 6, 14, 15, 18, 12, 7], #[1, 1, 1, 14, 4, 16, 16, 19], #[0, 5, 1, 1, 17, 7, 3, 10]],
  #[#[1, 1, 1, 14, 4, 16, 16, 19], #[0, 1, 6, 1, 15, 3, 8, 12], #[0, 1, 1, 14, 2, 18, 18, 19], #[1, 5, 6, 14, 9, 15, 17, 16]]]

def outputs : Array Bool := #[true, false, false, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false, true]

def lit (q : ℕ) := outputs[q]?.getD false

def code (t x y : Bool) := 4 * t.toNat + 2 * x.toNat + y.toNat

def go (q : ℕ) (t x y : Bool) : ℕ :=
  (((transitions[q / 16]?.getD #[])[q % 16]?.getD #[])[code t x y]?).getD 0

def digit (n : ℕ) (b : Bool) : ℕ := 2 * n + b.toNat

def prev (n : ℕ) : ℕ := if n = 0 then 1 else n - 1

lemma digit_half (n : ℕ) (b : Bool) : digit n b / 2 = n := by
  cases b <;> simp [digit] <;> omega

lemma digit_parity (n : ℕ) (b : Bool) : (digit n b % 2 == 1) = b := by
  cases b <;> simp [digit] <;> omega

lemma digit_zero (n : ℕ) (b : Bool) : (digit n b == 0) = ((n == 0) && !b) := by
  cases b <;> simp [digit]

lemma digit_next (n : ℕ) (b : Bool) :
    digit n b + 1 = digit (if b then n + 1 else n) (!b) := by
  cases b <;> simp [digit] <;> omega

lemma digit_prev (n : ℕ) (b : Bool) :
    prev (digit n b) = digit (if b || (n == 0) then n else prev n) (!b) := by
  cases n <;> cases b <;> simp [digit, prev] <;> omega

def address : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | w + 1, t, x, y => go (address w (t / 2) (x / 2) (y / 2)) (t % 2 == 1) (x % 2 == 1) (y % 2 == 1)

lemma address_digit (w t x y : ℕ) (bt bx by' : Bool) :
    address (w + 1) (digit t bt) (digit x bx) (digit y by') =
      go (address w t x y) bt bx by' := by
  simp only [address, digit_half, digit_parity]

structure Local where
  c : ℕ
  next : ℕ
  left : ℕ
  right : ℕ
  down : ℕ
  up : ℕ
  zx : Bool
  zy : Bool
  zt : Bool
  deriving DecidableEq, Inhabited

def position (w t x y : ℕ) : Local :=
  ⟨address (w + 1) t x y, address (w + 1) (t + 1) x y,
   address (w + 1) t (prev x) y, address (w + 1) t (x + 1) y,
   address (w + 1) t x (prev y), address (w + 1) t x (y + 1), x == 0, y == 0, t == 0⟩

def descend (g : Local) (t x y : Bool) : Local :=
  ⟨go g.c t x y, go (if t then g.next else g.c) (!t) x y,
   go (if x || g.zx then g.c else g.left) t (!x) y,
   go (if x then g.right else g.c) t (!x) y,
   go (if y || g.zy then g.c else g.down) t x (!y),
   go (if y then g.up else g.c) t x (!y),
   g.zx && !x, g.zy && !y, g.zt && !t⟩

lemma position_digit (w t x y : ℕ) (bt bx by' : Bool) :
    position (w + 1) (digit t bt) (digit x bx) (digit y by') =
      descend (position w t x y) bt bx by' := by
  simp only [position, descend, digit_next, digit_prev, digit_zero, address_digit]
  cases bt <;> cases bx <;> cases by' <;> by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [hx, hy]

def localRule (r : ℕ) (c l h d u : Bool) : Bool :=
  r.testBit (c.toNat + 2 * (l.toNat + h.toNat + d.toNat + u.toNat))

def valid (s : Local) : Prop :=
  (s.zt = true → lit s.c = (s.zx && s.zy)) ∧
  lit s.next = localRule 401 (lit s.c) (lit s.left) (lit s.right) (lit s.down) (lit s.up) ∧
  lit s.next = localRule 409 (lit s.c) (lit s.left) (lit s.right) (lit s.down) (lit s.up)

instance (s : Local) : Decidable (valid s) := by unfold valid; infer_instance

def windows : Array (Array Local) := #[
  #[⟨0, 2, 1, 1, 1, 1, true, true, true⟩, ⟨1, 3, 1, 1, 0, 1, true, false, true⟩, ⟨1, 3, 0, 1, 1, 1, false, true, true⟩, ⟨1, 4, 1, 1, 1, 1, false, false, true⟩, ⟨2, 0, 3, 3, 3, 3, true, true, false⟩, ⟨3, 5, 4, 4, 2, 4, true, false, false⟩, ⟨3, 6, 2, 4, 4, 4, false, true, false⟩, ⟨4, 1, 3, 4, 3, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, true, false, true⟩, ⟨4, 0, 4, 4, 3, 4, true, false, false⟩, ⟨4, 1, 4, 4, 4, 4, true, false, false⟩, ⟨4, 1, 4, 4, 4, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, true, true⟩, ⟨4, 0, 3, 4, 4, 4, false, true, false⟩, ⟨4, 1, 4, 4, 4, 4, false, true, false⟩, ⟨0, 3, 6, 6, 5, 5, true, true, false⟩],
  #[⟨5, 7, 1, 1, 0, 0, true, false, false⟩, ⟨6, 8, 0, 0, 1, 1, false, true, false⟩, ⟨1, 9, 5, 1, 6, 1, false, false, false⟩, ⟨3, 0, 8, 8, 7, 7, true, true, false⟩, ⟨7, 1, 9, 9, 3, 2, true, false, false⟩, ⟨8, 1, 3, 2, 9, 9, false, true, false⟩, ⟨9, 1, 7, 3, 8, 3, false, false, false⟩, ⟨0, 2, 1, 1, 5, 1, true, false, false⟩, ⟨1, 3, 1, 1, 0, 1, true, false, false⟩, ⟨1, 3, 0, 1, 1, 1, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, false, false⟩, ⟨2, 1, 3, 3, 7, 3, true, false, false⟩, ⟨3, 1, 2, 4, 9, 4, false, false, false⟩, ⟨0, 2, 6, 1, 1, 1, false, true, false⟩, ⟨1, 3, 1, 1, 0, 1, false, false, false⟩, ⟨1, 3, 0, 1, 1, 1, false, true, false⟩],
  #[⟨2, 1, 8, 3, 3, 3, false, true, false⟩, ⟨3, 1, 9, 4, 2, 4, false, false, false⟩, ⟨1, 4, 1, 1, 1, 1, true, false, false⟩, ⟨1, 4, 1, 1, 1, 1, false, true, false⟩, ⟨0, 2, 1, 1, 1, 1, true, true, false⟩, ⟨3, 1, 4, 4, 2, 10, true, false, false⟩, ⟨3, 1, 2, 12, 4, 4, false, true, false⟩, ⟨1, 10, 1, 1, 1, 5, true, false, false⟩, ⟨5, 11, 1, 1, 1, 0, true, false, false⟩, ⟨1, 10, 5, 1, 1, 1, false, false, false⟩, ⟨10, 1, 4, 4, 3, 11, true, false, false⟩, ⟨11, 5, 10, 10, 10, 2, true, false, false⟩, ⟨4, 1, 10, 4, 4, 10, false, false, false⟩, ⟨10, 14, 11, 4, 4, 3, false, false, false⟩, ⟨1, 12, 1, 6, 1, 1, false, true, false⟩, ⟨6, 13, 1, 0, 1, 1, false, true, false⟩],
  #[⟨1, 12, 1, 1, 6, 1, false, false, false⟩, ⟨12, 1, 3, 13, 4, 4, false, true, false⟩, ⟨4, 1, 4, 12, 12, 4, false, false, false⟩, ⟨13, 6, 12, 2, 12, 12, false, true, false⟩, ⟨12, 14, 4, 3, 13, 4, false, false, false⟩, ⟨4, 5, 10, 4, 4, 4, false, false, false⟩, ⟨4, 6, 4, 4, 12, 4, false, false, false⟩, ⟨4, 1, 3, 16, 3, 16, false, false, false⟩, ⟨5, 15, 14, 14, 1, 0, true, false, false⟩, ⟨1, 16, 1, 1, 1, 14, false, false, false⟩, ⟨14, 8, 5, 5, 1, 6, false, false, false⟩, ⟨10, 1, 16, 16, 3, 15, true, false, false⟩, ⟨15, 1, 8, 8, 10, 3, true, false, false⟩, ⟨16, 1, 10, 9, 4, 8, false, false, false⟩, ⟨8, 1, 15, 11, 16, 8, false, false, false⟩, ⟨1, 16, 1, 14, 1, 1, false, false, false⟩],
  #[⟨6, 17, 1, 0, 14, 14, false, true, false⟩, ⟨14, 7, 1, 5, 6, 6, false, false, false⟩, ⟨12, 1, 3, 17, 16, 16, false, true, false⟩, ⟨16, 1, 4, 7, 12, 9, false, false, false⟩, ⟨17, 1, 12, 3, 7, 7, false, true, false⟩, ⟨7, 1, 16, 7, 17, 13, false, false, false⟩, ⟨1, 9, 1, 6, 1, 5, false, false, false⟩, ⟨5, 11, 14, 1, 1, 0, false, false, false⟩, ⟨6, 13, 1, 0, 14, 1, false, false, false⟩, ⟨9, 1, 16, 13, 16, 11, false, false, false⟩, ⟨11, 1, 8, 9, 9, 2, false, false, false⟩, ⟨13, 1, 9, 2, 7, 9, false, false, false⟩, ⟨9, 1, 11, 3, 13, 3, false, false, false⟩, ⟨2, 0, 3, 3, 11, 3, true, false, false⟩, ⟨3, 6, 2, 4, 10, 4, false, false, false⟩, ⟨4, 0, 3, 4, 4, 4, false, false, false⟩],
  #[⟨0, 3, 6, 6, 5, 5, true, false, false⟩, ⟨6, 8, 0, 0, 14, 1, false, false, false⟩, ⟨3, 1, 8, 8, 15, 7, true, false, false⟩, ⟨8, 1, 3, 2, 8, 9, false, false, false⟩, ⟨0, 2, 6, 1, 5, 1, false, false, false⟩, ⟨2, 1, 8, 3, 11, 3, false, false, false⟩, ⟨2, 0, 13, 3, 3, 3, false, true, false⟩, ⟨3, 5, 12, 4, 2, 4, false, false, false⟩, ⟨4, 0, 4, 4, 3, 4, false, false, false⟩, ⟨0, 3, 6, 6, 5, 5, false, true, false⟩, ⟨5, 7, 14, 1, 0, 0, false, false, false⟩, ⟨3, 1, 17, 8, 7, 7, false, true, false⟩, ⟨7, 1, 7, 9, 3, 2, false, false, false⟩, ⟨2, 1, 13, 3, 7, 3, false, false, false⟩, ⟨4, 5, 4, 4, 4, 10, true, false, false⟩, ⟨10, 0, 4, 4, 4, 11, true, false, false⟩],
  #[⟨11, 1, 10, 10, 10, 17, true, false, false⟩, ⟨10, 1, 11, 4, 4, 18, false, false, false⟩, ⟨0, 17, 1, 1, 5, 5, true, false, false⟩, ⟨5, 10, 14, 14, 0, 0, true, false, false⟩, ⟨1, 18, 0, 1, 1, 14, false, false, false⟩, ⟨17, 1, 18, 18, 11, 10, true, false, false⟩, ⟨10, 5, 8, 8, 17, 3, true, false, false⟩, ⟨18, 1, 17, 10, 10, 8, false, false, false⟩, ⟨8, 1, 10, 11, 18, 8, false, false, false⟩, ⟨1, 10, 1, 1, 1, 5, false, false, false⟩, ⟨10, 1, 18, 4, 4, 11, false, false, false⟩, ⟨11, 1, 8, 10, 10, 2, false, false, false⟩, ⟨4, 6, 4, 12, 4, 4, false, true, false⟩, ⟨12, 0, 4, 13, 4, 4, false, true, false⟩, ⟨13, 1, 12, 15, 12, 12, false, true, false⟩, ⟨12, 1, 4, 18, 13, 4, false, false, false⟩],
  #[⟨0, 15, 6, 6, 1, 1, false, true, false⟩, ⟨1, 18, 1, 14, 0, 1, false, false, false⟩, ⟨6, 12, 0, 0, 14, 14, false, true, false⟩, ⟨15, 1, 13, 12, 18, 18, false, true, false⟩, ⟨18, 1, 12, 7, 15, 12, false, false, false⟩, ⟨12, 6, 15, 3, 7, 7, false, true, false⟩, ⟨7, 1, 18, 7, 12, 13, false, false, false⟩, ⟨1, 12, 1, 6, 1, 1, false, false, false⟩, ⟨12, 1, 4, 13, 18, 4, false, false, false⟩, ⟨13, 1, 12, 2, 7, 12, false, false, false⟩, ⟨4, 1, 4, 16, 4, 16, false, false, false⟩, ⟨10, 1, 11, 16, 4, 3, false, false, false⟩, ⟨4, 14, 4, 4, 4, 16, false, false, false⟩, ⟨14, 19, 1, 5, 1, 6, false, false, false⟩, ⟨16, 1, 10, 19, 4, 12, false, false, false⟩, ⟨16, 6, 4, 10, 4, 19, false, false, false⟩],
  #[⟨19, 14, 16, 11, 16, 13, false, false, false⟩, ⟨17, 1, 3, 3, 11, 7, true, false, false⟩, ⟨7, 1, 10, 10, 17, 2, true, false, false⟩, ⟨3, 1, 17, 12, 10, 10, false, false, false⟩, ⟨10, 1, 7, 16, 3, 3, false, false, false⟩, ⟨16, 1, 4, 9, 4, 19, false, false, false⟩, ⟨19, 1, 16, 11, 16, 17, false, false, false⟩, ⟨6, 17, 1, 0, 14, 14, false, false, false⟩, ⟨12, 1, 3, 17, 16, 16, false, false, false⟩, ⟨16, 1, 10, 7, 12, 12, false, false, false⟩, ⟨17, 1, 12, 17, 19, 7, false, false, false⟩, ⟨7, 1, 16, 10, 17, 17, false, false, false⟩, ⟨4, 14, 4, 16, 4, 4, false, false, false⟩, ⟨12, 1, 4, 3, 13, 16, false, false, false⟩, ⟨16, 5, 4, 19, 4, 12, false, false, false⟩, ⟨16, 1, 4, 10, 12, 19, false, false, false⟩],
  #[⟨16, 1, 4, 19, 4, 9, false, false, false⟩, ⟨19, 1, 16, 15, 16, 13, false, false, false⟩, ⟨15, 1, 13, 8, 3, 3, false, true, false⟩, ⟨3, 1, 12, 12, 15, 10, false, false, false⟩, ⟨8, 1, 15, 2, 12, 12, false, true, false⟩, ⟨12, 1, 3, 3, 8, 16, false, false, false⟩, ⟨5, 15, 14, 14, 1, 0, false, false, false⟩, ⟨10, 1, 16, 16, 3, 15, false, false, false⟩, ⟨15, 1, 19, 8, 10, 15, false, false, false⟩, ⟨16, 1, 10, 10, 12, 8, false, false, false⟩, ⟨8, 1, 15, 15, 16, 12, false, false, false⟩, ⟨4, 5, 4, 4, 4, 10, false, false, false⟩, ⟨4, 6, 4, 12, 4, 4, false, false, false⟩, ⟨10, 0, 16, 4, 4, 11, false, false, false⟩, ⟨11, 5, 19, 10, 10, 2, false, false, false⟩, ⟨12, 0, 4, 13, 16, 4, false, false, false⟩],
  #[⟨13, 6, 12, 2, 19, 12, false, false, false⟩, ⟨11, 1, 19, 9, 9, 17, false, false, false⟩, ⟨13, 1, 9, 15, 19, 9, false, false, false⟩, ⟨9, 1, 11, 18, 13, 18, false, false, false⟩, ⟨0, 17, 6, 1, 5, 5, false, false, false⟩, ⟨5, 10, 14, 14, 0, 0, false, false, false⟩, ⟨17, 1, 17, 18, 11, 10, false, false, false⟩, ⟨10, 1, 7, 8, 17, 3, false, false, false⟩, ⟨18, 1, 17, 9, 9, 8, false, false, false⟩, ⟨0, 15, 6, 6, 5, 1, false, false, false⟩, ⟨6, 12, 0, 0, 14, 14, false, false, false⟩, ⟨15, 1, 13, 12, 15, 18, false, false, false⟩, ⟨18, 1, 9, 7, 15, 9, false, false, false⟩, ⟨12, 1, 15, 3, 8, 7, false, false, false⟩, ⟨9, 1, 18, 13, 18, 11, false, false, false⟩, ⟨3, 0, 8, 8, 10, 7, true, false, false⟩],
  #[⟨3, 1, 2, 12, 10, 4, false, false, false⟩, ⟨12, 1, 3, 13, 16, 4, false, false, false⟩, ⟨17, 1, 12, 3, 7, 7, false, false, false⟩, ⟨2, 0, 13, 3, 11, 3, false, false, false⟩, ⟨0, 3, 6, 6, 5, 5, false, false, false⟩, ⟨3, 1, 17, 8, 10, 7, false, false, false⟩, ⟨3, 0, 12, 8, 7, 7, false, true, false⟩, ⟨3, 1, 12, 4, 2, 10, false, false, false⟩, ⟨10, 1, 16, 4, 3, 11, false, false, false⟩, ⟨15, 1, 8, 8, 10, 3, false, false, false⟩, ⟨3, 1, 12, 8, 15, 7, false, false, false⟩, ⟨10, 1, 8, 8, 17, 15, true, false, false⟩, ⟨0, 15, 6, 6, 5, 1, true, false, false⟩, ⟨3, 1, 12, 12, 15, 10, true, false, false⟩, ⟨8, 1, 15, 2, 8, 12, false, false, false⟩, ⟨12, 1, 3, 18, 8, 4, false, false, false⟩],
  #[⟨4, 1, 10, 12, 12, 10, false, false, false⟩, ⟨2, 1, 8, 18, 11, 18, false, false, false⟩, ⟨18, 1, 12, 19, 2, 12, false, false, false⟩, ⟨18, 1, 2, 10, 10, 19, false, false, false⟩, ⟨19, 1, 18, 11, 18, 17, false, false, false⟩, ⟨12, 1, 4, 17, 18, 16, false, false, false⟩, ⟨11, 1, 19, 10, 10, 17, false, false, false⟩, ⟨12, 1, 15, 17, 7, 7, false, true, false⟩, ⟨0, 17, 6, 1, 5, 5, false, true, false⟩, ⟨7, 1, 7, 10, 17, 2, false, false, false⟩, ⟨3, 1, 17, 12, 10, 10, false, true, false⟩, ⟨10, 1, 7, 4, 3, 18, false, false, false⟩, ⟨2, 1, 13, 18, 7, 18, false, false, false⟩, ⟨19, 1, 18, 15, 18, 13, false, false, false⟩, ⟨10, 1, 18, 16, 4, 15, false, false, false⟩, ⟨13, 1, 12, 15, 19, 12, false, false, false⟩],
  #[⟨14, 16, 5, 5, 6, 6, false, false, false⟩, ⟨9, 1, 16, 17, 16, 15, false, false, false⟩, ⟨15, 1, 19, 16, 9, 15, false, false, false⟩, ⟨17, 1, 9, 17, 19, 16, false, false, false⟩, ⟨16, 14, 15, 10, 17, 12, false, false, false⟩, ⟨16, 1, 15, 10, 17, 8, false, false, false⟩, ⟨15, 1, 13, 8, 15, 3, false, false, false⟩, ⟨16, 1, 15, 7, 17, 12, false, false, false⟩, ⟨17, 1, 17, 3, 11, 7, false, false, false⟩, ⟨10, 5, 16, 8, 17, 3, false, false, false⟩, ⟨12, 6, 15, 3, 16, 7, false, false, false⟩, ⟨10, 1, 16, 8, 17, 15, false, false, false⟩, ⟨12, 1, 15, 17, 16, 7, false, false, false⟩, ⟨18, 1, 2, 9, 9, 19, false, false, false⟩, ⟨18, 1, 9, 19, 2, 9, false, false, false⟩, ⟨3, 0, 12, 8, 10, 7, false, false, false⟩],
  #[⟨9, 1, 7, 18, 8, 18, false, false, false⟩, ⟨9, 1, 18, 17, 18, 15, false, false, false⟩, ⟨3, 1, 17, 4, 9, 10, false, false, false⟩, ⟨3, 1, 9, 12, 15, 4, false, false, false⟩]]

def links : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 2, 3, 4, 5, 6, 7], #[8, 8, 3, 3, 9, 10, 11, 11], #[12, 3, 12, 3, 13, 11, 14, 11], #[3, 3, 3, 3, 11, 11, 11, 11], #[15, 16, 17, 18, 19, 20, 21, 22], #[23, 24, 25, 26, 27, 5, 28, 7], #[29, 30, 31, 26, 32, 33, 6, 7], #[26, 26, 26, 26, 7, 11, 11, 11], #[8, 8, 3, 3, 10, 10, 11, 11], #[34, 34, 26, 26, 9, 10, 11, 11], #[34, 34, 26, 26, 10, 10, 11, 11], #[26, 26, 26, 26, 11, 11, 11, 11], #[12, 3, 12, 3, 14, 11, 14, 11], #[35, 26, 35, 26, 13, 11, 14, 11], #[35, 26, 35, 26, 14, 11, 14, 11], #[36, 24, 31, 26, 4, 37, 38, 7]],
  #[#[39, 40, 26, 41, 42, 43, 44, 45], #[46, 26, 47, 48, 49, 50, 51, 52], #[26, 26, 26, 26, 11, 53, 54, 11], #[36, 24, 31, 26, 4, 37, 38, 55], #[39, 56, 57, 58, 59, 60, 61, 62], #[46, 63, 64, 65, 66, 67, 68, 69], #[70, 71, 72, 18, 73, 74, 75, 76], #[23, 24, 25, 26, 77, 5, 78, 7], #[34, 34, 26, 26, 9, 10, 11, 11], #[26, 26, 26, 26, 79, 11, 11, 11], #[26, 26, 26, 26, 11, 11, 11, 11], #[80, 16, 81, 18, 82, 20, 83, 22], #[84, 30, 25, 26, 85, 33, 28, 7], #[29, 30, 31, 26, 86, 87, 6, 7], #[26, 26, 26, 26, 88, 11, 11, 11], #[35, 26, 35, 26, 13, 11, 14, 11]],
  #[#[89, 90, 17, 18, 91, 92, 21, 22], #[84, 30, 25, 26, 93, 33, 28, 7], #[34, 34, 26, 26, 10, 10, 11, 11], #[35, 26, 35, 26, 14, 11, 14, 11], #[36, 24, 31, 26, 4, 5, 6, 7], #[23, 24, 25, 26, 27, 37, 28, 7], #[29, 30, 31, 26, 32, 33, 38, 7], #[34, 34, 26, 26, 10, 94, 11, 11], #[39, 40, 26, 41, 95, 43, 44, 45], #[26, 26, 26, 26, 11, 53, 11, 11], #[39, 40, 26, 41, 42, 96, 44, 97], #[98, 99, 100, 58, 101, 102, 103, 104], #[26, 26, 26, 26, 11, 44, 11, 11], #[105, 71, 26, 41, 106, 107, 44, 45], #[35, 26, 35, 26, 14, 11, 108, 11], #[46, 26, 47, 48, 109, 50, 51, 52]],
  #[#[26, 26, 26, 26, 11, 11, 54, 11], #[46, 26, 47, 48, 49, 50, 110, 111], #[26, 26, 26, 26, 11, 11, 50, 11], #[112, 113, 114, 65, 115, 116, 117, 118], #[119, 26, 72, 48, 120, 50, 121, 52], #[26, 26, 26, 26, 11, 53, 11, 11], #[26, 26, 26, 26, 11, 11, 54, 11], #[26, 26, 26, 26, 7, 11, 11, 122], #[39, 40, 26, 41, 95, 43, 44, 123], #[26, 26, 26, 26, 11, 11, 11, 124], #[26, 63, 57, 125, 122, 126, 127, 128], #[39, 40, 26, 41, 42, 96, 44, 123], #[98, 16, 25, 41, 129, 130, 131, 132], #[26, 63, 57, 125, 122, 126, 133, 134], #[119, 63, 135, 65, 136, 137, 138, 139], #[26, 26, 26, 26, 11, 11, 11, 140]],
  #[#[46, 26, 47, 48, 109, 50, 51, 141], #[26, 63, 57, 125, 122, 142, 143, 128], #[46, 26, 47, 48, 49, 50, 110, 141], #[26, 63, 57, 125, 122, 144, 143, 145], #[112, 30, 17, 48, 146, 147, 148, 149], #[105, 150, 57, 58, 151, 152, 153, 154], #[26, 26, 26, 26, 11, 155, 156, 11], #[105, 71, 26, 41, 157, 158, 44, 45], #[119, 26, 72, 48, 159, 50, 160, 52], #[70, 71, 72, 18, 73, 161, 162, 163], #[164, 165, 100, 58, 166, 167, 168, 104], #[169, 113, 170, 65, 171, 172, 173, 118], #[70, 71, 72, 18, 174, 74, 75, 76], #[80, 16, 81, 18, 175, 20, 83, 22], #[84, 30, 25, 26, 85, 33, 78, 7], #[26, 26, 26, 26, 79, 11, 11, 11]],
  #[#[23, 24, 25, 26, 77, 37, 176, 7], #[119, 26, 72, 48, 177, 50, 160, 52], #[23, 24, 25, 26, 27, 37, 176, 55], #[119, 63, 135, 65, 136, 67, 178, 69], #[84, 30, 25, 26, 179, 87, 78, 7], #[180, 90, 81, 18, 181, 92, 83, 22], #[89, 90, 17, 18, 182, 92, 21, 22], #[84, 30, 25, 26, 93, 87, 28, 7], #[26, 26, 26, 26, 88, 11, 11, 11], #[29, 30, 31, 26, 86, 183, 38, 7], #[105, 71, 26, 41, 184, 158, 44, 45], #[29, 30, 31, 26, 32, 183, 38, 55], #[105, 150, 57, 58, 151, 185, 61, 62], #[180, 90, 81, 18, 186, 92, 83, 22], #[34, 34, 26, 26, 10, 94, 11, 11], #[39, 40, 26, 41, 95, 96, 44, 97]],
  #[#[98, 99, 100, 58, 101, 187, 103, 104], #[105, 71, 26, 41, 106, 107, 44, 97], #[23, 24, 25, 26, 77, 37, 78, 7], #[39, 40, 26, 41, 42, 43, 44, 123], #[26, 26, 26, 26, 79, 11, 11, 124], #[188, 24, 81, 48, 60, 189, 190, 191], #[39, 40, 26, 41, 42, 43, 192, 123], #[84, 113, 100, 125, 193, 194, 195, 196], #[119, 63, 135, 65, 197, 137, 138, 139], #[26, 26, 26, 26, 11, 155, 11, 11], #[105, 71, 26, 41, 106, 198, 44, 97], #[164, 165, 100, 58, 166, 167, 103, 104], #[35, 26, 35, 26, 14, 11, 108, 11], #[46, 26, 47, 48, 109, 50, 110, 111], #[112, 113, 114, 65, 115, 116, 199, 118], #[119, 26, 72, 48, 120, 50, 121, 111]],
  #[#[29, 30, 31, 26, 86, 87, 38, 7], #[26, 26, 26, 26, 88, 11, 11, 140], #[46, 26, 47, 48, 49, 50, 51, 141], #[200, 90, 31, 41, 68, 201, 202, 203], #[84, 113, 100, 125, 204, 194, 195, 205], #[46, 26, 47, 48, 49, 192, 51, 141], #[105, 150, 57, 58, 206, 152, 153, 154], #[26, 26, 26, 26, 11, 11, 156, 11], #[119, 26, 72, 48, 120, 50, 207, 111], #[169, 113, 170, 65, 171, 116, 173, 118], #[26, 26, 26, 26, 11, 11, 11, 122], #[105, 71, 26, 41, 106, 107, 44, 123], #[26, 26, 26, 26, 11, 11, 11, 124], #[26, 63, 57, 125, 122, 142, 127, 128], #[26, 63, 57, 125, 122, 126, 133, 145], #[26, 63, 57, 125, 122, 144, 127, 134]],
  #[#[70, 150, 135, 208, 209, 210, 211, 212], #[188, 24, 81, 48, 60, 189, 190, 149], #[39, 56, 57, 58, 59, 60, 153, 62], #[84, 30, 25, 26, 85, 183, 176, 7], #[105, 71, 26, 41, 184, 107, 44, 123], #[26, 63, 57, 125, 122, 144, 133, 134], #[70, 150, 135, 208, 209, 210, 211, 213], #[119, 26, 72, 48, 159, 50, 160, 141], #[119, 26, 72, 48, 177, 50, 207, 141], #[26, 63, 57, 125, 122, 126, 143, 145], #[169, 30, 81, 48, 214, 147, 154, 149], #[105, 150, 57, 58, 151, 152, 153, 62], #[26, 26, 26, 26, 11, 11, 11, 140], #[119, 26, 72, 48, 120, 50, 121, 141], #[26, 63, 57, 125, 122, 142, 133, 145], #[26, 63, 57, 125, 122, 144, 143, 134]],
  #[#[26, 63, 57, 125, 122, 144, 133, 145], #[70, 150, 135, 208, 209, 210, 211, 215], #[200, 90, 31, 41, 68, 201, 202, 132], #[84, 30, 25, 26, 93, 183, 176, 7], #[46, 63, 64, 65, 66, 137, 68, 69], #[119, 26, 72, 48, 177, 50, 121, 141], #[105, 71, 26, 41, 157, 158, 44, 123], #[105, 71, 26, 41, 184, 198, 44, 123], #[164, 90, 25, 41, 216, 139, 131, 132], #[26, 63, 57, 125, 122, 126, 143, 134], #[119, 63, 135, 65, 136, 137, 138, 69], #[26, 26, 26, 26, 11, 155, 11, 11], #[26, 26, 26, 26, 11, 11, 156, 11], #[105, 71, 26, 41, 157, 198, 44, 97], #[164, 165, 100, 58, 166, 217, 103, 104], #[119, 26, 72, 48, 159, 50, 207, 111]],
  #[#[169, 113, 170, 65, 171, 116, 218, 118], #[164, 165, 100, 58, 166, 219, 168, 104], #[169, 113, 170, 65, 171, 172, 220, 118], #[70, 71, 72, 18, 174, 74, 75, 163], #[84, 30, 25, 26, 179, 183, 78, 7], #[105, 71, 26, 41, 184, 158, 44, 123], #[169, 30, 81, 48, 185, 147, 190, 191], #[105, 71, 26, 41, 184, 107, 192, 123], #[84, 113, 100, 125, 193, 194, 221, 196], #[84, 30, 25, 26, 179, 87, 176, 7], #[119, 26, 72, 48, 177, 50, 160, 141], #[164, 90, 25, 41, 178, 201, 131, 203], #[84, 113, 100, 125, 204, 222, 195, 205], #[119, 26, 72, 48, 177, 192, 121, 141], #[70, 71, 72, 18, 174, 161, 162, 163], #[23, 24, 25, 26, 77, 37, 176, 55]],
  #[#[84, 30, 25, 26, 85, 33, 176, 7], #[119, 26, 72, 48, 177, 50, 207, 111], #[169, 30, 81, 48, 214, 147, 190, 149], #[180, 90, 81, 18, 223, 92, 83, 22], #[84, 30, 25, 26, 179, 183, 176, 7], #[84, 30, 25, 26, 85, 183, 176, 55], #[29, 30, 31, 26, 86, 183, 38, 55], #[84, 30, 25, 26, 93, 183, 28, 7], #[105, 71, 26, 41, 184, 198, 44, 97], #[164, 90, 25, 41, 216, 201, 131, 132], #[84, 30, 25, 26, 93, 183, 176, 55], #[39, 40, 26, 41, 42, 96, 192, 123], #[23, 24, 25, 26, 77, 5, 176, 7], #[23, 24, 25, 26, 27, 37, 176, 7], #[119, 63, 135, 65, 136, 137, 178, 69], #[119, 26, 72, 48, 177, 50, 121, 111]],
  #[#[26, 26, 26, 26, 11, 44, 50, 11], #[180, 90, 81, 18, 181, 92, 83, 224], #[84, 113, 100, 125, 204, 194, 221, 205], #[84, 113, 100, 125, 193, 222, 195, 196], #[70, 150, 135, 208, 225, 210, 211, 213], #[119, 26, 72, 48, 120, 50, 207, 141], #[164, 165, 100, 58, 166, 219, 103, 104], #[46, 26, 47, 48, 49, 192, 110, 141], #[29, 30, 31, 26, 86, 183, 6, 7], #[105, 150, 57, 58, 151, 185, 153, 62], #[29, 30, 31, 26, 32, 183, 38, 7], #[105, 71, 26, 41, 184, 107, 44, 97], #[180, 90, 81, 18, 186, 92, 83, 224], #[70, 150, 135, 208, 225, 210, 211, 215], #[105, 71, 26, 41, 106, 198, 44, 123], #[169, 113, 170, 65, 171, 116, 220, 118]],
  #[#[26, 63, 57, 125, 122, 126, 143, 128], #[70, 71, 72, 18, 73, 161, 162, 76], #[164, 90, 25, 41, 216, 139, 226, 132], #[169, 30, 81, 48, 214, 227, 154, 149], #[26, 63, 57, 125, 55, 126, 143, 128], #[26, 63, 57, 125, 55, 126, 143, 134], #[164, 90, 25, 41, 178, 201, 131, 132], #[26, 63, 57, 125, 55, 126, 143, 145], #[169, 30, 81, 48, 185, 147, 190, 149], #[105, 71, 26, 41, 184, 158, 192, 123], #[119, 26, 72, 48, 177, 192, 160, 141], #[105, 71, 26, 41, 184, 198, 192, 123], #[119, 26, 72, 48, 177, 192, 207, 141], #[84, 113, 100, 125, 193, 222, 221, 196], #[84, 113, 100, 125, 204, 222, 221, 205], #[84, 30, 25, 26, 179, 183, 176, 55]],
  #[#[70, 71, 72, 18, 73, 74, 75, 163], #[70, 71, 72, 18, 174, 161, 162, 76], #[84, 30, 25, 26, 85, 183, 28, 7], #[84, 30, 25, 26, 93, 33, 176, 7]]]

abbrev Index := Fin 228

def window (i : Index) : Local := ((windows[i.val / 16]?.getD #[])[i.val % 16]?).getD default

def link (i : Index) (t x y : Bool) : Index :=
  ⟨((((links[i.val / 16]?.getD #[])[i.val % 16]?.getD #[])[code t x y]?).getD 0) % 228,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma certificate : ∀ i : Index, valid (window i) ∧
    ∀ t x y : Bool, window (link i t x y) = descend (window i) t x y := by
  decide +kernel

lemma at_origin : position 0 0 0 0 = window 0 := by decide

lemma decomposes (n : ℕ) : digit (n / 2) (n % 2 == 1) = n := by
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;> simp [digit, h] <;> omega

lemma covered (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    ∃ i, position w t x y = window i := by
  induction w generalizing t x y with
  | zero =>
    simp only [pow_zero] at ht hx hy
    obtain rfl : t = 0 := by omega
    obtain rfl : x = 0 := by omega
    obtain rfl : y = 0 := by omega
    exact ⟨0, at_origin⟩
  | succ w ih =>
    simp only [pow_succ] at ht hx hy
    obtain ⟨i, hi⟩ := ih (t / 2) (x / 2) (y / 2) (by omega) (by omega) (by omega)
    refine ⟨link i (t % 2 == 1) (x % 2 == 1) (y % 2 == 1), ?_⟩
    have h := position_digit w (t / 2) (x / 2) (y / 2) (t % 2 == 1) (x % 2 == 1) (y % 2 == 1)
    rw [decomposes, decomposes, decomposes, hi, ← (certificate i).2] at h
    exact h

lemma address_stable (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    address (w + 1) t x y = address w t x y := by
  induction w generalizing t x y with
  | zero =>
    simp only [pow_zero] at ht hx hy
    have : t = 0 := by omega
    have : x = 0 := by omega
    have : y = 0 := by omega
    subst_vars
    decide
  | succ w ih =>
    simp only [pow_succ] at ht hx hy
    change go (address (w + 1) (t / 2) (x / 2) (y / 2)) _ _ _ = go (address w _ _ _) _ _ _
    rw [ih (t / 2) (x / 2) (y / 2) (by omega) (by omega) (by omega)]

lemma address_wider (w u t x y : ℕ) (hu : w ≤ u) (ht : t < 2 ^ w) (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) : address u t x y = address w t x y := by
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    have hpow : 2 ^ w ≤ (2 : ℕ) ^ u := Nat.pow_le_pow_right (by decide) hu
    rw [address_stable u t x y (by omega) (by omega) (by omega), ih]

def value (t x y : ℕ) := lit (address (t + x + y + 1) t x y)

lemma at_width (w t x y : ℕ) (ht : t < 2 ^ w) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    value t x y = lit (address w t x y) := by
  unfold value
  by_cases h : w ≤ t + x + y + 1
  · rw [address_wider w _ _ _ _ h ht hx hy]
  · have hb := Nat.lt_two_pow_self (n := t + x + y + 1)
    rw [address_wider (t + x + y + 1) w _ _ _ (by omega) (by omega) (by omega) (by omega)]

lemma natural_law (r t x y : ℕ) (hr : r = 401 ∨ r = 409) :
    (t = 0 → value t x y = decide (x = 0 ∧ y = 0)) ∧
    value (t + 1) x y = localRule r (value t x y) (value t (prev x) y) (value t (x + 1) y)
      (value t x (prev y)) (value t x (y + 1)) := by
  let w := t + x + y + 2
  have hw : t + x + y + 2 < 2 ^ w := Nat.lt_two_pow_self
  obtain ⟨i, hi⟩ := covered w t x y (by omega) (by omega) (by omega)
  have h := (certificate i).1
  rw [← hi] at h
  simp only [valid, position] at h
  have hpow : t + x + y + 2 < 2 ^ (w + 1) := by rw [pow_succ]; omega
  have hpx : prev x ≤ x + 1 := by unfold prev; split <;> omega
  have hpy : prev y ≤ y + 1 := by unfold prev; split <;> omega
  rw [at_width (w + 1) t x y (by omega) (by omega) (by omega),
    at_width (w + 1) (t + 1) x y (by omega) (by omega) (by omega),
    at_width (w + 1) t (prev x) y (by omega) (by omega) (by omega),
    at_width (w + 1) t (x + 1) y (by omega) (by omega) (by omega),
    at_width (w + 1) t x (prev y) (by omega) (by omega) (by omega),
    at_width (w + 1) t x (y + 1) (by omega) (by omega) (by omega)]
  constructor
  · intro ht
    have h0 := h.1 (by simp [ht])
    cases x <;> cases y <;> simpa using h0
  · rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2

def plane (t : ℕ) (x y : ℤ) := value t x.natAbs y.natAbs

lemma plane_zero (x y : ℤ) : plane 0 x y = decide (x = 0 ∧ y = 0) := by
  simpa [plane] using (natural_law 401 0 x.natAbs y.natAbs (Or.inl rfl : 401 = 401 ∨ 401 = 409)).1 rfl

lemma neighbors (x : ℤ) :
    ((x - 1).natAbs = prev x.natAbs ∧ (x + 1).natAbs = x.natAbs + 1) ∨
    ((x + 1).natAbs = prev x.natAbs ∧ (x - 1).natAbs = x.natAbs + 1) := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · right
    have a := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    have b := Int.ofNat_natAbs_of_nonpos (show x + 1 ≤ 0 by omega)
    have c := Int.ofNat_natAbs_of_nonpos (show x - 1 ≤ 0 by omega)
    unfold prev; split <;> omega
  · decide
  · left
    have a := Int.natAbs_of_nonneg (show 0 ≤ x by omega)
    have b := Int.natAbs_of_nonneg (show 0 ≤ x + 1 by omega)
    have c := Int.natAbs_of_nonneg (show 0 ≤ x - 1 by omega)
    unfold prev; split <;> omega

lemma plane_step (r t : ℕ) (x y : ℤ) (hr : r = 401 ∨ r = 409) :
    plane (t + 1) x y = localRule r (plane t x y) (plane t (x - 1) y) (plane t (x + 1) y)
      (plane t x (y - 1)) (plane t x (y + 1)) := by
  unfold plane
  rw [(natural_law r t x.natAbs y.natAbs hr).2]
  unfold localRule
  rcases neighbors x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases neighbors y with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h1, h2, h3, h4] <;> ac_rfl

def gridRows (t : ℕ) (f : ℤ → ℤ → Bool) : List (List Bool) :=
  (List.range (2 * t + 1)).map fun (j : ℕ) =>
    (List.range (2 * t + 1)).map fun (i : ℕ) => f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t)

def background (r : ℕ) : ℕ → Bool
  | 0 => false
  | t + 1 => applyRule r (background r t) (background r t) (background r t)
      (background r t) (background r t)

lemma applyRule_eq_localRule (r : ℕ) (c n s w e : Bool) :
    applyRule r c n s w e = localRule r c w e n s := by
  unfold applyRule localRule; congr 1; omega

lemma outside (r t : ℕ) (hr : r = 401 ∨ r = 409) (x y : ℤ)
    (h : x < -(t : ℤ) ∨ (t : ℤ) < x ∨ y < -(t : ℤ) ∨ (t : ℤ) < y) :
    plane t x y = background r t := by
  induction t generalizing x y with
  | zero => rw [plane_zero]; simp [background]; omega
  | succ t ih =>
    simp only [Nat.cast_succ] at h
    rw [plane_step r t x y hr, ih x y (by omega), ih (x - 1) y (by omega),
      ih (x + 1) y (by omega), ih x (y - 1) (by omega), ih x (y + 1) (by omega)]
    rw [background]
    exact (applyRule_eq_localRule r _ _ _ _ _).symm

lemma getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, hi]

lemma getCell_gridRows (t : ℕ) (bg : Bool) (f : ℤ → ℤ → Bool)
    (hout : ∀ u v : ℤ, u < -(t : ℤ) ∨ (t : ℤ) < u ∨ v < -(t : ℤ) ∨ (t : ℤ) < v → f u v = bg)
    (x y : ℤ) :
    getCell t (bg, gridRows t f) x y = f x y := by
  unfold getCell
  split_ifs with h
  · rcases h with ⟨hx1, hx2, hy1, hy2⟩
    have hiy : (y + ↑t).toNat < 2 * t + 1 := by omega
    have hix : (x + ↑t).toNat < 2 * t + 1 := by omega
    have hiy_eq : (((y + ↑t).toNat : ℤ) - ↑t) = y := by omega
    have hix_eq : (((x + ↑t).toNat : ℤ) - ↑t) = x := by omega
    unfold gridRows
    rw [getD_map_range _ _ _ _ hiy, getD_map_range _ _ _ _ hix, hix_eq, hiy_eq]
  · symm; apply hout; omega

lemma flatMap_pure_map {α β γ : Type} (xs : List α) (c : α → β) (f : β → γ) :
    List.map f (List.flatMap (fun a => [c a]) xs) = List.map (fun a => f (c a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma stages (r t : ℕ) (hr : r = 401 ∨ r = 409) :
    stageCfg r t = (background r t, gridRows t (plane t)) := by
  induction t with
  | zero =>
    simp [stageCfg, background, gridRows, plane_zero]
  | succ t ih =>
    rw [stageCfg, ih]
    have hg : getCell t (background r t, gridRows t (plane t)) = plane t := by
      funext x y; exact getCell_gridRows t (background r t) (plane t) (outside r t hr) x y
    dsimp only [stepCfg]
    rw [hg]
    refine Prod.ext rfl ?_
    simp only [List.bind_eq_flatMap, List.pure_def, flatMap_pure_map, gridRows]
    apply List.map_congr_left; intro iy _
    apply List.map_congr_left; intro ix _
    rw [plane_step r t _ _ hr]
    exact applyRule_eq_localRule r _ _ _ _ _

lemma count_map_range (n : ℕ) (g : ℕ → Bool) :
    (((List.range n).map g).count true : ℤ) = ∑ i ∈ Finset.range n, ((g i).toNat : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil]
    push_cast
    rw [ih]
    cases g n <;> simp

lemma sum_map_range (n : ℕ) (g : ℕ → ℕ) :
    (Nat.cast (((List.range n).map g).sum) : ℤ) = ∑ i ∈ Finset.range n, (g i : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, Nat.cast_add, ih]
    simp

lemma sum_gridRows (t : ℕ) (f : ℤ → ℤ → Bool) :
    (Nat.cast (((gridRows t f).map fun row => row.count true).sum) : ℤ) =
      ∑ j ∈ Finset.range (2 * t + 1), ∑ i ∈ Finset.range (2 * t + 1),
        ((f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t)).toNat : ℤ) := by
  unfold gridRows
  simp only [List.map_map, Function.comp_def]
  rw [sum_map_range]
  apply Finset.sum_congr rfl
  intro j _
  exact count_map_range (2 * t + 1) (fun i => f ((i : ℤ) - ↑t) ((j : ℤ) - ↑t))

lemma reflect_sum (t : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * t + 1), f (((i : ℤ) - ↑t).natAbs) =
      2 * (∑ i ∈ Finset.range (t + 1), f i) - f 0 := by
  rw [show 2 * t + 1 = (t + 1) + t by omega, Finset.sum_range_add]
  have h₁ : ∑ i ∈ Finset.range (t + 1), f (((i : ℤ) - ↑t).natAbs) =
      ∑ i ∈ Finset.range (t + 1), f i := by
    rw [← Finset.sum_range_reflect f (t + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    have := Int.ofNat_natAbs_of_nonpos (show (i : ℤ) - ↑t ≤ 0 by omega)
    omega
  rw [h₁]
  have h₂ : ∑ i ∈ Finset.range t, f ((((t + 1 + i : ℕ) : ℤ) - ↑t).natAbs) =
      ∑ i ∈ Finset.range t, f (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    rw [show (t : ℤ) + 1 + i - ↑t = ↑(i + 1 : ℕ) by omega]
    rfl
  rw [h₂]
  have := Finset.sum_range_succ' f t
  omega

def span (b : Bool) (n : ℕ) := if b then 2 ^ n else 1

def pick (b : Bool) (f : Bool → ℤ) := if b then f false + f true else f false

def mix (u v : Bool) (f : ℕ → ℤ) (q : ℕ) :=
  pick v fun y => pick u fun x => f (go q true x y)

def total (n : ℕ) (u v : Bool) (f : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (span v n), ∑ i ∈ Finset.range (span u n),
    f (address n (2 ^ n - 1) i j)

def weight (q : ℕ) : ℤ := (lit q).toNat

def count (n : ℕ) (u v : Bool) := total n u v weight

lemma paired (k : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * k), f i =
      ∑ i ∈ Finset.range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

lemma span_split (b : Bool) (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (span b (n + 1)), f i =
      ∑ i ∈ Finset.range (span b n), pick b (fun bit => f (digit i bit)) := by
  cases b
  · simp [span, pick, digit]
  · simp only [span, ↓reduceIte, pick, digit, Bool.toNat_false,
      Bool.toNat_true, Nat.add_zero, pow_succ]
    rw [Nat.mul_comm, paired]

lemma total_step (n : ℕ) (u v : Bool) (f : ℕ → ℤ) :
    total (n + 1) u v f = total n u v (mix u v f) := by
  have ht : 2 ^ (n + 1) - 1 = digit (2 ^ n - 1) true := by
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    simp [digit, pow_succ]; omega
  unfold total
  rw [span_split v n]
  apply Finset.sum_congr rfl
  intro j _
  cases v <;> simp only [mix, pick, Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib,
    span_split u n, ht, address_digit]
  all_goals first | rfl | rw [Finset.sum_add_distrib]

lemma small_go : ∀ q : Fin 20, ∀ t x y : Bool, go q.val t x y < 20 := by decide +kernel

lemma small_address (w t x y : ℕ) : address w t x y < 20 := by
  induction w generalizing t x y with
  | zero => change 0 < 20; decide
  | succ w ih => exact small_go ⟨_, ih (t / 2) (x / 2) (y / 2)⟩ _ _ _

def iterate (k : ℕ) (u v : Bool) : ℕ → ℤ :=
  match k with
  | 0 => weight
  | k + 1 => mix u v (iterate k u v)

def iterVec (k : ℕ) (u v : Bool) : List ℤ :=
  match k with
  | 0 => (List.range 20).map weight
  | k + 1 =>
    let prev := iterVec k u v
    (List.range 20).map (fun q => mix u v (fun s => prev.getD s 0) q)

lemma iterVec_eq (k : ℕ) (u v : Bool) :
    ∀ q < 20, (iterVec k u v).getD q 0 = iterate k u v q := by
  induction k with
  | zero =>
    intro q hq
    exact getD_map_range 20 weight q 0 hq
  | succ k ih =>
    intro q hq
    unfold iterVec iterate
    dsimp only
    rw [getD_map_range 20 _ q 0 hq]
    unfold mix
    congr 1; funext y; congr 1; funext x
    exact ih (go q true x y) (small_go ⟨q, hq⟩ true x y)

lemma shift_total (n k : ℕ) (u v : Bool) :
    count (n + k) u v = total n u v (iterate k u v) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [show n + (k + 1) = (n + 1) + k by omega, ih, total_step]
    rfl

set_option maxHeartbeats 4000000 in
lemma iter_vec_rec : ∀ u v : Bool,
    let v1 := iterVec 1 u v
    let v2 := iterVec 2 u v
    let v3 := iterVec 3 u v
    let v4 := iterVec 4 u v
    let v5 := iterVec 5 u v
    let v6 := iterVec 6 u v
    let v7 := iterVec 7 u v
    ∀ q : Fin 20, v7.getD q.val 0 = 9 * v6.getD q.val 0 - 23 * v5.getD q.val 0 + 3 * v4.getD q.val 0 + 40 * v3.getD q.val 0 - 12 * v2.getD q.val 0 - 16 * v1.getD q.val 0 := by
  decide +kernel

lemma iter_rec (u v : Bool) (q : Fin 20) :
    iterate 7 u v q.val = 9 * iterate 6 u v q.val - 23 * iterate 5 u v q.val + 3 * iterate 4 u v q.val + 40 * iterate 3 u v q.val - 12 * iterate 2 u v q.val - 16 * iterate 1 u v q.val := by
  simpa only [iterVec_eq _ u v q.val q.isLt] using iter_vec_rec u v q

lemma count_rec (n : ℕ) (u v : Bool) :
    count (n + 7) u v = 9 * count (n + 6) u v - 23 * count (n + 5) u v + 3 * count (n + 4) u v + 40 * count (n + 3) u v - 12 * count (n + 2) u v - 16 * count (n + 1) u v := by
  simp only [shift_total, total, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact iter_rec u v ⟨_, small_address n _ x y⟩

lemma reflect_square (t : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ j ∈ Finset.range (2 * t + 1), ∑ i ∈ Finset.range (2 * t + 1),
      f (((i : ℤ) - ↑t).natAbs) (((j : ℤ) - ↑t).natAbs) =
    4 * (∑ j ∈ Finset.range (t + 1), ∑ i ∈ Finset.range (t + 1), f i j) -
      2 * (∑ j ∈ Finset.range (t + 1), f 0 j) - 2 * (∑ i ∈ Finset.range (t + 1), f i 0) + f 0 0 := by
  rw [reflect_sum t (fun y => ∑ i ∈ Finset.range (2 * t + 1), f (((i : ℤ) - ↑t).natAbs) y)]
  have inner (y : ℕ) := reflect_sum t (fun i => f i y)
  simp only [inner]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma count_eq (n : ℕ) (u v : Bool) :
    count n u v = ∑ j ∈ Finset.range (span v n), ∑ i ∈ Finset.range (span u n),
      ((value (2 ^ n - 1) i j).toNat : ℤ) := by
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  unfold count total weight
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro i hi
  simp only [Finset.mem_range] at hi hj
  have hb (b : Bool) : span b n ≤ 2 ^ n := by cases b <;> simp [span, Nat.one_le_two_pow]
  rw [at_width n _ _ _ (by omega) (lt_of_lt_of_le hi (hb u)) (lt_of_lt_of_le hj (hb v))]

lemma count_eq_iterVec (k : ℕ) (u v : Bool) :
    count k u v = (iterVec k u v).getD 0 0 := by
  have h := shift_total 0 k u v
  rw [Nat.zero_add] at h
  rw [h]
  have su : span u 0 = 1 := by cases u <;> rfl
  have sv : span v 0 = 1 := by cases v <;> rfl
  unfold total
  rw [su, sv]
  simp only [Finset.sum_range_one, address]
  exact (iterVec_eq k u v 0 (by decide)).symm

lemma sampled_eq (n r : ℕ) (hr : r = 401 ∨ r = 409) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * count n true true - 2 * count n false true - 2 * count n true false + count n false false := by
  have h : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  unfold countOn
  rw [stages r _ hr]
  dsimp only
  rw [sum_gridRows]
  unfold plane
  rw [reflect_square (2 ^ n - 1) (fun i j => ((value (2 ^ n - 1) i j).toNat : ℤ))]
  simp only [count_eq, span, ↓reduceIte, Bool.false_eq_true, Finset.sum_range_one,
    show (2 : ℕ) ^ n - 1 + 1 = 2 ^ n by omega]

lemma sampled_fast (n r : ℕ) (hr : r = 401 ∨ r = 409) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * (iterVec n true true).getD 0 0 - 2 * (iterVec n false true).getD 0 0 -
      2 * (iterVec n true false).getD 0 0 + (iterVec n false false).getD 0 0 := by
  rw [sampled_eq n r hr]
  simp only [count_eq_iterVec]

end Scale401


section Proof_a271804

lemma a_rec6 (n : ℕ) :
    (a (n + 7) : ℤ) = 9 * a (n + 6) - 23 * a (n + 5) + 3 * a (n + 4) +
      40 * a (n + 3) - 12 * a (n + 2) - 16 * a (n + 1) := by
  simp only [a, Scale401.sampled_eq _ 401 (Or.inl rfl), Scale401.count_rec n]
  ring

lemma a_init :
    (a 0 : ℤ) = 1 ∧ (a 1 : ℤ) = 4 ∧ (a 2 : ℤ) = 32 ∧ (a 3 : ℤ) = 164 ∧
    (a 4 : ℤ) = 744 ∧ (a 5 : ℤ) = 3196 ∧ (a 6 : ℤ) = 13376 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a, Scale401.sampled_fast 0 401 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale401.sampled_fast 1 401 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale401.sampled_fast 2 401 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale401.sampled_fast 3 401 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale401.sampled_fast 4 401 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale401.sampled_fast 5 401 (Or.inl rfl)]; decide +kernel
  · rw [a, Scale401.sampled_fast 6 401 (Or.inl rfl)]; decide +kernel

noncomputable def radClosed (n : ℕ) : ℝ :=
  1 - 2 ^ (2 + n) + 4 ^ (1 + n) +
    ((2 : ℝ) ^ (-1 - (n : ℤ)) *
      (-(3 - Real.sqrt 17) ^ n * (-7 + Real.sqrt 17) -
        (3 + Real.sqrt 17) ^ n * (7 + Real.sqrt 17))) / Real.sqrt 17

lemma two_zpow_neg (n : ℕ) : (2 : ℝ) ^ (-1 - (n : ℤ)) = 1 / (2 * 2 ^ n) := by
  have heq : (-1 - (n : ℤ)) = -(((1 + n : ℕ) : ℤ)) := by omega
  rw [heq, zpow_neg, zpow_natCast, pow_add, pow_one, one_div]

lemma radClosed_alt (n : ℕ) :
    radClosed n = 1 - 2 ^ (2 + n) + 4 ^ (1 + n) +
      (((1 / 2 : ℝ) * (((3 - Real.sqrt 17) / 2) ^ n * -(-7 + Real.sqrt 17) -
        ((3 + Real.sqrt 17) / 2) ^ n * (7 + Real.sqrt 17))) / Real.sqrt 17) := by
  unfold radClosed
  rw [two_zpow_neg, div_pow, div_pow]
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  congr 1
  congr 1
  field_simp [h2]

lemma root_char (r : ℝ) (hr : r ^ 2 = 3 * r + 2) :
    r ^ 5 - 10 * r ^ 4 + 33 * r ^ 3 - 36 * r ^ 2 - 4 * r + 16 = 0 := by
  linear_combination (r ^ 3 - 7 * r ^ 2 + 14 * r - 8) * hr

set_option maxHeartbeats 4000000 in
lemma alg_a271804 (F : ℕ → ℤ)
    (hinit : F 0 = 1 ∧ F 1 = 4 ∧ F 2 = 32 ∧ F 3 = 164 ∧ F 4 = 744 ∧ F 5 = 3196 ∧ F 6 = 13376)
    (hrec6 : ∀ n, F (n + 7) = 9 * F (n + 6) - 23 * F (n + 5) + 3 * F (n + 4) +
      40 * F (n + 3) - 12 * F (n + 2) - 16 * F (n + 1)) :
    (∀ n, 0 < n → (F n : ℝ) = radClosed n) ∧
    (PowerSeries.mk F *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X) * (1 - 3 * X - 2 * X ^ 2)) =
      1 - 6 * X + 25 * X ^ 2 - 60 * X ^ 3 + 12 * X ^ 4 + 16 * X ^ 5) := by
  have f_rec5 : ∀ n, F (n + 6) = 10 * F (n + 5) - 33 * F (n + 4) + 36 * F (n + 3) +
      4 * F (n + 2) - 16 * F (n + 1) := by
    intro n
    induction n with
    | zero =>
      rcases hinit with ⟨_, v1, v2, v3, v4, v5, v6⟩
      norm_num [v1, v2, v3, v4, v5, v6]
    | succ n ih =>
      have h6 := hrec6 n
      have e7 : n + 1 + 6 = n + 7 := by omega
      have e6 : n + 1 + 5 = n + 6 := by omega
      have e5 : n + 1 + 4 = n + 5 := by omega
      have e4 : n + 1 + 3 = n + 4 := by omega
      have e3 : n + 1 + 2 = n + 3 := by omega
      have e2 : n + 1 + 1 = n + 2 := by omega
      rw [e7, e6, e5, e4, e3, e2]
      linarith [ih, h6]
  have recurrence5 : ∀ n, 5 < n →
      F n = 10 * F (n - 1) - 33 * F (n - 2) + 36 * F (n - 3) + 4 * F (n - 4) - 16 * F (n - 5) := by
    intro n hn
    simpa only [show n - 6 + 6 = n by omega, show n - 6 + 5 = n - 1 by omega,
      show n - 6 + 4 = n - 2 by omega, show n - 6 + 3 = n - 3 by omega,
      show n - 6 + 2 = n - 4 by omega, show n - 6 + 1 = n - 5 by omega] using f_rec5 (n - 6)
  refine ⟨?_, ?_⟩
  · intro n hn
    have hq2 : Real.sqrt 17 ^ 2 = (17 : ℝ) := Real.sq_sqrt (by norm_num)
    have hq0 : Real.sqrt 17 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    let u : ℝ := (3 - Real.sqrt 17) / 2
    let v : ℝ := (3 + Real.sqrt 17) / 2
    have hrad_uv : ∀ m : ℕ, radClosed m = 1 - 2 ^ (2 + m) + 4 ^ (1 + m) +
        ((1 / 2 : ℝ) * (u ^ m * -(-7 + Real.sqrt 17) - v ^ m * (7 + Real.sqrt 17))) *
          (Real.sqrt 17)⁻¹ := by
      intro m; rw [radClosed_alt, div_eq_mul_inv]
    have hr1 : u ^ 2 = 3 * u + 2 := by
      dsimp only [u]; linear_combination (1 / 4 : ℝ) * hq2
    have hr2 : v ^ 2 = 3 * v + 2 := by
      dsimp only [v]; linear_combination (1 / 4 : ℝ) * hq2
    have hc1 := root_char u hr1
    have hc2 := root_char v hr2
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 6
      · rcases hinit with ⟨_, v1, v2, v3, v4, v5, _⟩
        have c1 : (F 1 : ℝ) = 4 := by exact_mod_cast v1
        have c2 : (F 2 : ℝ) = 32 := by exact_mod_cast v2
        have c3 : (F 3 : ℝ) = 164 := by exact_mod_cast v3
        have c4 : (F 4 : ℝ) = 744 := by exact_mod_cast v4
        have c5 : (F 5 : ℝ) = 3196 := by exact_mod_cast v5
        interval_cases n
        · rw [c1, radClosed_alt]; field_simp [hq0]; ring
        · have p3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hq2]
          rw [c2, radClosed_alt]; field_simp [hq0]; ring_nf
          simp only [p3]; ring
        · have p3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hq2]
          rw [c3, radClosed_alt]; field_simp [hq0]; ring_nf
          simp only [p3]; ring
        · have p3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hq2]
          have p4 : Real.sqrt 17 ^ 4 = 289 := by linear_combination (Real.sqrt 17 ^ 2 + 17) * hq2
          have p5 : Real.sqrt 17 ^ 5 = 289 * Real.sqrt 17 := by rw [pow_succ, p4]
          rw [c4, radClosed_alt]; field_simp [hq0]; ring_nf
          simp only [p5, p3]; ring
        · have p3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hq2]
          have p4 : Real.sqrt 17 ^ 4 = 289 := by linear_combination (Real.sqrt 17 ^ 2 + 17) * hq2
          have p5 : Real.sqrt 17 ^ 5 = 289 * Real.sqrt 17 := by rw [pow_succ, p4]
          rw [c5, radClosed_alt]; field_simp [hq0]; ring_nf
          simp only [p5, p3]; ring
      · let k := n - 6
        have hk : n = k + 6 := by dsimp [k]; omega
        have step_r : (F (k + 6) : ℝ) = 10 * F (k + 5) - 33 * F (k + 4) + 36 * F (k + 3) +
            4 * F (k + 2) - 16 * F (k + 1) := by
          exact_mod_cast f_rec5 k
        rw [hk, step_r,
          ih (k + 5) (by omega) (by omega),
          ih (k + 4) (by omega) (by omega),
          ih (k + 3) (by omega) (by omega),
          ih (k + 2) (by omega) (by omega),
          ih (k + 1) (by omega) (by omega)]
        simp only [hrad_uv,
          show 2 + (k + 6) = k + 8 by omega, show 2 + (k + 5) = k + 7 by omega,
          show 2 + (k + 4) = k + 6 by omega, show 2 + (k + 3) = k + 5 by omega,
          show 2 + (k + 2) = k + 4 by omega, show 2 + (k + 1) = k + 3 by omega,
          show 1 + (k + 6) = k + 7 by omega, show 1 + (k + 5) = k + 6 by omega,
          show 1 + (k + 4) = k + 5 by omega, show 1 + (k + 3) = k + 4 by omega,
          show 1 + (k + 2) = k + 3 by omega, show 1 + (k + 1) = k + 2 by omega, pow_add]
        linear_combination
          -((1 / 2 : ℝ) * -(-7 + Real.sqrt 17) * (Real.sqrt 17)⁻¹ * u ^ k * u) * hc1 +
          ((1 / 2 : ℝ) * (7 + Real.sqrt 17) * (Real.sqrt 17)⁻¹ * v ^ k * v) * hc2
  · have hd : mk F * ((1 - X) * (1 - 2 * X) * (1 - 4 * X) * (1 - 3 * X - 2 * X ^ 2)) =
        mk F * X ^ 0 + (-10 : ℤ) • (mk F * X ^ 1) + (33 : ℤ) • (mk F * X ^ 2) +
        (-36 : ℤ) • (mk F * X ^ 3) + (-4 : ℤ) • (mk F * X ^ 4) + (16 : ℤ) • (mk F * X ^ 5) := by
      simp only [zsmul_eq_mul]; push_cast; ring
    have hp : (1 - 6 * X + 25 * X ^ 2 - 60 * X ^ 3 + 12 * X ^ 4 + 16 * X ^ 5 : PowerSeries ℤ) =
        X ^ 0 + (-6 : ℤ) • X ^ 1 + (25 : ℤ) • X ^ 2 + (-60 : ℤ) • X ^ 3 +
        (12 : ℤ) • X ^ 4 + (16 : ℤ) • X ^ 5 := by
      simp only [zsmul_eq_mul]; push_cast; ring
    rw [hd, hp]
    ext n
    simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    by_cases hn : n < 6
    · rcases hinit with ⟨v0, v1, v2, v3, v4, v5, _⟩
      interval_cases n <;> norm_num [zsmul_eq_mul, v0, v1, v2, v3, v4, v5]
    · have hr := recurrence5 n (by omega)
      simp only [if_pos (show 0 ≤ n by omega), Nat.sub_zero, zsmul_eq_mul,
        if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
        if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
        if_pos (show 5 ≤ n by omega),
        if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
        if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega)]
      norm_num
      linarith only [hr]

end Proof_a271804

theorem OMA.solution : type_of% @OMA.S_oeis_a271804.main := by
  have halg := alg_a271804 (fun n => (a n : ℤ)) a_init a_rec6
  refine ⟨?_, fun n hn => ?_, halg.2⟩
  · intro n
    apply Int.ofNat.inj
    exact (Scale401.sampled_eq n 409 (Or.inr rfl)).trans
      (Scale401.sampled_eq n 401 (Or.inl rfl)).symm
  · simpa only [Int.cast_natCast, radClosed] using halg.1 n hn
