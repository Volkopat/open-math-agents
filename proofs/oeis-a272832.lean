import OMAStatements.S_oeis_a272832

open OMA.S_oeis_a272832 PowerSeries

namespace Scale694

def transitions : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 1, 1, 2, 3, 4, 1], #[1, 1, 1, 1, 1, 1, 1, 1], #[5, 6, 7, 8, 5, 9, 10, 11], #[3, 1, 1, 1, 12, 3, 13, 1], #[4, 1, 1, 1, 14, 13, 4, 1], #[5, 15, 16, 17, 5, 15, 16, 17], #[18, 6, 19, 8, 18, 9, 20, 21], #[22, 19, 7, 8, 22, 20, 10, 23], #[8, 1, 1, 1, 24, 8, 8, 1], #[18, 25, 20, 26, 18, 25, 20, 27], #[22, 20, 28, 29, 22, 20, 28, 30], #[31, 21, 23, 8, 31, 32, 33, 11], #[18, 6, 34, 8, 35, 9, 36, 11], #[13, 1, 1, 1, 37, 13, 13, 1], #[22, 38, 7, 8, 39, 40, 10, 11], #[18, 25, 20, 41, 18, 25, 20, 41]],
  #[#[22, 20, 28, 42, 22, 20, 28, 42], #[31, 43, 44, 17, 31, 43, 44, 17], #[45, 15, 46, 17, 35, 15, 46, 17], #[47, 19, 19, 8, 47, 20, 20, 24], #[47, 20, 20, 31, 47, 20, 20, 31], #[31, 21, 24, 8, 31, 32, 31, 21], #[48, 49, 16, 17, 39, 49, 16, 17], #[31, 24, 23, 8, 31, 31, 33, 23], #[31, 24, 24, 8, 31, 31, 31, 24], #[18, 25, 20, 41, 18, 25, 20, 41], #[31, 43, 31, 26, 31, 43, 31, 27], #[31, 43, 31, 50, 31, 43, 31, 41], #[22, 20, 28, 42, 22, 20, 28, 42], #[31, 31, 44, 29, 31, 31, 44, 30], #[31, 31, 44, 51, 31, 31, 44, 42], #[31, 31, 31, 31, 31, 31, 31, 31]],
  #[#[31, 43, 31, 26, 31, 52, 31, 27], #[31, 31, 44, 29, 31, 31, 53, 30], #[47, 19, 34, 8, 54, 20, 36, 23], #[45, 15, 55, 17, 45, 15, 55, 17], #[47, 20, 55, 29, 47, 20, 55, 30], #[47, 38, 34, 8, 54, 40, 36, 11], #[47, 38, 19, 8, 54, 40, 20, 21], #[48, 56, 16, 17, 48, 56, 16, 17], #[47, 56, 20, 26, 47, 56, 20, 27], #[31, 43, 31, 41, 31, 43, 31, 41], #[31, 31, 44, 42, 31, 31, 44, 42], #[31, 52, 31, 41, 31, 52, 31, 41], #[31, 31, 53, 42, 31, 31, 53, 42], #[45, 15, 55, 17, 45, 15, 55, 17], #[47, 20, 55, 42, 47, 20, 55, 42], #[47, 49, 46, 17, 47, 49, 46, 17]],
  #[#[48, 56, 16, 17, 48, 56, 16, 17], #[47, 56, 20, 41, 47, 56, 20, 41], #[31, 43, 31, 41, 31, 43, 31, 41], #[31, 31, 44, 42, 31, 31, 44, 42], #[31, 52, 31, 41, 31, 52, 31, 41], #[31, 31, 53, 42, 31, 31, 53, 42], #[47, 49, 46, 17, 47, 49, 46, 17], #[47, 20, 55, 42, 47, 20, 55, 42], #[47, 56, 20, 41, 47, 56, 20, 41]]]

def outputs : Array Bool := #[true, false, true, true, true, true, false, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false, true, true, false, true, true]

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
  lit s.next = localRule 694 (lit s.c) (lit s.left) (lit s.right) (lit s.down) (lit s.up)

instance (s : Local) : Decidable (valid s) := by unfold valid; infer_instance

def windows : Array (Array Local) := #[
  #[⟨0, 2, 1, 1, 1, 1, true, true, true⟩, ⟨1, 3, 1, 1, 0, 1, true, false, true⟩, ⟨1, 4, 0, 1, 1, 1, false, true, true⟩, ⟨1, 1, 1, 1, 1, 1, false, false, true⟩, ⟨2, 5, 4, 4, 3, 3, true, true, false⟩, ⟨3, 6, 1, 1, 2, 1, true, false, false⟩, ⟨4, 7, 2, 1, 1, 1, false, true, false⟩, ⟨1, 8, 3, 1, 4, 1, false, false, false⟩, ⟨1, 1, 1, 1, 1, 1, true, false, true⟩, ⟨1, 3, 1, 1, 3, 1, true, false, false⟩, ⟨1, 1, 1, 1, 1, 1, true, false, false⟩, ⟨1, 1, 1, 1, 1, 1, false, false, false⟩, ⟨1, 1, 1, 1, 1, 1, false, true, true⟩, ⟨1, 4, 4, 1, 1, 1, false, true, false⟩, ⟨1, 1, 1, 1, 1, 1, false, true, false⟩, ⟨5, 5, 7, 7, 6, 6, true, true, false⟩],
  #[⟨6, 9, 8, 8, 5, 3, true, false, false⟩, ⟨7, 10, 5, 4, 8, 8, false, true, false⟩, ⟨8, 11, 6, 1, 7, 1, false, false, false⟩, ⟨5, 5, 10, 10, 9, 9, true, true, false⟩, ⟨9, 15, 11, 11, 5, 12, true, false, false⟩, ⟨10, 16, 5, 14, 11, 11, false, true, false⟩, ⟨11, 17, 9, 13, 10, 13, false, false, false⟩, ⟨3, 12, 1, 1, 6, 1, true, false, false⟩, ⟨1, 13, 3, 1, 8, 1, false, false, false⟩, ⟨12, 18, 13, 13, 9, 3, true, false, false⟩, ⟨3, 6, 1, 1, 12, 1, true, false, false⟩, ⟨13, 19, 12, 1, 11, 1, false, false, false⟩, ⟨1, 8, 3, 1, 13, 1, false, false, false⟩, ⟨4, 14, 7, 1, 1, 1, false, true, false⟩, ⟨1, 13, 8, 1, 4, 1, false, false, false⟩, ⟨14, 22, 10, 4, 13, 13, false, true, false⟩],
  #[⟨13, 19, 11, 1, 14, 1, false, false, false⟩, ⟨4, 7, 14, 1, 1, 1, false, true, false⟩, ⟨1, 8, 13, 1, 4, 1, false, false, false⟩, ⟨1, 8, 13, 1, 13, 1, false, false, false⟩, ⟨5, 5, 16, 16, 15, 15, true, true, false⟩, ⟨15, 15, 17, 17, 5, 18, true, false, false⟩, ⟨16, 16, 5, 22, 17, 17, false, true, false⟩, ⟨17, 17, 15, 19, 16, 19, false, false, false⟩, ⟨17, 17, 15, 20, 16, 20, false, false, false⟩, ⟨18, 18, 19, 19, 15, 6, true, false, false⟩, ⟨6, 9, 8, 8, 18, 3, true, false, false⟩, ⟨19, 20, 18, 8, 17, 8, false, false, false⟩, ⟨8, 21, 6, 1, 19, 1, false, false, false⟩, ⟨18, 18, 20, 20, 15, 9, true, false, false⟩, ⟨9, 25, 21, 21, 18, 12, true, false, false⟩, ⟨20, 20, 18, 24, 17, 21, false, false, false⟩],
  #[⟨21, 26, 9, 8, 20, 13, false, false, false⟩, ⟨22, 22, 16, 7, 19, 19, false, true, false⟩, ⟨19, 20, 17, 8, 22, 8, false, false, false⟩, ⟨7, 10, 22, 4, 8, 8, false, true, false⟩, ⟨8, 23, 19, 1, 7, 1, false, false, false⟩, ⟨22, 22, 16, 10, 20, 20, false, true, false⟩, ⟨20, 20, 17, 23, 22, 24, false, false, false⟩, ⟨10, 28, 22, 14, 23, 23, false, true, false⟩, ⟨23, 29, 20, 13, 10, 8, false, false, false⟩, ⟨8, 24, 19, 1, 19, 1, false, false, false⟩, ⟨1, 8, 8, 1, 8, 1, false, false, false⟩, ⟨24, 31, 20, 8, 20, 8, false, false, false⟩, ⟨8, 21, 21, 1, 24, 1, false, false, false⟩, ⟨8, 23, 24, 1, 23, 1, false, false, false⟩, ⟨18, 18, 20, 20, 15, 25, true, false, false⟩, ⟨25, 25, 26, 26, 18, 18, true, false, false⟩],
  #[⟨20, 20, 18, 31, 17, 26, false, false, false⟩, ⟨26, 27, 25, 21, 20, 34, false, false, false⟩, ⟨25, 25, 27, 27, 18, 35, true, false, false⟩, ⟨20, 20, 18, 31, 17, 27, false, false, false⟩, ⟨27, 41, 25, 32, 20, 36, false, false, false⟩, ⟨22, 22, 16, 28, 20, 20, false, true, false⟩, ⟨20, 20, 17, 29, 22, 31, false, false, false⟩, ⟨28, 28, 22, 22, 29, 29, false, true, false⟩, ⟨29, 30, 20, 38, 28, 23, false, false, false⟩, ⟨20, 20, 17, 30, 22, 31, false, false, false⟩, ⟨28, 28, 22, 39, 30, 30, false, true, false⟩, ⟨30, 42, 20, 40, 28, 33, false, false, false⟩, ⟨31, 31, 20, 23, 20, 21, false, false, false⟩, ⟨21, 32, 26, 8, 31, 13, false, false, false⟩, ⟨23, 33, 31, 13, 29, 8, false, false, false⟩, ⟨8, 11, 21, 1, 23, 1, false, false, false⟩],
  #[⟨31, 31, 20, 33, 20, 32, false, false, false⟩, ⟨32, 43, 27, 11, 31, 37, false, false, false⟩, ⟨33, 44, 31, 37, 30, 11, false, false, false⟩, ⟨11, 17, 32, 13, 33, 13, false, false, false⟩, ⟨13, 34, 12, 1, 21, 1, false, false, false⟩, ⟨1, 13, 13, 1, 8, 1, false, false, false⟩, ⟨18, 35, 34, 34, 25, 6, true, false, false⟩, ⟨34, 36, 18, 13, 26, 8, false, false, false⟩, ⟨8, 11, 6, 1, 34, 1, false, false, false⟩, ⟨35, 45, 36, 36, 25, 9, true, false, false⟩, ⟨9, 15, 11, 11, 35, 12, true, false, false⟩, ⟨36, 46, 35, 37, 27, 11, false, false, false⟩, ⟨11, 17, 9, 13, 36, 13, false, false, false⟩, ⟨13, 37, 34, 1, 21, 1, false, false, false⟩, ⟨1, 13, 8, 1, 13, 1, false, false, false⟩, ⟨37, 47, 36, 13, 32, 13, false, false, false⟩],
  #[⟨13, 19, 11, 1, 37, 1, false, false, false⟩, ⟨13, 19, 37, 1, 11, 1, false, false, false⟩, ⟨13, 38, 23, 1, 14, 1, false, false, false⟩, ⟨22, 39, 28, 7, 38, 38, false, true, false⟩, ⟨38, 40, 29, 8, 22, 13, false, false, false⟩, ⟨8, 11, 38, 1, 7, 1, false, false, false⟩, ⟨39, 48, 28, 10, 40, 40, false, true, false⟩, ⟨40, 49, 30, 11, 39, 37, false, false, false⟩, ⟨10, 16, 39, 14, 11, 11, false, true, false⟩, ⟨11, 17, 40, 13, 10, 13, false, false, false⟩, ⟨13, 37, 23, 1, 38, 1, false, false, false⟩, ⟨37, 47, 33, 13, 40, 13, false, false, false⟩, ⟨25, 25, 41, 41, 18, 45, true, false, false⟩, ⟨20, 20, 18, 31, 17, 41, false, false, false⟩, ⟨41, 41, 25, 43, 20, 46, false, false, false⟩, ⟨25, 25, 41, 41, 18, 35, true, false, false⟩],
  #[⟨20, 20, 17, 42, 22, 31, false, false, false⟩, ⟨28, 28, 22, 48, 42, 42, false, true, false⟩, ⟨42, 42, 20, 49, 28, 44, false, false, false⟩, ⟨28, 28, 22, 39, 42, 42, false, true, false⟩, ⟨31, 31, 20, 44, 20, 43, false, false, false⟩, ⟨43, 43, 41, 17, 31, 47, false, false, false⟩, ⟨44, 44, 31, 47, 42, 17, false, false, false⟩, ⟨17, 17, 43, 19, 44, 19, false, false, false⟩, ⟨17, 17, 43, 20, 44, 20, false, false, false⟩, ⟨45, 35, 46, 46, 25, 15, true, false, false⟩, ⟨15, 15, 17, 17, 45, 18, true, false, false⟩, ⟨46, 46, 45, 47, 41, 17, false, false, false⟩, ⟨17, 17, 15, 19, 46, 19, false, false, false⟩, ⟨35, 45, 46, 46, 25, 15, true, false, false⟩, ⟨15, 15, 17, 17, 35, 18, true, false, false⟩, ⟨46, 46, 35, 47, 41, 17, false, false, false⟩],
  #[⟨17, 17, 15, 20, 46, 20, false, false, false⟩, ⟨47, 47, 46, 19, 43, 19, false, false, false⟩, ⟨19, 20, 17, 8, 47, 8, false, false, false⟩, ⟨19, 20, 47, 8, 17, 8, false, false, false⟩, ⟨47, 47, 46, 20, 43, 20, false, false, false⟩, ⟨20, 20, 17, 24, 47, 24, false, false, false⟩, ⟨20, 20, 47, 24, 17, 24, false, false, false⟩, ⟨8, 24, 24, 1, 24, 1, false, false, false⟩, ⟨20, 20, 17, 31, 47, 31, false, false, false⟩, ⟨20, 20, 47, 31, 17, 31, false, false, false⟩, ⟨31, 31, 20, 24, 20, 24, false, false, false⟩, ⟨31, 31, 20, 31, 20, 31, false, false, false⟩, ⟨31, 31, 20, 24, 20, 21, false, false, false⟩, ⟨24, 31, 31, 8, 31, 8, false, false, false⟩, ⟨31, 31, 20, 31, 20, 32, false, false, false⟩, ⟨32, 43, 27, 21, 31, 37, false, false, false⟩],
  #[⟨31, 31, 31, 24, 31, 21, false, false, false⟩, ⟨21, 26, 32, 8, 31, 13, false, false, false⟩, ⟨48, 39, 28, 16, 49, 49, false, true, false⟩, ⟨49, 49, 42, 17, 48, 47, false, false, false⟩, ⟨16, 16, 48, 22, 17, 17, false, true, false⟩, ⟨17, 17, 49, 19, 16, 19, false, false, false⟩, ⟨39, 48, 28, 16, 49, 49, false, true, false⟩, ⟨49, 49, 42, 17, 39, 47, false, false, false⟩, ⟨16, 16, 39, 22, 17, 17, false, true, false⟩, ⟨17, 17, 49, 20, 16, 20, false, false, false⟩, ⟨47, 47, 44, 19, 49, 19, false, false, false⟩, ⟨47, 47, 44, 20, 49, 20, false, false, false⟩, ⟨31, 31, 20, 23, 20, 24, false, false, false⟩, ⟨31, 31, 20, 33, 20, 31, false, false, false⟩, ⟨31, 31, 31, 23, 31, 24, false, false, false⟩, ⟨33, 44, 31, 37, 30, 23, false, false, false⟩],
  #[⟨23, 29, 31, 13, 33, 8, false, false, false⟩, ⟨31, 31, 31, 24, 31, 24, false, false, false⟩, ⟨31, 31, 20, 31, 20, 43, false, false, false⟩, ⟨43, 43, 41, 26, 31, 47, false, false, false⟩, ⟨31, 31, 31, 31, 31, 26, false, false, false⟩, ⟨26, 27, 43, 21, 31, 34, false, false, false⟩, ⟨43, 43, 41, 27, 31, 54, false, false, false⟩, ⟨31, 31, 31, 31, 31, 27, false, false, false⟩, ⟨27, 50, 43, 32, 31, 36, false, false, false⟩, ⟨41, 41, 25, 43, 20, 55, false, false, false⟩, ⟨43, 43, 41, 50, 31, 47, false, false, false⟩, ⟨31, 31, 31, 31, 31, 50, false, false, false⟩, ⟨50, 41, 43, 43, 31, 55, false, false, false⟩, ⟨43, 43, 41, 41, 31, 47, false, false, false⟩, ⟨31, 31, 31, 31, 31, 41, false, false, false⟩, ⟨41, 41, 43, 52, 31, 55, false, false, false⟩],
  #[⟨31, 31, 20, 44, 20, 31, false, false, false⟩, ⟨31, 31, 31, 29, 31, 31, false, false, false⟩, ⟨44, 44, 31, 47, 42, 29, false, false, false⟩, ⟨29, 30, 31, 38, 44, 23, false, false, false⟩, ⟨31, 31, 31, 30, 31, 31, false, false, false⟩, ⟨44, 44, 31, 54, 42, 30, false, false, false⟩, ⟨30, 51, 31, 40, 44, 33, false, false, false⟩, ⟨42, 42, 20, 56, 28, 44, false, false, false⟩, ⟨31, 31, 31, 51, 31, 31, false, false, false⟩, ⟨44, 44, 31, 47, 42, 51, false, false, false⟩, ⟨51, 42, 31, 56, 44, 44, false, false, false⟩, ⟨31, 31, 31, 42, 31, 31, false, false, false⟩, ⟨44, 44, 31, 47, 42, 42, false, false, false⟩, ⟨42, 42, 31, 56, 44, 53, false, false, false⟩, ⟨31, 31, 31, 31, 31, 31, false, false, false⟩, ⟨31, 31, 31, 31, 31, 32, false, false, false⟩],
  #[⟨31, 31, 31, 33, 31, 31, false, false, false⟩, ⟨31, 31, 31, 31, 31, 43, false, false, false⟩, ⟨43, 52, 50, 26, 31, 47, false, false, false⟩, ⟨31, 31, 31, 31, 31, 52, false, false, false⟩, ⟨52, 52, 41, 27, 31, 54, false, false, false⟩, ⟨27, 41, 52, 32, 31, 36, false, false, false⟩, ⟨31, 31, 31, 44, 31, 31, false, false, false⟩, ⟨44, 53, 31, 47, 51, 29, false, false, false⟩, ⟨31, 31, 31, 53, 31, 31, false, false, false⟩, ⟨53, 53, 31, 54, 42, 30, false, false, false⟩, ⟨30, 42, 31, 40, 53, 33, false, false, false⟩, ⟨31, 31, 31, 23, 31, 21, false, false, false⟩, ⟨31, 31, 31, 33, 31, 32, false, false, false⟩, ⟨13, 34, 37, 1, 21, 1, false, false, false⟩, ⟨46, 55, 35, 54, 41, 17, false, false, false⟩, ⟨47, 54, 46, 34, 43, 19, false, false, false⟩],
  #[⟨34, 36, 47, 13, 26, 8, false, false, false⟩, ⟨8, 23, 19, 1, 34, 1, false, false, false⟩, ⟨54, 47, 46, 36, 43, 20, false, false, false⟩, ⟨20, 20, 17, 23, 54, 24, false, false, false⟩, ⟨36, 55, 54, 37, 27, 23, false, false, false⟩, ⟨23, 29, 20, 13, 36, 8, false, false, false⟩, ⟨45, 45, 55, 55, 25, 15, true, false, false⟩, ⟨55, 55, 45, 47, 41, 17, false, false, false⟩, ⟨17, 17, 15, 20, 55, 20, false, false, false⟩, ⟨47, 47, 55, 55, 43, 20, false, false, false⟩, ⟨20, 20, 17, 29, 47, 31, false, false, false⟩, ⟨55, 55, 47, 47, 50, 29, false, false, false⟩, ⟨29, 30, 20, 38, 55, 23, false, false, false⟩, ⟨20, 20, 17, 30, 47, 31, false, false, false⟩, ⟨55, 55, 47, 54, 41, 30, false, false, false⟩, ⟨30, 42, 20, 40, 55, 33, false, false, false⟩],
  #[⟨13, 38, 23, 1, 37, 1, false, false, false⟩, ⟨47, 54, 55, 34, 43, 38, false, false, false⟩, ⟨38, 40, 29, 8, 47, 13, false, false, false⟩, ⟨8, 11, 38, 1, 34, 1, false, false, false⟩, ⟨54, 47, 55, 36, 52, 40, false, false, false⟩, ⟨40, 49, 30, 11, 54, 37, false, false, false⟩, ⟨36, 46, 54, 37, 27, 11, false, false, false⟩, ⟨11, 17, 40, 13, 36, 13, false, false, false⟩, ⟨49, 56, 42, 17, 39, 54, false, false, false⟩, ⟨47, 54, 44, 19, 49, 38, false, false, false⟩, ⟨8, 21, 38, 1, 19, 1, false, false, false⟩, ⟨54, 47, 44, 20, 49, 40, false, false, false⟩, ⟨40, 56, 30, 21, 54, 37, false, false, false⟩, ⟨20, 20, 54, 24, 17, 21, false, false, false⟩, ⟨21, 26, 40, 8, 20, 13, false, false, false⟩, ⟨48, 48, 28, 16, 56, 56, false, true, false⟩],
  #[⟨56, 56, 42, 17, 48, 47, false, false, false⟩, ⟨17, 17, 56, 20, 16, 20, false, false, false⟩, ⟨47, 47, 44, 20, 56, 56, false, false, false⟩, ⟨56, 56, 51, 26, 47, 47, false, false, false⟩, ⟨20, 20, 47, 31, 17, 26, false, false, false⟩, ⟨26, 27, 56, 21, 20, 34, false, false, false⟩, ⟨56, 56, 42, 27, 47, 54, false, false, false⟩, ⟨20, 20, 47, 31, 17, 27, false, false, false⟩, ⟨27, 41, 56, 32, 20, 36, false, false, false⟩, ⟨47, 54, 44, 34, 56, 38, false, false, false⟩, ⟨54, 47, 53, 36, 56, 40, false, false, false⟩, ⟨52, 52, 41, 41, 31, 47, false, false, false⟩, ⟨41, 41, 52, 43, 31, 46, false, false, false⟩, ⟨53, 53, 31, 47, 42, 42, false, false, false⟩, ⟨42, 42, 31, 49, 53, 44, false, false, false⟩, ⟨31, 31, 31, 44, 31, 43, false, false, false⟩],
  #[⟨20, 20, 17, 42, 47, 31, false, false, false⟩, ⟨55, 55, 47, 47, 41, 42, false, false, false⟩, ⟨42, 42, 20, 49, 55, 44, false, false, false⟩, ⟨47, 47, 55, 46, 52, 49, false, false, false⟩, ⟨49, 49, 42, 17, 47, 47, false, false, false⟩, ⟨46, 46, 47, 47, 41, 17, false, false, false⟩, ⟨17, 17, 49, 19, 46, 19, false, false, false⟩, ⟨17, 17, 49, 20, 46, 20, false, false, false⟩, ⟨56, 56, 42, 41, 47, 47, false, false, false⟩, ⟨20, 20, 47, 31, 17, 41, false, false, false⟩, ⟨41, 41, 56, 43, 20, 46, false, false, false⟩, ⟨47, 47, 53, 46, 56, 49, false, false, false⟩, ⟨46, 46, 47, 54, 41, 17, false, false, false⟩, ⟨47, 47, 46, 55, 43, 20, false, false, false⟩, ⟨49, 49, 42, 17, 47, 54, false, false, false⟩, ⟨47, 47, 44, 20, 49, 56, false, false, false⟩]]

def links : Array (Array (Array ℕ)) := #[
  #[#[0, 1, 2, 3, 4, 5, 6, 7], #[8, 8, 3, 3, 9, 10, 11, 11], #[12, 3, 12, 3, 13, 11, 14, 11], #[3, 3, 3, 3, 11, 11, 11, 11], #[15, 16, 17, 18, 19, 20, 21, 22], #[23, 9, 24, 11, 25, 26, 27, 28], #[29, 30, 13, 11, 31, 32, 33, 34], #[11, 11, 11, 11, 35, 11, 11, 11], #[8, 8, 3, 3, 10, 10, 11, 11], #[10, 10, 11, 11, 9, 10, 11, 11], #[10, 10, 11, 11, 10, 10, 11, 11], #[11, 11, 11, 11, 11, 11, 11, 11], #[12, 3, 12, 3, 14, 11, 14, 11], #[14, 11, 14, 11, 13, 11, 14, 11], #[14, 11, 14, 11, 14, 11, 14, 11], #[36, 37, 38, 39, 36, 37, 38, 40]],
  #[#[41, 42, 43, 44, 45, 46, 47, 48], #[49, 50, 51, 52, 53, 54, 55, 56], #[57, 58, 58, 11, 59, 60, 61, 58], #[36, 37, 38, 40, 36, 37, 38, 40], #[62, 63, 64, 65, 62, 66, 67, 68], #[69, 70, 71, 72, 69, 73, 74, 75], #[76, 77, 78, 79, 80, 81, 82, 83], #[23, 9, 24, 11, 25, 26, 84, 28], #[11, 11, 11, 11, 85, 11, 11, 11], #[86, 42, 87, 88, 89, 90, 91, 92], #[23, 9, 24, 11, 25, 26, 27, 28], #[93, 94, 85, 11, 95, 96, 97, 35], #[11, 11, 11, 11, 35, 11, 11, 11], #[29, 30, 13, 11, 31, 98, 33, 34], #[11, 11, 11, 11, 94, 11, 11, 11], #[99, 100, 51, 101, 102, 103, 104, 105]],
  #[#[106, 94, 85, 11, 107, 96, 97, 35], #[29, 30, 13, 11, 31, 32, 33, 34], #[11, 11, 11, 11, 35, 11, 11, 11], #[11, 11, 11, 11, 35, 11, 11, 11], #[36, 37, 38, 40, 36, 37, 38, 40], #[62, 108, 109, 110, 62, 111, 109, 110], #[69, 112, 113, 114, 69, 112, 115, 114], #[116, 117, 118, 119, 116, 117, 118, 120], #[116, 117, 118, 120, 116, 117, 118, 120], #[121, 122, 123, 124, 125, 126, 127, 128], #[41, 42, 43, 44, 45, 46, 47, 48], #[129, 130, 131, 57, 132, 133, 134, 59], #[57, 58, 58, 11, 59, 60, 135, 58], #[121, 122, 123, 128, 125, 126, 127, 128], #[62, 63, 64, 65, 62, 66, 67, 68], #[132, 136, 137, 138, 132, 136, 137, 139]],
  #[#[140, 77, 141, 60, 142, 143, 144, 145], #[146, 147, 148, 149, 150, 151, 152, 153], #[154, 130, 131, 57, 155, 133, 134, 59], #[49, 50, 51, 52, 53, 54, 55, 56], #[57, 58, 58, 11, 59, 135, 61, 58], #[146, 147, 148, 153, 150, 151, 152, 153], #[155, 136, 137, 138, 155, 136, 137, 139], #[69, 70, 71, 72, 69, 73, 74, 75], #[156, 141, 78, 61, 157, 158, 159, 160], #[57, 58, 58, 11, 59, 135, 135, 58], #[11, 11, 11, 11, 58, 11, 11, 11], #[138, 141, 141, 135, 139, 161, 161, 141], #[135, 58, 58, 11, 141, 60, 135, 58], #[135, 58, 58, 11, 141, 135, 61, 58], #[121, 122, 123, 128, 125, 126, 127, 128], #[62, 108, 109, 110, 62, 111, 109, 110]],
  #[#[132, 136, 137, 139, 132, 136, 137, 139], #[162, 163, 164, 165, 162, 166, 167, 168], #[62, 108, 109, 169, 62, 108, 109, 169], #[132, 136, 137, 139, 132, 136, 137, 139], #[162, 170, 171, 172, 162, 173, 174, 175], #[146, 147, 148, 153, 150, 151, 152, 153], #[155, 136, 137, 139, 155, 136, 137, 139], #[69, 112, 113, 114, 69, 112, 115, 114], #[176, 177, 178, 179, 176, 180, 181, 182], #[155, 136, 137, 139, 155, 136, 137, 139], #[69, 112, 113, 183, 69, 112, 113, 183], #[176, 184, 185, 186, 176, 187, 188, 189], #[139, 190, 190, 161, 139, 190, 190, 190], #[144, 77, 141, 60, 191, 143, 144, 145], #[158, 141, 78, 61, 192, 158, 159, 160], #[135, 58, 58, 11, 141, 60, 61, 58]],
  #[#[139, 190, 190, 190, 139, 190, 190, 190], #[193, 194, 164, 165, 195, 196, 167, 197], #[198, 177, 199, 179, 200, 180, 201, 202], #[203, 77, 78, 79, 204, 81, 82, 83], #[93, 94, 85, 11, 95, 96, 205, 35], #[11, 11, 11, 11, 85, 11, 11, 11], #[121, 122, 123, 124, 125, 126, 206, 128], #[207, 130, 208, 209, 210, 211, 212, 213], #[57, 58, 58, 11, 59, 60, 61, 58], #[214, 122, 215, 216, 214, 122, 215, 216], #[62, 63, 64, 65, 62, 66, 67, 68], #[217, 218, 219, 220, 217, 221, 222, 223], #[76, 77, 78, 79, 80, 81, 82, 83], #[93, 94, 85, 11, 95, 224, 205, 35], #[11, 11, 11, 11, 94, 11, 11, 11], #[225, 226, 208, 227, 228, 229, 230, 231]],
  #[#[106, 94, 85, 11, 107, 96, 97, 35], #[93, 94, 85, 11, 95, 96, 97, 35], #[106, 94, 85, 11, 107, 224, 97, 35], #[146, 147, 148, 149, 150, 232, 152, 153], #[233, 226, 131, 234, 235, 236, 237, 238], #[57, 58, 58, 11, 59, 60, 61, 58], #[239, 240, 148, 241, 239, 240, 148, 241], #[242, 243, 244, 245, 242, 246, 247, 248], #[69, 70, 71, 72, 69, 73, 74, 75], #[76, 77, 78, 79, 80, 81, 82, 83], #[106, 94, 85, 11, 107, 224, 205, 35], #[249, 226, 208, 227, 250, 229, 230, 231], #[62, 108, 109, 169, 62, 108, 109, 169], #[132, 136, 137, 139, 132, 136, 137, 139], #[162, 173, 174, 175, 162, 173, 174, 175], #[62, 108, 109, 169, 62, 108, 109, 169]],
  #[#[155, 136, 137, 139, 155, 136, 137, 139], #[69, 112, 113, 183, 69, 112, 113, 183], #[176, 187, 188, 189, 176, 187, 188, 189], #[69, 112, 113, 183, 69, 112, 113, 183], #[139, 190, 190, 190, 139, 190, 190, 190], #[195, 251, 174, 252, 195, 251, 174, 252], #[200, 187, 253, 254, 200, 187, 253, 254], #[255, 117, 118, 119, 255, 117, 118, 120], #[255, 117, 118, 120, 255, 117, 118, 120], #[214, 122, 215, 216, 214, 122, 215, 216], #[62, 108, 109, 110, 62, 111, 109, 110], #[217, 256, 257, 258, 217, 256, 257, 258], #[116, 117, 118, 119, 116, 117, 118, 120], #[214, 122, 215, 216, 214, 122, 215, 216], #[62, 108, 109, 110, 62, 111, 109, 110], #[217, 256, 257, 258, 217, 256, 257, 258]],
  #[#[116, 117, 118, 120, 116, 117, 118, 120], #[259, 260, 261, 262, 259, 260, 261, 263], #[154, 130, 131, 57, 155, 133, 134, 59], #[129, 130, 131, 57, 132, 133, 134, 59], #[259, 260, 261, 263, 259, 260, 261, 263], #[155, 136, 137, 138, 155, 136, 137, 139], #[132, 136, 137, 138, 132, 136, 137, 139], #[135, 58, 58, 11, 141, 135, 135, 58], #[155, 136, 137, 139, 155, 136, 137, 139], #[132, 136, 137, 139, 132, 136, 137, 139], #[139, 190, 190, 161, 139, 190, 190, 190], #[139, 190, 190, 190, 139, 190, 190, 190], #[139, 190, 190, 161, 139, 190, 190, 190], #[161, 141, 141, 135, 190, 161, 161, 141], #[139, 190, 190, 190, 139, 190, 190, 190], #[193, 194, 164, 165, 195, 196, 167, 197]],
  #[#[190, 190, 190, 161, 190, 190, 190, 190], #[144, 77, 141, 60, 191, 143, 144, 145], #[239, 240, 148, 241, 239, 240, 148, 241], #[242, 264, 265, 266, 242, 264, 265, 266], #[69, 112, 113, 114, 69, 112, 115, 114], #[116, 117, 118, 119, 116, 117, 118, 120], #[239, 240, 148, 241, 239, 240, 148, 241], #[242, 264, 265, 266, 242, 264, 265, 266], #[69, 112, 113, 114, 69, 112, 115, 114], #[116, 117, 118, 120, 116, 117, 118, 120], #[267, 260, 261, 262, 267, 260, 261, 263], #[267, 260, 261, 263, 267, 260, 261, 263], #[139, 190, 190, 161, 139, 190, 190, 190], #[139, 190, 190, 190, 139, 190, 190, 190], #[190, 190, 190, 161, 190, 190, 190, 190], #[198, 177, 199, 179, 200, 180, 201, 202]],
  #[#[158, 141, 78, 61, 192, 158, 159, 160], #[190, 190, 190, 161, 190, 190, 190, 190], #[139, 190, 190, 190, 139, 190, 190, 190], #[195, 251, 174, 252, 195, 251, 174, 252], #[190, 190, 190, 190, 190, 190, 190, 190], #[193, 163, 164, 165, 193, 166, 167, 168], #[195, 251, 174, 252, 195, 251, 174, 252], #[190, 190, 190, 190, 190, 190, 190, 190], #[193, 170, 171, 172, 193, 173, 174, 175], #[162, 173, 174, 175, 162, 173, 174, 175], #[195, 251, 174, 252, 195, 251, 174, 252], #[190, 190, 190, 190, 190, 190, 190, 190], #[193, 173, 174, 175, 193, 173, 174, 175], #[195, 251, 174, 252, 195, 251, 174, 252], #[190, 190, 190, 190, 190, 190, 190, 190], #[193, 173, 174, 175, 193, 173, 174, 175]],
  #[#[139, 190, 190, 190, 139, 190, 190, 190], #[190, 190, 190, 190, 190, 190, 190, 190], #[200, 187, 253, 254, 200, 187, 253, 254], #[198, 177, 178, 179, 198, 180, 181, 182], #[190, 190, 190, 190, 190, 190, 190, 190], #[200, 187, 253, 254, 200, 187, 253, 254], #[198, 184, 185, 186, 198, 187, 188, 189], #[176, 187, 188, 189, 176, 187, 188, 189], #[190, 190, 190, 190, 190, 190, 190, 190], #[200, 187, 253, 254, 200, 187, 253, 254], #[198, 187, 188, 189, 198, 187, 188, 189], #[190, 190, 190, 190, 190, 190, 190, 190], #[200, 187, 253, 254, 200, 187, 253, 254], #[198, 187, 188, 189, 198, 187, 188, 189], #[190, 190, 190, 190, 190, 190, 190, 190], #[190, 190, 190, 190, 190, 190, 190, 190]],
  #[#[190, 190, 190, 190, 190, 190, 190, 190], #[190, 190, 190, 190, 190, 190, 190, 190], #[195, 251, 174, 252, 195, 251, 174, 252], #[190, 190, 190, 190, 190, 190, 190, 190], #[195, 251, 174, 252, 195, 251, 174, 252], #[193, 170, 171, 172, 193, 173, 174, 175], #[190, 190, 190, 190, 190, 190, 190, 190], #[200, 187, 253, 254, 200, 187, 253, 254], #[190, 190, 190, 190, 190, 190, 190, 190], #[200, 187, 253, 254, 200, 187, 253, 254], #[198, 184, 185, 186, 198, 187, 188, 189], #[190, 190, 190, 161, 190, 190, 190, 190], #[190, 190, 190, 190, 190, 190, 190, 190], #[93, 94, 85, 11, 95, 96, 205, 35], #[217, 256, 257, 258, 217, 256, 257, 258], #[259, 260, 261, 262, 259, 260, 268, 263]],
  #[#[207, 130, 208, 209, 210, 211, 212, 213], #[57, 58, 58, 11, 59, 135, 61, 58], #[259, 260, 261, 263, 259, 260, 261, 263], #[155, 136, 137, 138, 155, 136, 137, 139], #[269, 218, 219, 220, 269, 221, 222, 223], #[156, 141, 78, 61, 157, 158, 159, 160], #[214, 122, 215, 216, 214, 122, 215, 216], #[217, 256, 257, 258, 217, 256, 257, 258], #[116, 117, 118, 120, 116, 117, 118, 120], #[259, 260, 261, 263, 259, 260, 261, 263], #[155, 136, 137, 139, 155, 136, 137, 139], #[269, 256, 257, 258, 269, 256, 257, 258], #[176, 177, 178, 179, 176, 180, 181, 182], #[155, 136, 137, 139, 155, 136, 137, 139], #[269, 256, 257, 258, 269, 256, 257, 258], #[176, 184, 185, 186, 176, 187, 188, 189]],
  #[#[106, 94, 85, 11, 107, 224, 97, 35], #[259, 260, 261, 262, 259, 270, 268, 263], #[233, 226, 131, 234, 235, 236, 237, 238], #[57, 58, 58, 11, 59, 60, 61, 58], #[259, 260, 261, 263, 259, 260, 261, 263], #[271, 243, 244, 245, 271, 246, 247, 248], #[269, 218, 219, 220, 269, 221, 222, 223], #[76, 77, 78, 79, 80, 81, 82, 83], #[242, 264, 265, 266, 242, 264, 265, 266], #[267, 260, 261, 262, 267, 270, 261, 263], #[57, 58, 58, 11, 59, 60, 135, 58], #[267, 260, 261, 263, 267, 260, 261, 263], #[271, 243, 244, 245, 271, 246, 247, 248], #[132, 136, 137, 138, 132, 136, 137, 139], #[140, 77, 141, 60, 142, 143, 144, 145], #[239, 240, 148, 241, 239, 240, 148, 241]],
  #[#[242, 264, 265, 266, 242, 264, 265, 266], #[116, 117, 118, 120, 116, 117, 118, 120], #[267, 260, 261, 263, 267, 260, 261, 263], #[271, 264, 265, 266, 271, 264, 265, 266], #[132, 136, 137, 139, 132, 136, 137, 139], #[162, 163, 164, 165, 162, 166, 167, 168], #[271, 264, 265, 266, 271, 264, 265, 266], #[132, 136, 137, 139, 132, 136, 137, 139], #[162, 170, 171, 172, 162, 173, 174, 175], #[267, 260, 261, 262, 267, 270, 268, 263], #[267, 260, 261, 263, 267, 260, 261, 263], #[195, 251, 174, 252, 195, 251, 174, 252], #[193, 173, 174, 175, 193, 173, 174, 175], #[200, 187, 253, 254, 200, 187, 253, 254], #[198, 187, 188, 189, 198, 187, 188, 189], #[190, 190, 190, 190, 190, 190, 190, 190]],
  #[#[155, 136, 137, 139, 155, 136, 137, 139], #[269, 256, 257, 258, 269, 256, 257, 258], #[176, 187, 188, 189, 176, 187, 188, 189], #[259, 260, 261, 263, 259, 260, 261, 263], #[271, 264, 265, 266, 271, 264, 265, 266], #[269, 256, 257, 258, 269, 256, 257, 258], #[116, 117, 118, 119, 116, 117, 118, 120], #[116, 117, 118, 120, 116, 117, 118, 120], #[271, 264, 265, 266, 271, 264, 265, 266], #[132, 136, 137, 139, 132, 136, 137, 139], #[162, 173, 174, 175, 162, 173, 174, 175], #[267, 260, 261, 263, 267, 260, 261, 263], #[269, 256, 257, 258, 269, 256, 257, 258], #[259, 260, 261, 263, 259, 260, 261, 263], #[271, 264, 265, 266, 271, 264, 265, 266], #[267, 260, 261, 263, 267, 260, 261, 263]]]

abbrev Index := Fin 272

def window (i : Index) : Local := ((windows[i.val / 16]?.getD #[])[i.val % 16]?).getD default

def link (i : Index) (t x y : Bool) : Index :=
  ⟨((((links[i.val / 16]?.getD #[])[i.val % 16]?.getD #[])[code t x y]?).getD 0) % 272,
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

lemma natural_law (r t x y : ℕ) (hr : r = 694) :
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
  · subst hr; exact h.2

def plane (t : ℕ) (x y : ℤ) := value t x.natAbs y.natAbs

lemma plane_zero (x y : ℤ) : plane 0 x y = decide (x = 0 ∧ y = 0) := by
  simpa [plane] using (natural_law 694 0 x.natAbs y.natAbs (rfl : 694 = 694)).1 rfl

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

lemma plane_step (r t : ℕ) (x y : ℤ) (hr : r = 694) :
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

lemma outside (r t : ℕ) (hr : r = 694) (x y : ℤ)
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

lemma stages (r t : ℕ) (hr : r = 694) :
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

lemma small_go : ∀ q : Fin 57, ∀ t x y : Bool, go q.val t x y < 57 := by decide +kernel

lemma small_address (w t x y : ℕ) : address w t x y < 57 := by
  induction w generalizing t x y with
  | zero => change 0 < 57; decide
  | succ w ih => exact small_go ⟨_, ih (t / 2) (x / 2) (y / 2)⟩ _ _ _

def iterate (k : ℕ) (u v : Bool) : ℕ → ℤ :=
  match k with
  | 0 => weight
  | k + 1 => mix u v (iterate k u v)

def iterVec (k : ℕ) (u v : Bool) : List ℤ :=
  match k with
  | 0 => (List.range 57).map weight
  | k + 1 =>
    let prev := iterVec k u v
    (List.range 57).map (fun q => mix u v (fun s => prev.getD s 0) q)

lemma iterVec_eq (k : ℕ) (u v : Bool) :
    ∀ q < 57, (iterVec k u v).getD q 0 = iterate k u v q := by
  induction k with
  | zero =>
    intro q hq
    exact getD_map_range 57 weight q 0 hq
  | succ k ih =>
    intro q hq
    unfold iterVec iterate
    dsimp only
    rw [getD_map_range 57 _ q 0 hq]
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
    let v3 := iterVec 3 u v
    let v4 := iterVec 4 u v
    let v5 := iterVec 5 u v
    let v6 := iterVec 6 u v
    let v7 := iterVec 7 u v
    ∀ q : Fin 57, v7.getD q.val 0 = 10 * v6.getD q.val 0 - 35 * v5.getD q.val 0 + 50 * v4.getD q.val 0 - 24 * v3.getD q.val 0 := by
  decide +kernel

lemma iter_rec (u v : Bool) (q : Fin 57) :
    iterate 7 u v q.val = 10 * iterate 6 u v q.val - 35 * iterate 5 u v q.val + 50 * iterate 4 u v q.val - 24 * iterate 3 u v q.val := by
  simpa only [iterVec_eq _ u v q.val q.isLt] using iter_vec_rec u v q

lemma count_rec (n : ℕ) (u v : Bool) :
    count (n + 7) u v = 10 * count (n + 6) u v - 35 * count (n + 5) u v + 50 * count (n + 4) u v - 24 * count (n + 3) u v := by
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

lemma sampled_eq (n r : ℕ) (hr : r = 694) : (countOn r (2 ^ n - 1) : ℤ) =
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

lemma sampled_fast (n r : ℕ) (hr : r = 694) : (countOn r (2 ^ n - 1) : ℤ) =
    4 * (iterVec n true true).getD 0 0 - 2 * (iterVec n false true).getD 0 0 -
      2 * (iterVec n true false).getD 0 0 + (iterVec n false false).getD 0 0 := by
  rw [sampled_eq n r hr]
  simp only [count_eq_iterVec]

end Scale694


section Proof_a272832

lemma a_rec (n : ℕ) :
    (a (n + 7) : ℤ) = 10 * a (n + 6) - 35 * a (n + 5) + 50 * a (n + 4) - 24 * a (n + 3) := by
  simp only [a, Scale694.sampled_eq _ 694 rfl, Scale694.count_rec n]
  ring

lemma recurrence (n : ℕ) (h : 6 < n) :
    (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4) := by
  simpa only [show n - 7 + 7 = n by omega, show n - 7 + 6 = n - 1 by omega,
    show n - 7 + 5 = n - 2 by omega, show n - 7 + 4 = n - 3 by omega,
    show n - 7 + 3 = n - 4 by omega] using a_rec (n - 7)

lemma a_init :
    (a 0 : ℤ) = 1 ∧ (a 1 : ℤ) = 5 ∧ (a 2 : ℤ) = 21 ∧ (a 3 : ℤ) = 85 ∧
    (a 4 : ℤ) = 377 ∧ (a 5 : ℤ) = 1633 ∧ (a 6 : ℤ) = 6929 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a, Scale694.sampled_fast 0 694 rfl]; decide +kernel
  · rw [a, Scale694.sampled_fast 1 694 rfl]; decide +kernel
  · rw [a, Scale694.sampled_fast 2 694 rfl]; decide +kernel
  · rw [a, Scale694.sampled_fast 3 694 rfl]; decide +kernel
  · rw [a, Scale694.sampled_fast 4 694 rfl]; decide +kernel
  · rw [a, Scale694.sampled_fast 5 694 rfl]; decide +kernel
  · rw [a, Scale694.sampled_fast 6 694 rfl]; decide +kernel

set_option maxHeartbeats 2000000 in
lemma alg_a272832 (F : ℕ → ℤ)
    (hinit : F 0 = 1 ∧ F 1 = 5 ∧ F 2 = 21 ∧ F 3 = 85 ∧ F 4 = 377 ∧ F 5 = 1633 ∧ F 6 = 6929)
    (hrec : ∀ n, F (n + 7) = 10 * F (n + 6) - 35 * F (n + 5) + 50 * F (n + 4) - 24 * F (n + 3)) :
    (∀ n, 2 < n → F n = 2 * 4 ^ n - 16 * 3 ^ (n - 2) + 2 ^ (n - 1) + 1) ∧
    (PowerSeries.mk F * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      1 - 5 * X + 6 * X ^ 2 + 36 * X ^ 4 - 92 * X ^ 5 + 48 * X ^ 6) := by
  have recurrence : ∀ n, 6 < n →
      F n = 10 * F (n - 1) - 35 * F (n - 2) + 50 * F (n - 3) - 24 * F (n - 4) := by
    intro n hn
    simpa only [show n - 7 + 7 = n by omega, show n - 7 + 6 = n - 1 by omega,
      show n - 7 + 5 = n - 2 by omega, show n - 7 + 4 = n - 3 by omega,
      show n - 7 + 3 = n - 4 by omega] using hrec (n - 7)
  refine ⟨?_, ?_⟩
  · intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 7
      · rcases hinit with ⟨_, _, _, v3, v4, v5, v6⟩
        interval_cases n <;> norm_num [v3, v4, v5, v6]
      · let k := n - 7
        have hk : n = k + 7 := by dsimp [k]; omega
        have h3 := ih (k + 3) (by omega) (by omega)
        have h4 := ih (k + 4) (by omega) (by omega)
        have h5 := ih (k + 5) (by omega) (by omega)
        have h6 := ih (k + 6) (by omega) (by omega)
        rw [hk, hrec k, h3, h4, h5, h6]
        simp only [show k + 7 - 2 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
          show k + 5 - 2 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
          show k + 3 - 2 = k + 1 by omega, show k + 7 - 1 = k + 6 by omega,
          show k + 6 - 1 = k + 5 by omega, show k + 5 - 1 = k + 4 by omega,
          show k + 4 - 1 = k + 3 by omega, show k + 3 - 1 = k + 2 by omega, pow_add]
        ring
  · have hd : mk F * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
        mk F * X ^ 0 + (-10 : ℤ) • (mk F * X ^ 1) + (35 : ℤ) • (mk F * X ^ 2) +
        (-50 : ℤ) • (mk F * X ^ 3) + (24 : ℤ) • (mk F * X ^ 4) := by
      simp only [zsmul_eq_mul]; push_cast; ring
    have hp : (1 - 5 * X + 6 * X ^ 2 + 36 * X ^ 4 - 92 * X ^ 5 + 48 * X ^ 6 : PowerSeries ℤ) =
        X ^ 0 + (-5 : ℤ) • X ^ 1 + (6 : ℤ) • X ^ 2 + (36 : ℤ) • X ^ 4 +
        (-92 : ℤ) • X ^ 5 + (48 : ℤ) • X ^ 6 := by
      simp only [zsmul_eq_mul]; push_cast; ring
    rw [hd, hp]
    ext n
    simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    by_cases hn : n < 7
    · rcases hinit with ⟨v0, v1, v2, v3, v4, v5, v6⟩
      interval_cases n <;> norm_num [zsmul_eq_mul, v0, v1, v2, v3, v4, v5, v6]
    · have hr := recurrence n (by omega)
      simp only [if_pos (show 0 ≤ n by omega), Nat.sub_zero, zsmul_eq_mul,
        if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
        if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
        if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 4 by omega),
        if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega)]
      norm_num
      linarith only [hr]

end Proof_a272832

theorem OMA.solution : type_of% @OMA.S_oeis_a272832.main :=
  alg_a272832 (fun n => (a n : ℤ)) a_init a_rec
