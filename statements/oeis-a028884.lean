import Mathlib

/-!
# A028884: a(n) = (n + 3)^2 - 8 via Rule 94 and discriminants
Source: https://oeis.org/A028884 (Klaus Purath, Jan 04 2023)

Conjecture: a(n) = A079896(A265284(n-1)), for n >= 1.

Conventions.
* A265284(m) is the total number of ON cells in generations 0..m of the elementary
  cellular automaton Rule 94 (Wolfram code 94, binary 01011110), started from a single
  ON cell at position 0 on an otherwise OFF line. Generation t occupies the 2t+1 cells
  at positions -t..t (all other cells are OFF since 000 maps to 0); it is scanned here
  as positions j - t for j < 2t+1.
* A079896 lists the discriminants of indefinite binary quadratic forms, i.e. the
  natural numbers that are 0 or 1 mod 4 and are not squares, in increasing order.
  When the conjecture was made (Jan 2023) A079896 had offset 0, so A079896(0) = 5;
  N. J. A. Sloane changed the offset to 1 on Mar 14 2023. We use the offset 0 that the
  conjecture refers to: A079896(k) = Nat.nth IsDisc k. (Read with offset 1 the formula
  would already fail at n = 1, where a(1) = 8 but the first discriminant is 5.)
-/

namespace OMA.S_oeis_a028884

/-- The sequence A028884, offset 0. -/
def a (n : ℕ) : ℕ := (n + 3) ^ 2 - 8

/-- Rule 94: the new state of a cell with neighbourhood (l, c, r) is bit number
4l + 2c + r of the binary expansion of 94. -/
def rule94 (l c r : Bool) : Bool :=
  Nat.testBit 94 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `state t i`: is cell `i` ON in generation `t`? -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule94 (state t (i - 1)) (state t i) (state t (i + 1))

/-- Number of ON cells in generation `t` (positions -t..t). -/
def onCells (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun j : ℕ => state t ((j : ℤ) - (t : ℤ)) = true).card

/-- A265284(m): total number of ON cells in generations 0..m. -/
def A265284 (m : ℕ) : ℕ := ∑ t ∈ Finset.range (m + 1), onCells t

/-- Discriminants of indefinite binary quadratic forms: 0 or 1 mod 4 and not a square. -/
def IsDisc (k : ℕ) : Prop := (k % 4 = 0 ∨ k % 4 = 1) ∧ ¬ IsSquare k

/-- A079896 with the offset 0 in force when the conjecture was made. -/
noncomputable def A079896 (k : ℕ) : ℕ := Nat.nth IsDisc k

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A079896 (A265284 (n - 1)) := by
  sorry

end OMA.S_oeis_a028884
