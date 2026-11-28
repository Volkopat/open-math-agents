import Mathlib

/-!
# A199126: Number of nX1 0..2 arrays with values 0..2 introduced in row major order, the number of instances of each value within one of each other, and no element equal to any horizontal or vertical neighbor.

Source: https://oeis.org/A199126
Credit: @agchua

R. J. Mathar (Nov 01 2015), in the formula section of A199126:
  Conjecture: a(3n) = A190917(n).

An n X 1 array with entries 0..2 is a word w : Fin n → Fin 3. Values introduced in row major
order means that every value smaller than w k already occurs at an earlier position (so w 0 = 0,
and each new value is one more than the largest earlier value). The numbers of instances of the
values 0, 1, 2 must be within one of each other, and no entry may equal its neighbour (the only
neighbours in an n X 1 array are vertical). A190917 (offset 0) is the number of permutations of
n copies of 1..3 introduced in order 1..3 with no element equal to another within a distance of
1; below the values 1, 2, 3 are written 0, 1, 2, so these are the words of length 3n in which
each value occurs exactly n times. A199126 has offset 1, so the conjecture is stated for n >= 1.
-/

namespace OMA.S_oeis_a199126

/-- The number of positions at which the word w has the value v. -/
noncomputable def numOcc {m : ℕ} (w : Fin m → Fin 3) (v : Fin 3) : ℕ :=
  (Finset.univ.filter (fun i => w i = v)).card

/-- A199126(n): words of length n over 0..2, values introduced in order, the numbers of
instances of the values within one of each other, no two neighbours equal. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 3 =>
    (∀ k : Fin n, ∀ v : Fin 3, v < w k → ∃ i : Fin n, i < k ∧ w i = v) ∧
    (∀ u v : Fin 3, numOcc w u ≤ numOcc w v + 1) ∧
    (∀ i j : Fin n, i.val + 1 = j.val → w i ≠ w j))).card

/-- A190917(n): words of length 3n with each of the three values exactly n times, values
introduced in order, no two neighbours equal. -/
noncomputable def A190917 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin (3 * n) → Fin 3 =>
    (∀ v : Fin 3, numOcc w v = n) ∧
    (∀ k : Fin (3 * n), ∀ v : Fin 3, v < w k → ∃ i : Fin (3 * n), i < k ∧ w i = v) ∧
    (∀ i j : Fin (3 * n), i.val + 1 = j.val → w i ≠ w j))).card

/-- Mathar's conjecture: a(3n) = A190917(n) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (3 * n) = A190917 n := by
  sorry

end OMA.S_oeis_a199126
