import Mathlib

/-!
# A300139: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with 4*x - 3*y a square, where x,y,z,w are nonnegative integers with z <= w such that 10*x or y is a square.

Source: https://oeis.org/A300139
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 for all n >= 0, and a(n) = 1 only for n = 16^k*m with k = 0, 1, 2, ... and m = 0, 7, 8,
   13, 22, 23, 24, 31, 44, 56, 71, 79, 88, 109, 120, 152, 184, 472, 1912, 6008, 9080.
2. Each n = 0, 1, 2, ... can be written as x^2 + y^2 + z^2 + w^2 with 3*x - y twice a square, where
   x, y, z, w are nonnegative integers such that 5*x or y is a square.

Formalization notes:
* 4x - 3y and 3x - y are computed in ℤ; "a square" means s^2 for an integer s, "twice a square" 2 s^2.
* a(n) counts quadruples with entries ≤ n. "a(n) = 1 only for n = 16^k m" is stated as an equivalence
  for all n ≥ 0.
* Controls (computed): for n < 1500, a(n) > 0, a(n) = 1 exactly on the stated family, and
  conjecture 2 holds.
-/

namespace OMA.S_oeis_a300139

open Classical in
/-- A300139(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun t : ℕ × ℕ × ℕ × ℕ => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = n ∧
      t.2.2.1 ≤ t.2.2.2 ∧ (∃ s : ℤ, 4 * (t.1 : ℤ) - 3 * t.2.1 = s ^ 2) ∧
      (IsSquare (10 * t.1) ∨ IsSquare t.2.1)).card

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ ({0, 7, 8, 13, 22, 23, 24, 31, 44, 56, 71, 79, 88, 109, 120,
        152, 184, 472, 1912, 6008, 9080} : Finset ℕ), n = 16 ^ k * m) ∧
      ∀ n : ℕ, ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        (∃ s : ℤ, 3 * (x : ℤ) - y = 2 * s ^ 2) ∧ (IsSquare (5 * x) ∨ IsSquare y) := by
  sorry

end OMA.S_oeis_a300139
