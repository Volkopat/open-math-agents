import Mathlib

/-!
# A299794: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x >= y >= 0 <= z <= w such that x or 2*y is a power of 4 (including 4^0 = 1) and x + 15*y is also a power of 4.

Source: https://oeis.org/A299794
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A299794 (Zhi-Wei Sun, Mar 04 2018), Conjecture 1, first
sentence: a(n) > 0 for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n^2 = x^2 + y^2 + z^2 + w^2, x >= y >= 0 <= z <=
  w, such that x or 2*y is a power of 4 and x + 15*y is also a power of 4, exactly as in the OEIS
  name.
* A power of 4 is 4^k with k = 0, 1, 2, ... (4^0 = 1 included).
* The chain x >= y >= 0 <= z <= w is the two conditions y <= x and z <= w on natural numbers.
* Only the first sentence of Conjecture 1 is formalized; its `Also` sentence and Conjecture 2 are
  different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a299794

/-- The condition in the name of A299794 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧ y ≤ x ∧ z ≤ w ∧
  ((∃ k : ℕ, x = 4 ^ k) ∨ (∃ k : ℕ, 2 * y = 4 ^ k)) ∧ ∃ k : ℕ, x + 15 * y = 4 ^ k

/-- A299794: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A299794. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a299794
