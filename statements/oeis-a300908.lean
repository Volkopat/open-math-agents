import Mathlib

/-!
# A300908: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with (3*x)^2 + (4*y)^2 + (12*z)^2 a square , where w is a positive integer and x,y,z are nonnegative integers such that z or 2*z or 3*z is a square.

Source: https://oeis.org/A300908
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300908 (Zhi-Wei Sun, Mar 15 2018), Conjecture 1, first
sentence: a(n) > 0 for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 3, 1, 2, 6, 1, 2, 3, 2, 7, 2, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^2 + y^2 + z^2 + w^2, w > 0, (3*x)^2 +
  (4*y)^2 + (12*z)^2 a square, and z or 2*z or 3*z a square, exactly as in the OEIS name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* Only the first sentence of Conjecture 1 is formalized; its `Moreover` sentence and Conjectures 2
  and 3 are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a300908

/-- The condition in the name of A300908 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ 0 < w ∧ IsSquare ((3 * x) ^ 2 + (4 * y) ^ 2 + (12 * z) ^ 2) ∧
  (IsSquare z ∨ IsSquare (2 * z) ∨ IsSquare (3 * z))

/-- A300908: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300908. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a300908
