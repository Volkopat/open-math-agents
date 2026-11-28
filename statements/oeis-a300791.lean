import Mathlib

/-!
# A300791: Number of ways to write n as x^2 + y^2 + z^2 + w^2, where w is a positive integer and x,y,z are nonnegative integers for which x or y or z is a square and (12*x)^2 + (15*y)^2 + (20*z)^2 is also a square.

Source: https://oeis.org/A300791
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300791 (Zhi-Wei Sun, Mar 12 2018): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 16^k*m with k = 0,1,2,... and m = 1, 3, 4, 6, 7, 21, 23, 24, 39,
47, 86, 95, 344, 651, 764.

Conventions:
* The sequence has offset 1 (data 1, 3, 1, 1, 6, 1, 1, 3, 2, 8, 2, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^2 + y^2 + z^2 + w^2, w > 0, such that x or
  y or z is a square and (12*x)^2 + (15*y)^2 + (20*z)^2 is also a square, exactly as in the OEIS
  name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a300791

/-- The condition in the name of A300791 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ 0 < w ∧ (IsSquare x ∨ IsSquare y ∨ IsSquare z) ∧
  IsSquare ((12 * x) ^ 2 + (15 * y) ^ 2 + (20 * z) ^ 2)

/-- A300791: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300791. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      ∃ k m : ℕ, m ∈ ({1, 3, 4, 6, 7, 21, 23, 24, 39, 47, 86, 95, 344, 651, 764} : Finset ℕ) ∧
        n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a300791
