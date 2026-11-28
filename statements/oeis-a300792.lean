import Mathlib

/-!
# A300792: Number of ways to write n as x^2 + y^2 + z^2 + w^2, where w is a positive integer and x,y,z are nonnegative integers such that x or y or z is a square and 9*x^2 + 16*y^2 + 24*z^2 is also a square.

Source: https://oeis.org/A300792
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300792 (Zhi-Wei Sun, Mar 12 2018), Conjecture 1: a(n)
> 0 for all n > 0, and a(n) = 1 only for n = 16^k*m with k = 0,1,2,... and m = 1, 3, 6, 14, 21,
24, 56, 79, 119, 143, 248, 301, 383, 591, 728, 959, 1223, 1751, 2311, 6119.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 2, 4, 1, 2, 2, 2, 6, 2, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^2 + y^2 + z^2 + w^2, w > 0, such that x or
  y or z is a square and 9*x^2 + 16*y^2 + 24*z^2 is also a square, exactly as in the OEIS name.
* `a square` is the Mathlib predicate `IsSquare` (0 included).
* Only Conjecture 1 is formalized; Conjecture 2 is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a300792

/-- The condition in the name of A300792 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ 0 < w ∧ (IsSquare x ∨ IsSquare y ∨ IsSquare z) ∧
  IsSquare (9 * x ^ 2 + 16 * y ^ 2 + 24 * z ^ 2)

/-- A300792: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300792. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      ∃ k m : ℕ, m ∈ ({1, 3, 6, 14, 21, 24, 56, 79, 119, 143, 248, 301, 383, 591, 728, 959, 1223,
        1751, 2311, 6119} : Finset ℕ) ∧
        n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a300792
