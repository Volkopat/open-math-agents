import Mathlib

/-!
# A275297: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^3 with x + 2*y a square, where x,y,z,w are nonnegative integers with z >= w.

Source: https://oeis.org/A275297
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275297 (Zhi-Wei Sun):
a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 3, 7, 8, 11, 12, 15, 23, 24, 32, 39,
47, 71, 103, 120, 136, 159, 176, 183, 218, 359, 463.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 3, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with z >= w, x + 2*y a square and n = x^2 + y^2 + z^2
  + w^3, exactly as in the OEIS name.
* A square means the square of an integer (0 included), rendered as `IsSquare` on natural numbers.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a275297

/-- A275297: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | x.2.2.2 ≤ x.2.2.1 ∧ IsSquare (x.1 + 2 * x.2.1) ∧
    x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 3 = n}

/-- The conjecture of Sun recorded in A275297. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 3, 7, 8, 11, 12, 15, 23, 24, 32, 39, 47, 71, 103, 120, 136, 159, 176, 183, 218,
      359, 463} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275297
