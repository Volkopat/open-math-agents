import Mathlib

/-!
# A275648: Number of ordered ways to write n as x^2*(1+y^2+z^2)+w^2, where x is a positive integer and y,z,w are nonnegative integers with y <= z <= w.

Source: https://oeis.org/A275648
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275648 (Zhi-Wei Sun):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 3, 6, 7, 11, 14, 15, 23, 38, 47, 71, 77, 143,
152, 191, 608, 2^(2k+1) (k = 0,1,2,...).

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x > 0, y <= z <= w and n = x^2*(1+y^2+z^2) +
  w^2, exactly as in the OEIS name.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every n >= 1, the range given in the entry.
* The second part is rendered literally as an only-if, for every n >= 1: a(n) = 1 implies that n
  is one of the listed values or a member of the listed infinite family.
-/

namespace OMA.S_oeis_a275648

/-- A275648: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | 0 < x.1 ∧ x.2.1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧
    x.1 ^ 2 * (1 + x.2.1 ^ 2 + x.2.2.1 ^ 2) + x.2.2.2 ^ 2 = n}

/-- The conjecture of Sun recorded in A275648. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < a n ∧ (a n = 1 →
      n ∈ ({1, 3, 6, 7, 11, 14, 15, 23, 38, 47, 71, 77, 143, 152, 191, 608} : Finset ℕ) ∨
      ∃ k : ℕ, n = 2 ^ (2 * k + 1)) := by
  sorry

end OMA.S_oeis_a275648
