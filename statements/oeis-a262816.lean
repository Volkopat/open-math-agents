import Mathlib

/-!
# A262816: Number of ordered ways to write n as x^3 + y^2 + z*(3*z-1)/2, where x and y are nonnegative integers, and z is a nonzero integer.

Source: https://oeis.org/A262816
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262816 (Zhi-Wei Sun):
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 4, 216.

Conventions:
* The sequence has offset 1 (data 1, 3, 3, 1, 2, 4, 3, 2, 3, 4, 4, 3, ...). `a n` is the number of
  triples (x, y, z) with x, y natural numbers and z a nonzero integer such that n = x^3 + y^2 +
  z*(3*z-1)/2, exactly as in the OEIS name.
* Integer variables range over `ℤ` and the equation is stated in `ℤ` with n cast; the division by
  2 is integer division, which is exact here because the product is always even (and nonnegative).
* Only part (i) of the conjecture is formalized; part (ii) concerns a different polynomial.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every n >= 1, the range given in the entry.
* The second part is rendered literally as an only-if, for every n >= 1: a(n) = 1 implies that n
  is one of the listed values.
-/

namespace OMA.S_oeis_a262816

/-- A262816: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℤ | x.2.2 ≠ 0 ∧
    (x.1 : ℤ) ^ 3 + (x.2.1 : ℤ) ^ 2 + x.2.2 * (3 * x.2.2 - 1) / 2 = (n : ℤ)}

/-- The conjecture of Sun recorded in A262816. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < a n ∧ (a n = 1 →
      n ∈ ({1, 4, 216} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a262816
