import Mathlib

/-!
# A270533: Number of ordered ways to write n = x^4 + x^3 + y^2 + z*(3z-1)/2, where x and y are nonnegative integers, and z is an integer.

Source: https://oeis.org/A270533
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270533 (Zhi-Wei Sun):
(i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 20, 22, 70, 87, 167, 252, 388,
562, 636, 658, 873, 2598, 14979, 18892, 20824.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 4, ...). `a n` is the number of
  triples (x, y, z) with x, y natural numbers and z an integer such that n = x^4 + x^3 + y^2 +
  z*(3*z-1)/2, exactly as in the OEIS name.
* Integer variables range over `ℤ` and the equation is stated in `ℤ` with n cast; the division by
  2 is integer division, which is exact here because the product is always even (and nonnegative).
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) concern other polynomials.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a270533

/-- A270533: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℤ |
    (x.1 : ℤ) ^ 4 + (x.1 : ℤ) ^ 3 + (x.2.1 : ℤ) ^ 2 + x.2.2 * (3 * x.2.2 - 1) / 2 = (n : ℤ)}

/-- The conjecture of Sun recorded in A270533. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 20, 22, 70, 87, 167, 252, 388, 562, 636, 658, 873, 2598, 14979, 18892, 20824} :
      Finset ℕ)) := by
  sorry

end OMA.S_oeis_a270533
