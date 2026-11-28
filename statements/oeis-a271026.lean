import Mathlib

/-!
# A271026: Number of ordered ways to write n as x^7 + y^4 + z^3 + w*(3w+1)/2, where x, y, z are nonnegative integers, and w is an integer.

Source: https://oeis.org/A271026
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271026 (Zhi-Wei Sun):
(i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 47, 61, 62, 112, 175, 448, 573,
714, 1073, 1175, 1839, 2167, 8043, 13844.

Conventions:
* The sequence has offset 0 (data 1, 4, 7, 7, 4, 2, 3, 4, 5, 6, 5, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) with x, y, z natural numbers and w an integer such that n = x^7 + y^4 +
  z^3 + w*(3*w+1)/2, exactly as in the OEIS name.
* Integer variables range over `ℤ` and the equation is stated in `ℤ` with n cast; the division by
  2 is integer division, which is exact here because the product is always even (and nonnegative).
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) concern other polynomials.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a271026

/-- A271026: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℤ | (x.1 : ℤ) ^ 7 + (x.2.1 : ℤ) ^ 4 + (x.2.2.1 : ℤ) ^ 3 +
    x.2.2.2 * (3 * x.2.2.2 + 1) / 2 = (n : ℤ)}

/-- The conjecture of Sun recorded in A271026. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844} : Finset
      ℕ)) := by
  sorry

end OMA.S_oeis_a271026
