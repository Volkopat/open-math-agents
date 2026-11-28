import Mathlib

/-!
# A270566: Number of ordered ways to write n as x^4 + y*(3y+1)/2 + z*(7z+1)/2, where x, y and z are integers with x nonnegative.

Source: https://oeis.org/A270566
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270566 (Zhi-Wei Sun):
a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 24, 47, 63, 78, 79, 143, 153, 325,
494, 949, 1079, 3328, 4335, 5609, 7949, 7967, 8888, 9665.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 2, 3, 5, 4, 2, 2, 2, 2, 2, ...). `a n` is the number of
  triples (x, y, z) with x a natural number and y, z integers such that n = x^4 + y*(3*y+1)/2 +
  z*(7*z+1)/2, exactly as in the OEIS name.
* Integer variables range over `ℤ` and the equation is stated in `ℤ` with n cast; the division by
  2 is integer division, which is exact here because the product is always even (and nonnegative).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a270566

/-- A270566: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℤ × ℤ |
    (x.1 : ℤ) ^ 4 + x.2.1 * (3 * x.2.1 + 1) / 2 + x.2.2 * (7 * x.2.2 + 1) / 2 = (n : ℤ)}

/-- The conjecture of Sun recorded in A270566. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 24, 47, 63, 78, 79, 143, 153, 325, 494, 949, 1079, 3328, 4335, 5609, 7949, 7967,
      8888, 9665} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a270566
