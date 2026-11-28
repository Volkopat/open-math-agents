import Mathlib

/-!
# A270469: Number of ordered ways to write n = x^3 + y*(y+1) + z*(3*z+2), where x and y are nonnegative integers and z is a nonzero integer.

Source: https://oeis.org/A270469
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A270469 (Zhi-Wei Sun):
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 3, 4, 5, 6, 10, 12, 20, 27, 56, 101.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, ...). `a n` is the number of
  triples (x, y, z) with x, y natural numbers and z a nonzero integer such that n = x^3 + y*(y+1)
  + z*(3*z+2), exactly as in the OEIS name.
* The integer variable z ranges over `ℤ` and the equation is stated in `ℤ` with n cast.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) concern other polynomials.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every n >= 1, the range given in the entry.
* The second part is rendered literally as an only-if, for every n >= 1: a(n) = 1 implies that n
  is one of the listed values.
-/

namespace OMA.S_oeis_a270469

/-- A270469: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℤ | x.2.2 ≠ 0 ∧
    (x.1 : ℤ) ^ 3 + (x.2.1 : ℤ) * ((x.2.1 : ℤ) + 1) + x.2.2 * (3 * x.2.2 + 2) = (n : ℤ)}

/-- The conjecture of Sun recorded in A270469. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < a n ∧ (a n = 1 →
      n ∈ ({1, 2, 3, 4, 5, 6, 10, 12, 20, 27, 56, 101} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a270469
