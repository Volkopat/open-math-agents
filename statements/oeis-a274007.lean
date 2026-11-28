import Mathlib

/-!
# A274007: Number of ordered ways to write n as x^5 + 2*y^5 + z*(3*z-1)/2 + w*(3*w+1)/2, where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A274007
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A274007 (Zhi-Wei Sun):
(i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 11, 57, 198, 229, 232, 1168,
2624.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 3, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^5 + 2*y^5 + z*(3*z-1)/2 + w*(3*w+1)/2,
  exactly as in the OEIS name.
* The divisions by 2 are natural number divisions and are exact since z*(3*z-1) and w*(3*w+1) are
  even; the natural subtraction 3*z - 1 only truncates at z = 0, where the product is 0 anyway.
* Only part (i) of the conjecture is formalized; parts (ii) to (v) concern other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a274007

/-- A274007: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | x.1 ^ 5 + 2 * x.2.1 ^ 5 + x.2.2.1 * (3 * x.2.2.1 - 1) / 2 +
    x.2.2.2 * (3 * x.2.2.2 + 1) / 2 = n}

/-- The conjecture of Sun recorded in A274007. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a274007
