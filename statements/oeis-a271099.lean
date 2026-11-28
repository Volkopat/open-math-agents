import Mathlib

/-!
# A271099: Number of ordered ways to write n as u^3 + v^3 + 2*x^3 + 2*y^3 + 3*z^3, where u, v, x, y and z are nonnegative integers with u <= v and x <= y.

Source: https://oeis.org/A271099
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271099 (Zhi-Wei Sun):
(i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 1, 10, 14, 15, 17, 22, 38, 39,
45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534.

Conventions:
* The sequence has offset 0 (data 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 2, ...). `a n` is the number of
  quintuples (u, v, x, y, z) of natural numbers with u <= v, x <= y and n = u^3 + v^3 + 2*x^3 +
  2*y^3 + 3*z^3, exactly as in the OEIS name.
* Only part (i) of the conjecture is formalized; parts (ii) and (iii) concern other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a271099

/-- A271099: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ × ℕ | x.1 ≤ x.2.1 ∧ x.2.2.1 ≤ x.2.2.2.1 ∧
    x.1 ^ 3 + x.2.1 ^ 3 + 2 * x.2.2.1 ^ 3 + 2 * x.2.2.2.1 ^ 3 + 3 * x.2.2.2.2 ^ 3 = n}

/-- The conjecture of Sun recorded in A271099. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} :
      Finset ℕ)) := by
  sorry

end OMA.S_oeis_a271099
