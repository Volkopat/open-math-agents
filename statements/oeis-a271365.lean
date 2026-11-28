import Mathlib

/-!
# A271365: Number of ordered ways to write n as u^2 + v^3 + x^4 + y^5 + z^6, where u is a positive integer, and v, x, y, z are nonnegative integers.

Source: https://oeis.org/A271365
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271365 (Zhi-Wei Sun):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 8, 15, 16, 23, 24, 56.

Conventions:
* The sequence has offset 1 (data 1, 4, 6, 5, 5, 6, 4, 1, 2, 7, 9, 6, ...). `a n` is the number of
  quintuples (u, v, x, y, z) of natural numbers with u > 0 and n = u^2 + v^3 + x^4 + y^5 + z^6,
  exactly as in the OEIS name.
* Only the first sentence of the conjecture is formalized; the further sentence (Moreover, ...)
  about u^2 + v^3 + x^4 + y^5 is a separate claim.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every n >= 1, the range given in the entry.
* The second part is rendered literally as an only-if, for every n >= 1: a(n) = 1 implies that n
  is one of the listed values.
-/

namespace OMA.S_oeis_a271365

/-- A271365: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ × ℕ | 0 < x.1 ∧
    x.1 ^ 2 + x.2.1 ^ 3 + x.2.2.1 ^ 4 + x.2.2.2.1 ^ 5 + x.2.2.2.2 ^ 6 = n}

/-- The conjecture of Sun recorded in A271365. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    0 < a n ∧ (a n = 1 →
      n ∈ ({1, 8, 15, 16, 23, 24, 56} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a271365
