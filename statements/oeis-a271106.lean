import Mathlib

/-!
# A271106: Number of ordered ways to write n as x^6 + 3*y^3 + z^3 + w*(w+1)/2, where x and y are nonnegative integers, and z and w are positive integers.

Source: https://oeis.org/A271106
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271106 (Zhi-Wei Sun):
a(n) > 0 for all n > 1, and a(n) = 1 only for n = 2, 3, 4, 6, 9, 13, 16, 20, 21, 24, 25, 44, 50,
51, 65, 84, 189, 290, 484, 616, 664, 680, 917, 1501, 1639, 3013.

Conventions:
* The sequence has offset 0 (data 0, 0, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with z > 0, w > 0 and n = x^6 + 3*y^3 + z^3 +
  w*(w+1)/2, exactly as in the OEIS name.
* w*(w+1)/2 is natural number division, which is exact since w*(w+1) is even.
* The General Conjecture stated later in the entry is a separate conjecture and is not part of the
  statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every n >= 2, the range given in the entry.
* The second part is rendered literally as an only-if, for every n >= 2: a(n) = 1 implies that n
  is one of the listed values.
-/

namespace OMA.S_oeis_a271106

/-- A271106: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
    x.1 ^ 6 + 3 * x.2.1 ^ 3 + x.2.2.1 ^ 3 + x.2.2.2 * (x.2.2.2 + 1) / 2 = n}

/-- The conjecture of Sun recorded in A271106. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    0 < a n ∧ (a n = 1 →
      n ∈ ({2, 3, 4, 6, 9, 13, 16, 20, 21, 24, 25, 44, 50, 51, 65, 84, 189, 290, 484, 616, 664,
      680, 917, 1501, 1639, 3013} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a271106
