import Mathlib

/-!
# A275301: Number of ordered ways to write n as x^2 + y^2 + z^2 + 2*w^2 with x + 2*y a cube, where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A275301
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275301 (Zhi-Wei Sun):
(i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 5, 6, 7, 8, 11, 14, 15, 30, 78,
90, 93, 106, 111, 117, 125, 223, 335.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 2, 1, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x + 2*y a cube and n = x^2 + y^2 + z^2 + 2*w^2,
  exactly as in the OEIS name.
* A cube means the cube c^3 of a natural number c (0 included).
* Only part (i) of the conjecture is formalized; part (ii) concerns a different form.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a275301

/-- A275301: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | (∃ c : ℕ, x.1 + 2 * x.2.1 = c ^ 3) ∧
    x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + 2 * x.2.2.2 ^ 2 = n}

/-- The conjecture of Sun recorded in A275301. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 5, 6, 7, 8, 11, 14, 15, 30, 78, 90, 93, 106, 111, 117, 125, 223, 335} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275301
