import Mathlib

/-!
# A262827: Number of ordered ways to write n as w^2 + x^3 + y^4 + 2*z^4, where w, x, y and z are nonnegative integers.

Source: https://oeis.org/A262827
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262827 (Zhi-Wei Sun):
a(n) > 0 for all n >= 0. Also, a(n) = 1 only for the following 41 values of n: 0, 14, 15, 21, 22,
23, 62, 71, 78, 87, 136, 216, 405, 437, 448, 477, 535, 583, 591, 623, 671, 696, 885, 950, 1046,
1135, 1206, 1208, 1248, 1317, 2288, 2383, 2543, 3167, 3717, 3974, 6847, 7918, 8328, 9096, 21935.

Conventions:
* The sequence has offset 0 (data 1, 3, 4, 4, 4, 3, 2, 2, 2, 3, 4, 4, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = w^2 + x^3 + y^4 + 2*z^4, exactly as in the
  OEIS name.
* The later comment of the entry about 8 further polynomials is a separate conjecture and is not
  part of the statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The positivity part is stated for every natural number n, the range given in the entry.
* The second part is rendered literally as an only-if, for every natural number n: a(n) = 1
  implies that n is one of the listed values.
-/

namespace OMA.S_oeis_a262827

/-- A262827: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ × ℕ | x.1 ^ 2 + x.2.1 ^ 3 + x.2.2.1 ^ 4 + 2 * x.2.2.2 ^ 4 = n}

/-- The conjecture of Sun recorded in A262827. -/
theorem main : ∀ n : ℕ,
    0 < a n ∧ (a n = 1 →
      n ∈ ({0, 14, 15, 21, 22, 23, 62, 71, 78, 87, 136, 216, 405, 437, 448, 477, 535, 583, 591,
      623, 671, 696, 885, 950, 1046, 1135, 1206, 1208, 1248, 1317, 2288, 2383, 2543, 3167,
      3717, 3974, 6847, 7918, 8328, 9096, 21935} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a262827
