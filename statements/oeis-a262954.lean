import Mathlib

/-!
# A262954: Number of ordered pairs (x,y) with x >= 0 and y > 0 such that n - x^4 - y*(y+1)/2 has the form z^2 or 8*z^2.

Source: https://oeis.org/A262954
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262954 (Zhi-Wei Sun, Oct 05 2015), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 1, 9, 13, 89, 449, 524, 1049, 2164, 14969, 51334.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 2, 2, 3, 2, 1, 4, 5, 3, ...). `a n` is the number of
  pairs (x, y) of natural numbers with y > 0 such that n - x^4 - y*(y+1)/2 has the form z^2 or
  8*z^2, exactly as in the OEIS name.
* The condition is written without subtraction as an equation for n, with z a natural number (z
  and -z give the same value). The division by 2 is exact.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a262954

/-- The condition in the name of A262954 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) : Prop :=
  0 < y ∧ ∃ z : ℕ, x ^ 4 + y * (y + 1) / 2 + z ^ 2 = n ∨ x ^ 4 + y * (y + 1) / 2 + 8 * z ^ 2 = n

/-- A262954: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A262954. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 9, 13, 89, 449, 524, 1049, 2164, 14969, 51334} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a262954
