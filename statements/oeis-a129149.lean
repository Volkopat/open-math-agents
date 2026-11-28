import Mathlib

/-!
# A129149: Permutations with exactly 7 fixed points.

Source: https://oeis.org/A129149
Credit: @ricnov

`a n` is the number of permutations of an `n`-element set that have exactly seven fixed points
(the column `k = 7` of the rencontres numbers, A008290). The entry has offset 7.

R. J. Mathar's conjecture of Nov 02 2015, as written in the entry:
`(-n+7)*a(n) + n*(n-8)*a(n-1) + n*(n-1)*a(n-2) = 0`.

Conventions: the recurrence mentions `a(n-2)`, so with offset 7 it is stated for `n ≥ 9`; it is
stated in the integers because its first coefficient is negative.
-/

namespace OMA.S_oeis_a129149

/-- The number of permutations of `Fin n` with exactly seven fixed points. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    (Finset.univ.filter fun i : Fin n => σ i = i).card = 7).card

/-- Mathar's conjectured recurrence for the terms of A129149. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    (-(n : ℤ) + 7) * (a n : ℤ) + (n : ℤ) * ((n : ℤ) - 8) * (a (n - 1) : ℤ)
      + (n : ℤ) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a129149
