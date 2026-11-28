import Mathlib

/-!
# A228255: Number of third differences of arrays of length n+3 of numbers in 0..3.

Source: https://oeis.org/A228255
Credit: @ceejcake

Formalizes Colin Barker's closed-form conjecture (Sep 10 2018) for OEIS A228255 (offset 1):
`a(n) = 4^(3 + n) - 3^(3 + n)` for all `n > 5`.
(The same comment also conjectures a rational g.f. with denominator `(1 - 3x)(1 - 4x)`; given the
listed initial terms, that g.f. is equivalent to this closed form, which is the part stated here.)

Conventions:
* An array of length `n + 3` with entries in `0..3` is modeled as `x : Fin (n + 3) → Fin 4`.
* Its third difference array `thirdDiff n x : Fin n → ℤ` has `i`-th entry
  `(x (i + 3) : ℤ) - 3 * (x (i + 2) : ℤ) + 3 * (x (i + 1) : ℤ) - (x i : ℤ)` (computed in `ℤ`).
* `a n` is the number of distinct third difference arrays `(Finset.univ.image (thirdDiff n)).card`.
* Initial values match OEIS A228255 DATA:
  `a(1) = 25`, `a(2) = 319`, `a(3) = 2511`, and `a(6) = 242461 = 4^9 - 3^9`.
-/

namespace OMA.S_oeis_a228255

/-- The third difference array of `x : Fin (n + 3) → Fin 4`, of length `n` with entries in `ℤ`. -/
def thirdDiff (n : ℕ) (x : Fin (n + 3) → Fin 4) : Fin n → ℤ :=
  fun i => (x ⟨i.1 + 3, by omega⟩ : ℤ) - 3 * (x ⟨i.1 + 2, by omega⟩ : ℤ) +
    3 * (x ⟨i.1 + 1, by omega⟩ : ℤ) - (x ⟨i.1, by omega⟩ : ℤ)

/-- OEIS A228255 (offset 1): number of distinct third differences of arrays of length `n + 3`
of numbers in `{0, 1, 2, 3}`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.image (thirdDiff n)).card

/-- Conjecture (Colin Barker, OEIS A228255): `a(n) = 4^(3 + n) - 3^(3 + n)` for all `n > 5`. -/
theorem main : ∀ n : ℕ, 5 < n → a n = 4 ^ (3 + n) - 3 ^ (3 + n) := by
  sorry

end OMA.S_oeis_a228255
