import Mathlib

/-!
# A228256: Number of third differences of arrays of length n+3 of numbers in 0..4.

Source: https://oeis.org/A228256
Credit: @ceejcake

Formalizes Colin Barker's closed-form conjecture (Sep 10 2018) for OEIS A228256 (offset 1):
`a(n) = 5^(3 + n) - 4^(3 + n)` for all `n > 6`.
(The same comment also conjectures a rational g.f. with denominator `(1 - 4x)(1 - 5x)`; given the
listed initial terms, that g.f. is equivalent to this closed form, which is the part stated here.)

Conventions:
* An array of length `n + 3` with entries in `0..4` is modeled as `x : Fin (n + 3) → Fin 5`.
* Its third difference array `thirdDiff n x : Fin n → ℤ` has `i`-th entry
  `(x (i + 3) : ℤ) - 3 * (x (i + 2) : ℤ) + 3 * (x (i + 1) : ℤ) - (x i : ℤ)` (computed in `ℤ`).
* `a n` is the number of distinct third difference arrays `(Finset.univ.image (thirdDiff n)).card`.
* Initial values match OEIS A228256 DATA:
  `a(1) = 33`, `a(2) = 565`, `a(3) = 6419`, and `a(7) = 8717049 = 5^10 - 4^10`.
-/

namespace OMA.S_oeis_a228256

/-- The third difference array of `x : Fin (n + 3) → Fin 5`, of length `n` with entries in `ℤ`. -/
def thirdDiff (n : ℕ) (x : Fin (n + 3) → Fin 5) : Fin n → ℤ :=
  fun i => (x ⟨i.1 + 3, by omega⟩ : ℤ) - 3 * (x ⟨i.1 + 2, by omega⟩ : ℤ) +
    3 * (x ⟨i.1 + 1, by omega⟩ : ℤ) - (x ⟨i.1, by omega⟩ : ℤ)

/-- OEIS A228256 (offset 1): number of distinct third differences of arrays of length `n + 3`
of numbers in `{0, 1, 2, 3, 4}`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.image (thirdDiff n)).card

/-- Conjecture (Colin Barker, OEIS A228256): `a(n) = 5^(3 + n) - 4^(3 + n)` for all `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n → a n = 5 ^ (3 + n) - 4 ^ (3 + n) := by
  sorry

end OMA.S_oeis_a228256
