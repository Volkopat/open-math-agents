import Mathlib

/-!
# A228214: Number of second differences of arrays of length n + 2 of numbers in 0..4.

Source: https://oeis.org/A228214
Credit: @ceejcake

Formalizes Colin Barker's closed-form conjecture (Sep 10 2018) for OEIS A228214 (offset 1):
`a(n) = 5^(2 + n) - 4^(2 + n)` for all `n > 7`.
(The same comment also conjectures a rational g.f. with denominator `(1 - 4x)(1 - 5x)`; given the
listed initial terms, that g.f. is equivalent to this closed form, which is the part stated here.)

Conventions:
* An array of length `n + 2` with entries in `0..4` is modeled as `x : Fin (n + 2) → Fin 5`.
* Its second difference array `secondDiff n x : Fin n → ℤ` has `i`-th entry
  `(x (i + 2) : ℤ) - 2 * (x (i + 1) : ℤ) + (x i : ℤ)` (computed in `ℤ`).
* `a n` is the number of distinct second difference arrays `(Finset.univ.image (secondDiff n)).card`.
* Initial values match OEIS A228214 DATA:
  `a(1) = 17`, `a(2) = 177`, `a(3) = 1429`, and `a(8) = 8717049 = 5^10 - 4^10`.
-/

namespace OMA.S_oeis_a228214

/-- The second difference array of `x : Fin (n + 2) → Fin 5`, of length `n` with entries in `ℤ`. -/
def secondDiff (n : ℕ) (x : Fin (n + 2) → Fin 5) : Fin n → ℤ :=
  fun i => (x ⟨i.1 + 2, by omega⟩ : ℤ) - 2 * (x ⟨i.1 + 1, by omega⟩ : ℤ) + (x ⟨i.1, by omega⟩ : ℤ)

/-- OEIS A228214 (offset 1): number of distinct second differences of arrays of length `n + 2`
of numbers in `{0, 1, 2, 3, 4}`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.image (secondDiff n)).card

/-- Conjecture (Colin Barker, OEIS A228214): `a(n) = 5^(2 + n) - 4^(2 + n)` for all `n > 7`. -/
theorem main : ∀ n : ℕ, 7 < n → a n = 5 ^ (2 + n) - 4 ^ (2 + n) := by
  sorry

end OMA.S_oeis_a228214
