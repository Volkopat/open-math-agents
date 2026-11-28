import Mathlib

/-!
# A228212: Number of second differences of arrays of length n + 2 of numbers in 0..2.

Source: https://oeis.org/A228212
Credit: @ceejcake

Formalizes Colin Barker's closed-form conjecture (Sep 09 2018) for OEIS A228212 (offset 1):
`a(n) = 3^(2 + n) - 2^(2 + n)` for all `n > 3`.

Conventions:
* An array of length `n + 2` with entries in `0..2` is modeled as `x : Fin (n + 2) → Fin 3`.
* Its second difference array `secondDiff n x : Fin n → ℤ` has `i`-th entry
  `(x i : ℤ) - 2 * (x (i + 1) : ℤ) + (x (i + 2) : ℤ)` (computed in `ℤ`).
* `a n` is the number of distinct second difference arrays `(Finset.univ.image (secondDiff n)).card`.
* Initial values match OEIS A228212 DATA:
  `a(1) = 9`, `a(2) = 49`, `a(3) = 199`, `a(4) = 665 = 3^6 - 2^6`, `a(5) = 2059 = 3^7 - 2^7`.
-/

namespace OMA.S_oeis_a228212

/-- The second difference array of `x : Fin (n + 2) → Fin 3`, of length `n` with entries in `ℤ`. -/
def secondDiff (n : ℕ) (x : Fin (n + 2) → Fin 3) : Fin n → ℤ :=
  fun i => (x ⟨i.1, by omega⟩ : ℤ) - 2 * (x ⟨i.1 + 1, by omega⟩ : ℤ) + (x ⟨i.1 + 2, by omega⟩ : ℤ)

/-- OEIS A228212 (offset 1): number of distinct second differences of arrays of length `n + 2`
of numbers in `{0, 1, 2}`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.image (secondDiff n)).card

/-- Conjecture (Colin Barker, OEIS A228212): `a(n) = 3^(2 + n) - 2^(2 + n)` for all `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → a n = 3 ^ (2 + n) - 2 ^ (2 + n) := by
  sorry

end OMA.S_oeis_a228212
