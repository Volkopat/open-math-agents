import Mathlib

/-!
# Mathar's recurrence for ternary strings in OEIS A385252

Enrique Navarrete counts ternary words of length 2n having at least one zero
and strictly fewer zeros than nonzero symbols. R. J. Mathar conjectured the
recurrence on 31 July 2025. The entry does not specify its starting index.
The first index with all six terms defined is 5, where the residual is −6912.
The first possible start for the homogeneous recurrence is therefore 6.

Source: https://oeis.org/A385252
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a385252

/-- Number of zero symbols in a ternary word. -/
def zeros {m : ℕ} (w : Fin m → Fin 3) : ℕ :=
  ∑ i, if w i = 0 then 1 else 0

/-- Sum of the indicator of the defining condition over all words of length 2n. -/
def a (n : ℕ) : ℤ :=
  ∑ w : Fin (2 * n) → Fin 3, if 0 < zeros w ∧ zeros w < n then 1 else 0

/-- Left-hand side of the proposed order-five recurrence, evaluated at n. -/
def residual (n : ℕ) : ℤ :=
  (n : ℤ) * a n + (36 - 37 * (n : ℤ)) * a (n - 1) +
  4 * (131 * (n : ℤ) - 245) * a (n - 2) +
  16 * (605 - 221 * (n : ℤ)) * a (n - 3) +
  192 * (59 * (n : ℤ) - 213) * a (n - 4) +
  6912 * (9 - 2 * (n : ℤ)) * a (n - 5)

theorem main : ∀ n : ℕ, 6 ≤ n → residual n = 0 := by
  sorry

end OMA.S_oeis_a385252
