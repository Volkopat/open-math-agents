import Mathlib

/-!
# OEIS A005043 (Riordan numbers): `a(n) = A002426(n) - A005717(n)`

Source: https://oeis.org/A005043
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (in the OEIS entry): `a(n) = A002426(n) - A005717(n)` for `n > 0`.

Sequences.
* A005043, Riordan numbers: `a(0) = 1`, `a(1) = 0`,
  `(n + 1) a(n) = (n - 1) (2 a(n-1) + 3 a(n-2))` (the recurrence in the entry); computed in `ℚ`.
* A002426, central trinomial coefficients: coefficient of `x^n` in `(1 + x + x²)^n`.
* A005717: coefficient of `x^(n-1)` in `(1 + x + x²)^n` (next-to-central column of the
  trinomial triangle).
-/

namespace OMA.S_oeis_a005043

open Polynomial

/-- Riordan numbers, via the recurrence. -/
noncomputable def riordan : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | (n + 2) => ((n + 1 : ℚ) / (n + 3)) * (2 * riordan (n + 1) + 3 * riordan n)

/-- Central trinomial coefficient (A002426). -/
noncomputable def trinomialCentral (n : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff n

/-- Next-to-central trinomial coefficient (A005717). -/
noncomputable def trinomialNext (n : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff (n - 1)

/-- The conjecture. -/
theorem main :
    ∀ n : ℕ, 0 < n → riordan n = ((trinomialCentral n - trinomialNext n : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a005043
