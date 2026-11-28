import Mathlib

/-!
# A008749: Expansion of (1+x^6)/((1-x)*(1-x^2)*(1-x^3))

Source: https://oeis.org/A008749
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (OEIS entry):
Let `a(n)` be the expansion of `(1 + x^6) / ((1 - x) * (1 - x^2) * (1 - x^3))`.
Let `b(0) = 0`, and for `n ≥ 1`, `b(n) = 2 * ⌊(n - 1) / 6⌋ + 1 + (2 if n + 1 ≡ 0 (mod 6) else 0)`.
Then `a(0) = 1` and `a(n) = a(n - 1) + b(n - 1)` for all `n ≥ 1`.

Conventions:
- `a(n)` is characterized as the coefficient of `X^n` in the formal power series
  `f : PowerSeries ℤ` satisfying `((1 - X) * (1 - X^2) * (1 - X^3)) * f = 1 + X^6`.
-/

namespace OMA.S_oeis_a008749

def bSeq : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (n / 6) + 1 + if (n + 2) % 6 = 0 then 2 else 0

theorem main :
    ∀ f : PowerSeries ℤ,
      ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ 3)) * f =
        1 + PowerSeries.X ^ 6 →
      PowerSeries.coeff 0 f = 1 ∧
        ∀ n : ℕ, PowerSeries.coeff (n + 1) f = PowerSeries.coeff n f + (bSeq n : ℤ) := by
  sorry

end OMA.S_oeis_a008749
