import Mathlib

/-!
# OEIS A137560: iterates of `z² + c` tend to the Catalan numbers

Source: https://oeis.org/A137560
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

With `f(z) = z² + c`, row `n` lists the coefficients of the `n`-fold composition `f(f(⋯f(0)⋯))` in
rising powers of `c`. Conjecture (OEIS entry): these polynomials tend to the Catalan numbers.

Conventions:
* `Pₙ(c) = f^[n](0)` in `ℤ[c]`: `P₀ = 0`, `P_{n+1} = Pₙ² + c`. 'Tend to the Catalan numbers' means
  coefficientwise stabilisation: for every `k ≥ 1`, the coefficient of `c^k` in `Pₙ` equals
  `C_{k-1}` (Catalan) for all large `n` (`P₁ = c, P₂ = c + c², P₃ = c + c² + 2c³ + c⁴, …`).
-/

namespace OMA.S_oeis_a137560

open Polynomial

/-- `Pₙ = f^[n](0)` with `f(z) = z² + c`. -/
noncomputable def P : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => P n ^ 2 + X

/-- The coefficients of `Pₙ` stabilise to the Catalan numbers. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, (P n).coeff k = (catalan (k - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a137560
