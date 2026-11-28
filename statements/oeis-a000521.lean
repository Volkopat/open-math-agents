import Mathlib

/-!
# OEIS A000521: coefficients of the modular invariant j

Source: https://oeis.org/A000521
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` (`n ≥ -1`) is the coefficient of `q^n` in `j(τ) = 1/q + 744 + 196884 q + ⋯`,
`q = e^(2πiτ)`. Conjecture (OEIS entry): `a(n)` for `n ≥ 0` is never a perfect power, and
`(a(n+1)/a(n))_{n ≥ 0}` is strictly decreasing.

Conventions:
* `j = E₄³ / Δ` with `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ` and `Δ = q ∏_{k ≥ 1} (1 - q^k)^24`. So
  `q j = E₄³ · D⁻¹` in `ℤ⟦q⟧` with `D = ∏_{k ≥ 1} (1 - q^k)^24`, which has constant term `1`;
  the coefficient of `qⁿ` in `D` only involves the factors with `k ≤ n`. Then `a(n)` is the
  coefficient of `q^(n+1)` in `q j`; below `a n` is indexed by `n : ℕ` meaning `n ≥ 0`.
* A perfect power is `m ^ k` with `m : ℤ` and `k ≥ 2`.
-/

namespace OMA.S_oeis_a000521

open PowerSeries

/-- `D = ∏_{k ≥ 1} (1 - q^k)^24`, coefficientwise via finite truncations. -/
noncomputable def D : PowerSeries ℤ :=
  PowerSeries.mk fun n => coeff n (∏ k ∈ Finset.range n, (1 - X ^ (k + 1) : PowerSeries ℤ) ^ 24)

/-- The Eisenstein series `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`. -/
noncomputable def E4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

/-- `q j(q) = E₄³ / D`. -/
noncomputable def qj : PowerSeries ℤ := E4 ^ 3 * invOfUnit D 1

/-- `a n` = coefficient of `qⁿ` in `j`, for `n ≥ 0`. -/
noncomputable def a (n : ℕ) : ℤ := coeff (n + 1) qj

/-- No `a n` (`n ≥ 0`) is a perfect power, and `a (n+1) / a n` is strictly decreasing. -/
theorem main :
    (∀ n : ℕ, ¬ ∃ (m : ℤ) (k : ℕ), 2 ≤ k ∧ a n = m ^ k) ∧
    (∀ n : ℕ, (a (n + 2) : ℚ) / a (n + 1) < (a (n + 1) : ℚ) / a n) := by
  sorry

end OMA.S_oeis_a000521
