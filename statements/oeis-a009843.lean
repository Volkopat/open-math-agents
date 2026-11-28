import Mathlib

/-!
# OEIS A009843: expansion of the e.g.f. `x / cos(x)` (odd powers only)

Source: https://oeis.org/A009843
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the coefficient of `x^(2n+1) / (2n+1)!` in `x / cos(x)`, offset 0
(`1, 3, 25, 427, 12465, 555731, …`).

The entry (Peter Bala, Mar 02 2015) gives `a(n) = (-1)^(n+1) * 4^(2n+1) * B(2n+1, 1/4)`, where
`B(n, x)` is the n-th Bernoulli polynomial, and adds: "Conjecturally, a(n) = the unsigned numerator
of B(2*n+1,1/4)." This file states that conjecture. (The entry reports a proof by Sela Fried,
Dec 22 2025; no Lean proof exists yet.)

Conventions:
* `x / cos(x)` is the formal power series `X * (cos x)⁻¹` in `PowerSeries ℚ`, with Mathlib's
  `PowerSeries.cos`; it has constant term `1`, so the inverse is the usual one. The term `a(n)` is
  `(2n+1)!` times its coefficient of `X^(2n+1)` (an e.g.f.), which is a natural number.
* `B(m, x)` is Mathlib's `Polynomial.bernoulli m` evaluated at `x`.
* "Unsigned numerator" is the numerator of the absolute value of the rational number, in lowest
  terms (`Rat.num`, which is `≥ 0` for a nonnegative rational).
* A computation with exact rationals confirms that this definition reproduces the data of the
  entry and that the conjectured identity holds for `n < 30`.
-/

namespace OMA.S_oeis_a009843

open PowerSeries

/-- `A009843(n)`: `(2n+1)!` times the coefficient of `x^(2n+1)` in `x / cos(x)`. -/
noncomputable def a (n : ℕ) : ℚ :=
  ((2 * n + 1).factorial : ℚ) * coeff (2 * n + 1) (X * (cos ℚ)⁻¹)

/-- Conjecture (Bala): `a(n)` is the unsigned numerator of `B(2n+1, 1/4)`. -/
theorem main :
    ∀ n : ℕ, a n = ((|(Polynomial.bernoulli (2 * n + 1)).eval (1 / 4 : ℚ)|).num : ℚ) := by
  sorry

end OMA.S_oeis_a009843
