import Mathlib

/-!
# OEIS A216359: the g.f. satisfies `A(x) = (1 + x A(x)²) (1 + x / A(x))`

Source: https://oeis.org/A216359
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the n-th coefficient of the power series `A(x)` with `A(0) = 1` and
`A(x) = (1 + x A(x)²) (1 + x / A(x))`, offset 0 (`1, 2, 3, 13, 32, 147, 445, 2067, …`).

The entry (Peter Bala, Sep 10 2024): "For n not of the form 3*m + 1, we conjecture that
a(n) = Sum_{k = 0..n} binomial(-n+3*k+1, k)*binomial(-n+3*k+1, n-k)/(-n+3*k+1)."
This file states that conjecture.

Conventions:
* `A` has constant term `1`, so it is a unit of `PowerSeries ℚ`, and multiplying the defining
  equation by `A` gives the equivalent `A² = (1 + x A²) (A + x)`, which is the form used here.
  This equation determines every coefficient of `A` from the earlier ones (the coefficient of `x^n`
  on the left has `2 a(n)`, on the right `a(n)`, plus earlier terms), so there is exactly one such
  `A`; the statement is made for that `A` by quantifying over every solution.
* `binomial(x, k)` for an integer `x` (possibly negative) is the generalized binomial coefficient
  `x (x - 1) ⋯ (x - k + 1) / k!`, written with Mathlib's `descPochhammer`, and the sum is in `ℚ`.
  For `n` not of the form `3m + 1` the divisor `-n + 3k + 1` is never `0`.
* A computation with exact rationals confirms that this `A` reproduces the data of the entry and
  that the conjectured formula holds for every `n ≤ 40` not of the form `3m + 1`.
-/

namespace OMA.S_oeis_a216359

open PowerSeries

/-- The generalized binomial coefficient `binomial(x, k) = x (x - 1) ⋯ (x - k + 1) / k!`. -/
noncomputable def gchoose (x : ℤ) (k : ℕ) : ℚ :=
  (descPochhammer ℚ k).eval (x : ℚ) / (k.factorial : ℚ)

/-- Bala's conjectured closed form. -/
noncomputable def bala (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    gchoose (-(n : ℤ) + 3 * k + 1) k * gchoose (-(n : ℤ) + 3 * k + 1) (n - k)
      / ((-(n : ℤ) + 3 * k + 1 : ℤ) : ℚ)

/-- Conjecture (Bala): for `n` not of the form `3m + 1`, `a(n)` is given by the binomial sum. -/
theorem main :
    ∀ A : PowerSeries ℚ, constantCoeff A = 1 → A ^ 2 = (1 + X * A ^ 2) * (A + X) →
      ∀ n : ℕ, n % 3 ≠ 1 → coeff n A = bala n := by
  sorry

end OMA.S_oeis_a216359
