import Mathlib

/-!
# A255932: a(n) is the denominator of Gamma(n+1/2)^2/(2*n*Pi), the value of an integral with sinh in the denominator.

Source: https://oeis.org/A255932
Credit: @ceejcake

Conjecture (OEIS A255932, Vaclav Kotesovec, Mar 11 2015): `a(n) <= 2^(3*n)`.

Formalization notes:
* The sequence has offset `1`, so the claim is stated for `n : ℕ` with `1 ≤ n`.
* `value n` is the real number `Γ(n + 1/2)^2 / (2 * n * π)`, written with `Real.Gamma` and `Real.pi`.
* `a(n)` is the denominator of `value n` in lowest terms. The statement encodes this as: there is a
  rational `q` whose image in `ℝ` is `value n` and whose reduced denominator `q.den` is at most
  `2 ^ (3 * n)`. Since the cast `ℚ → ℝ` is injective, such a `q` is unique, so the statement says
  exactly that `value n` is rational and that its denominator `a(n)` is at most `2 ^ (3 * n)`.
* Initial values for `n = 1, ..., 8`: the fractions are `1/8, 9/64, 75/128, 11025/2048, ...`, and
  `a(n) = 8, 64, 128, 2048, 2048, 16384, 32768, 1048576`.
-/

namespace OMA.S_oeis_a255932

/-- The real number `Γ(n + 1/2)^2 / (2 * n * π)`, whose denominator is `a(n)`. -/
noncomputable def value (n : ℕ) : ℝ :=
  Real.Gamma (n + 1 / 2) ^ 2 / (2 * n * Real.pi)

/-- OEIS A255932 conjecture: for every `n ≥ 1`, `value n` is a rational number whose denominator
`a(n)` satisfies `a(n) ≤ 2 ^ (3 * n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ q : ℚ, (q : ℝ) = value n ∧ q.den ≤ 2 ^ (3 * n) := by
  sorry

end OMA.S_oeis_a255932
