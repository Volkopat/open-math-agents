import Mathlib

/-!
# A246827: smallest `x` with `σ(x)/x = 2 σ(n)/n`

Source: https://oeis.org/A246827
Credit: @Lenqth

A246827(n) (offset 1) is the smallest `x` such that `σ(x)/x = 2 σ(n)/n`, where `σ` is the sum of
divisors. For example `a(1) = 6`, since `σ(6)/6 = 2 = 2 σ(1)/1`.

Formalizes the conjecture in the comments of A246827: `a(n)` exists for all `n`, i.e. for every
`n ≥ 1` there is a positive integer `x` whose abundancy `σ(x)/x` is twice that of `n`.
-/

namespace OMA.S_oeis_a246827

/-- For every `n ≥ 1` there is an `x ≥ 1` with `σ(x)/x = 2 σ(n)/n` (as rational numbers). -/
theorem main : ∀ n : ℕ, 0 < n → ∃ x : ℕ, 0 < x ∧
    (ArithmeticFunction.sigma 1 x : ℚ) / x = 2 * (ArithmeticFunction.sigma 1 n : ℚ) / n := by
  sorry

end OMA.S_oeis_a246827
