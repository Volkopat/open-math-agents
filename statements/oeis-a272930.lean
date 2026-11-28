import Mathlib

/-!
# A272930: least `k` with `σ(σ(k)) = n k`

Source: https://oeis.org/A272930
Credit: @Lenqth

A272930(n) (offset 1) is the least `k` such that `σ(σ(k)) = n k`, where `σ` is the sum of
divisors, or `0` if there is no such `k`. Known values: `1, 2, 8, 15, ?, 42, 24, 60, 168, ...`; the
entry notes that if `a(5)` is not zero, it exceeds `5 * 10^11`.

Formalizes the question in the comments of A272930 (F. T. Adams-Watters, who previously
conjectured that the answer is yes): is `a(n)` nonzero for every positive `n`? That is, for every
`n ≥ 1` there is a positive integer `k` with `σ(σ(k)) = n k`.
-/

namespace OMA.S_oeis_a272930

/-- For every `n ≥ 1` there is a `k ≥ 1` with `σ(σ(k)) = n * k`. -/
theorem main : ∀ n : ℕ, 0 < n →
    ∃ k : ℕ, 0 < k ∧ ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 k) = n * k := by
  sorry

end OMA.S_oeis_a272930
