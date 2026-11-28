import Mathlib

/-!
# A061652: Even superperfect numbers: 2^(p-1) where 2^p-1 is a Mersenne prime (A000668).

Source: https://oeis.org/A061652
Credit: @gblacher2

The source comment: "It is conjectured that there are no odd superperfect numbers, in which case
this coincides with A019279."

Superperfect numbers (A019279, https://oeis.org/A019279) are the numbers `k` with
`sigma(sigma(k)) = 2*k`, where `sigma` is the sum-of-divisors function (A000203). They are
positive integers (offset 1), so `k` ranges over positive integers: in Mathlib `σ 1 0 = 0`,
which would make `k = 0` satisfy the equation spuriously.
-/

namespace OMA.S_oeis_a061652

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `k` is superperfect: `σ(σ(k)) = 2k` (A019279), for a positive integer `k`. -/
def IsSuperperfect (k : ℕ) : Prop :=
  0 < k ∧ σ 1 (σ 1 k) = 2 * k

theorem main : ¬ ∃ k : ℕ, Odd k ∧ IsSuperperfect k := by
  sorry

end OMA.S_oeis_a061652
