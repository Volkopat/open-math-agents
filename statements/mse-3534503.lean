import Mathlib

/-!
# An odd square `n > 1` has no power divisible by the sum of its divisors

Source: https://math.stackexchange.com/questions/3534503

Conjecture: let `n = (2k + 1)²` with `k ∈ ℕ` and `n > 1`, and let `A = ∑_{d ∣ n} d`. Then `n^m`
is not divisible by `A` for any `m ∈ ℕ`. (For odd non-squares this is easy: `σ(n)` is even.)

Formalization notes:
* `n > 1` means `k ≥ 1`; `A` is `σ₁(n)`, Mathlib's `ArithmeticFunction.sigma 1`.
* `m` ranges over all of `ℕ`; `m = 0` holds trivially since `A > 1`.
-/

namespace OMA.S_mse_3534503

open scoped ArithmeticFunction.sigma

/-- For `k ≥ 1` and `n = (2k + 1)²`, `σ(n)` divides no power `n^m`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, ¬ σ 1 ((2 * k + 1) ^ 2) ∣ ((2 * k + 1) ^ 2) ^ m := by
  sorry

end OMA.S_mse_3534503
