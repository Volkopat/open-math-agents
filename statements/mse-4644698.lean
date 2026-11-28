import Mathlib

/-!
# Is every twin prime average x > 6 the sum of two smaller twin prime averages?

Source: https://math.stackexchange.com/questions/4644698

If `p, q = p + 2` are twin primes, their average `x = p + 1 = q - 1` is a twin prime average
(`4, 6, 12, 18, 30, …`). Conjecture: every twin prime average `x > 6` is the sum `x = x' + x''`
of two smaller twin prime averages `x', x''` (not necessarily distinct, e.g. `12 = 6 + 6`).

Formalization notes:
* `x` is a twin prime average when `x - 1` and `x + 1` are both prime; for `x = 0` the
  truncated `x - 1 = 0` is not prime, so this matches the definition.
-/

namespace OMA.S_mse_4644698

/-- `x` is the average of a pair of twin primes `x - 1`, `x + 1`. -/
def IsTwinAvg (x : ℕ) : Prop := (x - 1).Prime ∧ (x + 1).Prime

/-- Every twin prime average `x > 6` is a sum of two smaller twin prime averages. -/
theorem main : ∀ x : ℕ, 6 < x → IsTwinAvg x →
    ∃ a b : ℕ, IsTwinAvg a ∧ IsTwinAvg b ∧ a < x ∧ b < x ∧ a + b = x := by
  sorry

end OMA.S_mse_4644698
