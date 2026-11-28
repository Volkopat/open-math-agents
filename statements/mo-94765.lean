import Mathlib

/-!
# Sums of digits again

Source: https://mathoverflow.net/questions/94765 (CC BY-SA 4.0).

Conjecture: for every two natural numbers `a < b` with `a, b ≢ 0 (mod 10)`, there exists `n < b`
such that the sums of the decimal digits of `na` and `nb` are different. (One cannot ask for
`n ≤ a`: for `a = 10^k + 1`, `b = 10^{k+1} + 1` the least such `n` is `10^k + 9`.)

Formalization notes:
* The decimal digit sum is `(Nat.digits 10 m).sum`.
* `n = 0` never works (both digit sums are `0`), so asking for `0 < n < b` is the same.
* Checked numerically: holds for all `a < b < 400`.
-/

namespace OMA.S_mo_94765

/-- The sum of the decimal digits of `m`. -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- For `a < b`, neither divisible by `10`, some `0 < n < b` gives `na`, `nb` different digit sums. -/
theorem main : ∀ a b : ℕ, a < b → a % 10 ≠ 0 → b % 10 ≠ 0 →
    ∃ n : ℕ, 0 < n ∧ n < b ∧ digitSum (n * a) ≠ digitSum (n * b) := by
  sorry

end OMA.S_mo_94765
