import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a155200

/-- Coefficients of `A(x) = exp(∑_{k ≥ 1} 2^(k^2) * x^k / k)`, defined via the equivalent
logarithmic-derivative recurrence `a(0) = 1` and
`n * a(n) = ∑_{k=1}^n 2^(k^2) * a(n - k)` for `n ≥ 1`. -/
def a : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k ∈ Finset.range (n + 1), (2 : ℚ) ^ ((k + 1) ^ 2) * a (n - k)) / ((n + 1 : ℕ) : ℚ)

/-- OEIS A155200 Conjecture: the highest exponent of `2` dividing `a(n)` equals `A000120(n)`
(the number of `1`s in the binary expansion of `n`), so that `a(n) / 2^A000120(n)` is an odd
integer for all `n ≥ 0`. -/
theorem main :
    ∀ n : ℕ, ∃ m : ℕ, Odd m ∧ a n = ((2 ^ (Nat.digits 2 n).sum * m : ℕ) : ℚ) := by
  sorry

end OMA.S_oeis_a155200
