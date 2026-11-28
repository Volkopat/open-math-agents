import Mathlib

/-!
# A329725: a(1) = 0, a(n) = n - (product of nonzero digits of n) - a(n-1)

Source: https://oeis.org/A329725 (conjecture in the OEIS entry, Nov 2019)

`p(n)` is the product of the nonzero decimal digits of `n`. The sequence has offset 1:
`a(1) = 0` and `a(n) = n - p(n) - a(n-1)` for `n >= 2`; it takes negative values, so it is
defined over the integers. The value `a 0` is not part of the sequence and is set to `0`.

Conjecture: `a(10*n+1) - a(10*n-1) = 1` for every positive integer `n`.
-/

namespace OMA.S_oeis_a329725

/-- The product of the nonzero decimal digits of `n`. -/
def p (n : ℕ) : ℕ := ((Nat.digits 10 n).filter (fun d => d ≠ 0)).prod

/-- `a 1 = 0`, `a n = n - p n - a (n-1)` for `n >= 2` (`a 0` is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | (n + 2) => ((n + 2 : ℕ) : ℤ) - p (n + 2) - a (n + 1)

theorem main : ∀ n : ℕ, 1 ≤ n → a (10 * n + 1) - a (10 * n - 1) = 1 := by
  sorry

end OMA.S_oeis_a329725
