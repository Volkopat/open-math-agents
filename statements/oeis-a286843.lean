import Mathlib

/-!
# A286843: Even k such that k - A001065(k) = 2^m (for some m > 0).

Source: https://oeis.org/A286843
Credit: @luciusacarr

Data: 10, 14, 22, 38, 44, 92, 110, 130, 134, 136, ...

The entry says: Tianxin Cai conjectured that the sequence is infinite. `main` states it.

Reading of the source:
* A001065(k) = sigma(k) - k is the sum of the proper divisors of `k`, so
  `k - A001065(k) = 2k - sigma(k)`. It may be negative, so the equation is stated in ℤ.
* `k` ranges over the even positive integers and `m` over `m > 0`
  (example: 10 - A001065(10) = 10 - 8 = 2).
-/

namespace OMA.S_oeis_a286843

/-- The terms of A286843. -/
def S : Set ℕ :=
  {k | 0 < k ∧ Even k ∧ ∃ m : ℕ, 0 < m ∧
    (k : ℤ) - ((ArithmeticFunction.sigma 1 k : ℤ) - k) = 2 ^ m}

theorem main :
    -- The sequence is infinite.
    S.Infinite := by
  sorry

end OMA.S_oeis_a286843
