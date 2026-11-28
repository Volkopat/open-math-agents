import Mathlib

/-!
# A228144: Smallest k > n such that j*10^k + m*10^n - 1 is a prime number for at least a pair {j,m} with 0 < j < 10 and 0 < m < 10.

Source: https://oeis.org/A228144
Credit: @eltociear

`a(n)` (offset 1) is the least `k > n` such that `j * 10^k + m * 10^n - 1` is prime for some digits
`0 < j < 10` and `0 < m < 10` (`a(1) = 2` from `109 = 1·10^2 + 1·10 - 1`). The entry conjectures:

  there is always at least one k for each n.

`main` states that for every `n ≥ 1` some `k > n` and digits `j, m ∈ [1, 9]` make
`j * 10^k + m * 10^n - 1` prime. The subtraction is exact since `j * 10^k ≥ 1`.
-/

namespace OMA.S_oeis_a228144

/-- The conjecture in OEIS A228144: for every `n ≥ 1` there are `k > n` and `j, m ∈ [1, 9]` with
`j * 10^k + m * 10^n - 1` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k j m : ℕ, n < k ∧ j ∈ Finset.Icc 1 9 ∧ m ∈ Finset.Icc 1 9 ∧
      (j * 10 ^ k + m * 10 ^ n - 1).Prime := by
  sorry

end OMA.S_oeis_a228144
