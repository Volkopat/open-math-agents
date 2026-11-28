import Mathlib

/-!
# Infinitely recurring values in OEIS A189827

Source: https://oeis.org/A189827
Credit: @gdyan2022
-/

namespace OMA.S_oeis_a189827

/-- Every natural number greater than three occurs infinitely often among the sums of
the divisor counts of the two neighbors of `n`, with `n` starting at two. -/
theorem main : ∀ k : ℕ, 3 < k →
    {n : ℕ | 2 ≤ n ∧ (n - 1).divisors.card + (n + 1).divisors.card = k}.Infinite := by
  sorry

end OMA.S_oeis_a189827
