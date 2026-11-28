import Mathlib

/-!
# A220554: Number of ways to write 2n = p+q (q>0) with p, 2p+1 and (p-1)^2+q^2 all prime

Source: https://oeis.org/A220554
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A220554): a(n)>0 for all n>1. (Verified for n up to
10^9.)

Conventions:
* p, q are natural numbers with q > 0; since p is prime, p - 1 >= 1 and the natural-number
  subtraction is exact.
* a(n) > 0 means that at least one such pair (p, q) exists.
-/

namespace OMA.S_oeis_a220554

/-- Sun's conjecture on A220554: for every `n > 1`, `2n = p + q` with `q > 0` such that `p`,
`2p + 1` and `(p - 1)^2 + q^2` are all prime. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ p q : ℕ, 0 < q ∧ p + q = 2 * n ∧
    p.Prime ∧ (2 * p + 1).Prime ∧ ((p - 1) ^ 2 + q ^ 2).Prime := by
  sorry

end OMA.S_oeis_a220554
