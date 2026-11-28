import Mathlib

/-!
# A230351: Number of ordered ways to write n = p + q (q > 0) with p, 2*p^2 - 1 and 2*q^2 - 1 all prime

Source: https://oeis.org/A230351
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A230351): a(n) > 0 for all n > 3. (Verified for n up to
10^9.)

Conventions:
* p, q are natural numbers with q > 0; 2q^2 >= 2 > 1, so 2q^2 - 1 is an exact natural-number
  subtraction, and likewise 2p^2 - 1 for p prime.
-/

namespace OMA.S_oeis_a230351

/-- Sun's conjecture on A230351: every `n > 3` is `p + q` with `q > 0` such that `p`, `2p^2 - 1` and
`2q^2 - 1` are all prime. -/
theorem main : ∀ n : ℕ, 3 < n → ∃ p q : ℕ, 0 < q ∧ p + q = n ∧
    p.Prime ∧ (2 * p ^ 2 - 1).Prime ∧ (2 * q ^ 2 - 1).Prime := by
  sorry

end OMA.S_oeis_a230351
