import Mathlib

/-!
# A377838: Let p = prime(n), then a(n) is the least prime q < p such that p * q# + 1 is prime.

Source: https://oeis.org/A377838
Credit: @warshanks

For `p = prime(n)`, `a(n)` is the least prime `q < p` such that `p * q# + 1` is prime, where `q#`
(A034386) is the primorial of `q`, the product of all primes `≤ q`. The entry records one
conjecture (Buhler, Crandall and Penk):

  `a(n)` exists for all `n > 1`,

that is, for every prime `p = prime(n)` with `n > 1` (equivalently, every prime `p > 2`) there is a
prime `q < p` such that `p * q# + 1` is prime. `q#` is Mathlib's `primorial q`,
`∏ p ∈ range (q + 1) with p.Prime, p`.
-/

namespace OMA.S_oeis_a377838

/-- The Buhler–Crandall–Penk conjecture recorded in OEIS A377838: for every prime `p > 2` there is
a prime `q < p` such that `p * q# + 1` is prime. -/
theorem main : ∀ p : ℕ, p.Prime → 2 < p → ∃ q : ℕ, q.Prime ∧ q < p ∧ (p * primorial q + 1).Prime := by
  sorry

end OMA.S_oeis_a377838
