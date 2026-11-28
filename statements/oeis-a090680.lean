import Mathlib

/-!
# A090680: Number of primes p such that n < p < n+A033677(n).

Source: https://oeis.org/A090680
Credit: @eltociear

A033677(n) is the smallest divisor `d` of `n` with `d ≥ sqrt(n)`, equivalently `d * d ≥ n`
(for example A033677(36) = 6 and A033677(40) = 8). A090680(n) (offset 2) counts the primes `p`
with `n < p < n + A033677(n)`. The entry conjectures:

  no a(n) is zero,

that is, for every `n ≥ 2` there is a prime strictly between `n` and `n + A033677(n)`.
For `n ≥ 1` the set defining `A033677 n` contains `n`, so the infimum is attained.
-/

namespace OMA.S_oeis_a090680

/-- OEIS A033677: the smallest divisor `d` of `n` with `d ≥ √n`, i.e. `n ≤ d * d`. -/
noncomputable def A033677 (n : ℕ) : ℕ := sInf {d : ℕ | d ∣ n ∧ n ≤ d * d}

/-- The conjecture in OEIS A090680: for every `n ≥ 2` there is a prime `p` with
`n < p < n + A033677 n`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < n + A033677 n := by
  sorry

end OMA.S_oeis_a090680
-- ci: re-run check-proof
