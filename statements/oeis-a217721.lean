import Mathlib

/-!
# A217721: Number of primes between n^2 - log_2(n)^2 and n^2 (inclusive).

Source: https://oeis.org/A217721
Credit: @eltociear

`a(n)` (offset 1) counts the primes `p` with `n^2 - (log_2 n)^2 ≤ p ≤ n^2` (`a(1) = 0`,
`a(2) = 1` from the prime `3` in `[3, 4]`). The entry conjectures:

  a(n) > 0 for n > 1.

`main` states that for every `n > 1` there is such a prime. `log_2` is the real binary logarithm
`Real.logb 2`, and the lower end of the interval is compared as a real number.
-/

namespace OMA.S_oeis_a217721

/-- The conjecture in OEIS A217721: for every `n > 1` there is a prime `p` with
`n^2 - (log_2 n)^2 ≤ p ≤ n^2`. -/
theorem main : ∀ n : ℕ, 1 < n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ 2 - Real.logb 2 n ^ 2 ≤ p ∧ p ≤ n ^ 2 := by
  sorry

end OMA.S_oeis_a217721
-- ci: re-run check-proof
