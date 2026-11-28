import Mathlib

/-!
# A205321: Smallest k>=0 such that (2^n+k)*2^n-1 and (2^n+k)*2^n+1 are a twin prime pair.

Source: https://oeis.org/A205321
Credit: @eltociear

`a(n)` (offset 1) is the least `k ≥ 0` such that `(2^n + k) * 2^n - 1` and `(2^n + k) * 2^n + 1`
are both prime (`a(1) = 0` from `(3, 5)`, `a(2) = 11` from `(59, 61)`). The entry conjectures:

  there is at least one k for each n.

`main` states that for every `n ≥ 1` such a `k` exists. Since `(2^n + k) * 2^n ≥ 4` for `n ≥ 1`,
the natural-number subtraction `- 1` is exact.
-/

namespace OMA.S_oeis_a205321

/-- The conjecture in OEIS A205321: for every `n ≥ 1` there is `k ≥ 0` such that
`(2^n + k) * 2^n - 1` and `(2^n + k) * 2^n + 1` are both prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, ((2 ^ n + k) * 2 ^ n - 1).Prime ∧ ((2 ^ n + k) * 2 ^ n + 1).Prime := by
  sorry

end OMA.S_oeis_a205321
