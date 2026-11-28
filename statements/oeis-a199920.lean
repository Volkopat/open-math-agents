import Mathlib

/-!
# A199920: two conjectures of Zhi-Wei Sun on sums `n = p + k`

Source: https://oeis.org/A199920
Credit: @jagraj28

A199920 is the number of ways to write `n = p + k` with `p`, `p + 6`, `6k - 1` and `6k + 1` all
prime. The entry records two conjectures of Zhi-Wei Sun:
1. `a(n) > 0` for all `n > 11`;
2. any integer `n > 6` not equal to 319 can be written as `p + k` with `p`, `p + 6`,
   `3k - 2 + (n mod 2)` and `3k + 2 - (n mod 2)` all prime.

`main` is the conjunction of the two.

Conventions: `p` and `k` are positive integers (`6k - 1` and `3k - 2 + (n mod 2)` are only
meaningful primes for `k ≥ 1`; with `k ≥ 1` every subtraction below is exact in `ℕ`).
A check of both statements for `n ≤ 30000` finds no exception other than `n = 319` in part 2.
-/

namespace OMA.S_oeis_a199920

/-- Sun's two conjectures in OEIS A199920. -/
theorem main :
    (∀ n : ℕ, 11 < n → ∃ p k : ℕ, 1 ≤ k ∧ n = p + k ∧
      p.Prime ∧ (p + 6).Prime ∧ (6 * k - 1).Prime ∧ (6 * k + 1).Prime) ∧
    (∀ n : ℕ, 6 < n → n ≠ 319 → ∃ p k : ℕ, 1 ≤ k ∧ n = p + k ∧
      p.Prime ∧ (p + 6).Prime ∧ (3 * k - 2 + n % 2).Prime ∧ (3 * k + 2 - n % 2).Prime) := by
  sorry

end OMA.S_oeis_a199920
