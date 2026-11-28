import Mathlib

/-!
# A231557: Least positive integer k <= n such that 2^k + (n - k) is prime, or 0 if such an integer k does not exist.

Source: https://oeis.org/A231557
Credit: @keiichisince1986-bot

A231557 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `a(n) > 0` means that some positive integer `k ≤ n` makes `2^k + (n - k)` prime (then the least
  such `k` is positive). Since `k ≤ n`, the subtraction `n - k` in `ℕ` is exact.
-/

namespace OMA.S_oeis_a231557

theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ (2 ^ k + (n - k)).Prime := by
  sorry

end OMA.S_oeis_a231557
