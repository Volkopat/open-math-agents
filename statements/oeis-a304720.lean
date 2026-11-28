import Mathlib

/-!
# A304720: Number of nonnegative integers k such that n - (4^k - k) is positive and squarefree.

Source: https://oeis.org/A304720
Credit: @keiichisince1986-bot

A304720 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- `a(n) > 0` means that there is a natural number `k` with `n - (4^k - k)` positive and
  squarefree. Since `k < 4^k`, the truncated subtraction `4 ^ k - k` in `ℕ` is exact, and
  positivity is `4 ^ k - k < n`, which also makes `n - (4 ^ k - k)` exact.
-/

namespace OMA.S_oeis_a304720

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 4 ^ k - k < n ∧ Squarefree (n - (4 ^ k - k)) := by
  sorry

end OMA.S_oeis_a304720
