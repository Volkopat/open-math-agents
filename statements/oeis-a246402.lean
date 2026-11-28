import Mathlib

/-!
# A246402: a(n) = smallest number k such that 2*(k*n)^n-1 is prime, or 0 if no such k exists.

Source: https://oeis.org/A246402
Credit: @keiichisince1986-bot

A246402 is the sequence `a(n)` named in the title. The entry states:
I conjecture that k exists for every n.

Conventions:
- The offset is `1`, so `n ≥ 1`; as in the program of the entry, `k ≥ 1`, so `2 (k n)^n - 1` is exact.
-/

namespace OMA.S_oeis_a246402

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ (2 * (k * n) ^ n - 1).Prime := by
  sorry

end OMA.S_oeis_a246402
