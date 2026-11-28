import Mathlib

/-!
# A346154: a(n) is the least prime of the form n^k+n+1 with k>1, or 0 if there is no such prime.

Source: https://oeis.org/A346154
Credit: @keiichisince1986-bot

A346154 is the sequence `a(n)` named in the title. The entry states:
a(n) = 0 if n == 1 (mod 3) and n > 1. Conjecture: a(n) > 0 otherwise.

Conventions:
- The offset is `1`. `a(n) > 0` means that `n^k + n + 1` is prime for some `k > 1`; the conjecture is for every
  `n ≥ 1` with `n = 1` or `n` not congruent to `1` modulo `3`.
-/

namespace OMA.S_oeis_a346154

theorem main :
    ∀ n : ℕ, 1 ≤ n → (n = 1 ∨ n % 3 ≠ 1) → ∃ k : ℕ, 1 < k ∧ (n ^ k + n + 1).Prime := by
  sorry

end OMA.S_oeis_a346154
