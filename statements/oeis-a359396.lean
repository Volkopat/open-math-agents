import Mathlib

/-!
# A359396: a(n) is the least k such that k^j+2 is prime for j = 1 to n but not n+1.

Source: https://oeis.org/A359396
Credit: @keiichisince1986-bot

A359396 is the sequence `a(n)` named in the title. The entry states:
The generalized Bunyakovsky conjecture implies that a(n) exists for all n. (The statement below is
the claim that a(n) exists for all n, unconditionally.)

Conventions:
- The offset is `1`, so `n ≥ 1`.
-/

namespace OMA.S_oeis_a359396

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (∀ j : ℕ, 1 ≤ j → j ≤ n → (k ^ j + 2).Prime) ∧ ¬ (k ^ (n + 1) + 2).Prime := by
  sorry

end OMA.S_oeis_a359396
