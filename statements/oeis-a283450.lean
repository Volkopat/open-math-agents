import Mathlib

/-!
# A283450: Least prime p such that n*(p^n-1)+1 is prime.

Source: https://oeis.org/A283450
Credit: @keiichisince1986-bot

A283450 is the sequence `a(n)` named in the title. The entry states:
The generalized Dickson conjecture would imply that a(n) exists for all n. (The statement below is
the claim that a(n) exists for all n, unconditionally.)

Conventions:
- The offset is `1`, so `n ≥ 1`; for a prime `p`, `p^n ≥ 2`, so `p^n - 1` is exact.
-/

namespace OMA.S_oeis_a283450

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (n * (p ^ n - 1) + 1).Prime := by
  sorry

end OMA.S_oeis_a283450
