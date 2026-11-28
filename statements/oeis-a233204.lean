import Mathlib

/-!
# A233204: Number of ways to write n = k + m with 0 < k < m such that 2^k * prime(m) + 3 is prime.

Source: https://oeis.org/A233204
Credit: @keiichisince1986-bot

A233204 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 3. [The entry continues with further conjectures about other
expressions; only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- `a(n) > 0` means that `n = k + m` with `0 < k < m` and `2^k * prime(m) + 3` prime.
-/

namespace OMA.S_oeis_a233204

theorem main :
    ∀ n : ℕ, 3 < n → ∃ k m : ℕ, 0 < k ∧ k < m ∧ k + m = n ∧
      (2 ^ k * Nat.nth Nat.Prime (m - 1) + 3).Prime := by
  sorry

end OMA.S_oeis_a233204
