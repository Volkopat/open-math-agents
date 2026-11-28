import Mathlib

/-!
# A233439: a(n) = |{0 < k < n: prime(k)^2 + 4*prime(n-k)^2 is prime}|.

Source: https://oeis.org/A233439
Credit: @keiichisince1986-bot

A233439 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 3. [Parts (ii) and (iii) of the entry concern other
expressions; only part (i) is formalized here.]

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- `a(n) > 0` means that `prime(k)^2 + 4 * prime(n - k)^2` is prime for some `0 < k < n`.
-/

namespace OMA.S_oeis_a233439

theorem main :
    ∀ n : ℕ, 3 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
      (Nat.nth Nat.Prime (k - 1) ^ 2 + 4 * Nat.nth Nat.Prime (n - k - 1) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a233439
