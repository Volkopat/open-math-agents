import Mathlib

/-!
# A233542: Number of ways to write n = k^2 + m with k > 0 and m > 0 such that phi(k^2)*phi(m) - 1 is prime, where phi(.) is Euler's totient function (A000010).

Source: https://oeis.org/A233542
Credit: @keiichisince1986-bot

A233542 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 5. [Parts (ii) and (iii) of the entry concern other
expressions; only part (i) is formalized here.]

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- `phi(k^2) * phi(m) ≥ 1` for `k, m > 0`, so the natural-number subtraction is exact.
-/

namespace OMA.S_oeis_a233542

theorem main :
    ∀ n : ℕ, 5 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k ^ 2 + m ∧
      (Nat.totient (k ^ 2) * Nat.totient m - 1).Prime := by
  sorry

end OMA.S_oeis_a233542
