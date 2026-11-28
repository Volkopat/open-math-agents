import Mathlib

/-!
# A236472: a(n) = |{0 < k < n: p = prime(k) + phi(n-k), prime(p) + 2 and prime(p) + 6 are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236472
Credit: @keiichisince1986-bot

A236472 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for every n = 330, 331, ....

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)`.
- `phi` is `Nat.totient`; `p` itself must be prime (as in the program).
-/

namespace OMA.S_oeis_a236472

theorem main :
    ∀ n : ℕ, 330 ≤ n → ∃ k p : ℕ, 0 < k ∧ k < n ∧ p = Nat.nth Nat.Prime (k - 1) + Nat.totient (n - k) ∧
      p.Prime ∧ (Nat.nth Nat.Prime (p - 1) + 2).Prime ∧ (Nat.nth Nat.Prime (p - 1) + 6).Prime := by
  sorry

end OMA.S_oeis_a236472
