import Mathlib

/-!
# A097406: Largest primitive prime factor of 2^n - 1

Source: https://oeis.org/A097406
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the largest primitive prime factor of 2^n - 1, or 1 if no such prime exists.
Conjectures:
(1) For every n >= 1, if a primitive prime factor exists, the largest one is of the form k*n + 1.
(3) For each prime n, every prime factor of 2^n - 1 is of the form k*n + 1.
-/

namespace OMA.S_oeis_a097406

def IsPrimitivePrimeFactor (n p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ (2 ^ n - 1) ∧ ∀ m : ℕ, 1 ≤ m → m < n → ¬ (p ∣ (2 ^ m - 1))

theorem main :
    (∀ n p : ℕ, 1 ≤ n → IsPrimitivePrimeFactor n p →
      (∀ q : ℕ, IsPrimitivePrimeFactor n q → q ≤ p) → ∃ k : ℕ, p = k * n + 1) ∧
    (∀ n p : ℕ, Nat.Prime n → Nat.Prime p → p ∣ (2 ^ n - 1) → ∃ k : ℕ, p = k * n + 1) := by
  sorry

end OMA.S_oeis_a097406
