import Mathlib

/-!
# A072780: a(n) = sigma_2(n) + phi(n) * sigma(n) - 2*n^2

Source: https://oeis.org/A072780
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Statement: For `a(n) = σ₂(n) + φ(n) * σ₁(n) - 2 * n^2` (for `n ≥ 1`):
(1) `a(n) ≥ 0`, with equality if and only if `n = 1` or `n` is prime;
(2) `a(n) = 2` if and only if `n` is the product of two distinct primes.
-/

namespace OMA.S_oeis_a072780

/-- `a(n) = σ₂(n) + φ(n) * σ₁(n) - 2 * n^2` as an integer. -/
def a (n : ℕ) : ℤ :=
  (ArithmeticFunction.sigma 2 n : ℤ) +
    (Nat.totient n : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ) - 2 * (n : ℤ) ^ 2

theorem main :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ a n ∧ (a n = 0 ↔ n = 1 ∨ Nat.Prime n)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 2 ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p * q)) := by
  sorry

end OMA.S_oeis_a072780
