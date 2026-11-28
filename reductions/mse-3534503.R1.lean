import OMAStatements.S_mse_3534503
import Mathlib

/-! Suppose p occurs in the odd base to an exponent congruent to 1 modulo 3.
Then the divisor sum contains the factor p²+p+1. Divisibility into a power
forces a prime q from this factor into the complementary cofactor, with q=3
or q congruent to 1 modulo 3. The residual conjecture concerns bases that
satisfy this closure condition for every such p. -/

namespace OMA.R_mse_3534503_R1
open scoped ArithmeticFunction.sigma

def H1 : Prop := ∀ p t j m : ℕ, p.Prime → p.Coprime t →
    σ 1 ((p ^ (3 * j + 1) * t) ^ 2) ∣ ((p ^ (3 * j + 1) * t) ^ 2) ^ m →
    ∃ q : ℕ, q.Prime ∧ q ∣ t ∧ q ∣ p ^ 2 + p + 1 ∧ (q = 3 ∨ q % 3 = 1)

def H2 : Prop := ∀ k : ℕ, 1 ≤ k →
    (∀ p t j : ℕ, p.Prime → p.Coprime t → 2 * k + 1 = p ^ (3 * j + 1) * t →
      ∃ q : ℕ, q.Prime ∧ q ∣ t ∧ q ∣ p ^ 2 + p + 1 ∧ (q = 3 ∨ q % 3 = 1)) →
    ∀ m : ℕ, ¬ σ 1 ((2 * k + 1) ^ 2) ∣ ((2 * k + 1) ^ 2) ^ m

theorem main : H1 → H2 → type_of% @OMA.S_mse_3534503.main := by
  intro h1 h2 k hk m hd
  apply h2 k hk _ m hd
  intro p t j hp hc heq
  rw [heq] at hd
  exact h1 p t j m hp hc hd

end OMA.R_mse_3534503_R1
