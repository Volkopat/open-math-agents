import Mathlib

/-!
# Two conjectures related to Lemoine's and Goldbach's

Source: https://math.stackexchange.com/questions/2431879
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjectures (asker): (1) every odd `O ≥ 5` can be written `O = p - 2q` with `p, q` distinct odd
primes; (2) every odd `O ≥ 1` can be written `O = 2q - p` with `q < p`, `p` an odd prime and `q`
equal to `1` or an odd prime.
-/

namespace OMA.S_mse_2431879

/-- Both conjectures. -/
theorem main :
    (∀ O : ℕ, 5 ≤ O → Odd O → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≠ q ∧
      (O : ℤ) = p - 2 * q) ∧
    (∀ O : ℕ, 1 ≤ O → Odd O → ∃ p q : ℕ, p.Prime ∧ p ≠ 2 ∧ (q = 1 ∨ (q.Prime ∧ q ≠ 2)) ∧ q < p ∧
      (O : ℤ) = 2 * q - p) := by
  sorry

end OMA.S_mse_2431879
