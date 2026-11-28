import Mathlib

/-!
# Infinitely many composite Euclid numbers of the second kind (Kummer numbers)?

Source: https://math.stackexchange.com/questions/4549942
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The Kummer numbers are `p₁ p₂ ⋯ pₙ - 1` (`pᵢ` the `i`-th prime). Question: are there infinitely
many composite Kummer numbers? `main` states the answer yes.

Conventions:
* `pᵢ = Nat.nth Nat.Prime (i - 1)`, `n ≥ 1`; composite means `> 1` and not prime.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mse_4549942

/-- The `n`-th Kummer number `p₁ ⋯ pₙ - 1`. -/
noncomputable def kummer (n : ℕ) : ℕ := (∏ i ∈ Finset.range n, Nat.nth Nat.Prime i) - 1

/-- Infinitely many Kummer numbers are composite. -/
theorem main : {n : ℕ | 1 ≤ n ∧ 1 < kummer n ∧ ¬ (kummer n).Prime}.Infinite := by
  sorry

end OMA.S_mse_4549942
