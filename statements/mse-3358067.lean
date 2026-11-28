import Mathlib

/-!
# Sums of arctangents equal to a multiple of π/2

Source: https://math.stackexchange.com/questions/3358067
Fact: `arctan 1 + arctan 2 + arctan 3 = π`. Conjecture: there is no `n ≠ 3` such that
`arctan 1 + arctan 2 + ⋯ + arctan n = kπ/2` for an integer `k`.

Conventions. `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_3358067

open Real

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 3 →
      ¬ ∃ k : ℤ, ∑ j ∈ Finset.Icc 1 n, arctan j = k * π / 2 := by
  sorry

end OMA.S_mse_3358067
