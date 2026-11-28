import Mathlib

/-!
# Generalization of Legendre's conjecture

Source: https://mathoverflow.net/questions/267017/generalization-of-legendres-conjecture
Credit: @shc261392

Question. Is it true that for every `ε ∈ (0, 1]` there exists a natural number `n₀(ε)` such that
for every `n ≥ n₀(ε)` there is always a prime between `n^{1+ε}` and `(n+1)^{1+ε}`?

Reading used here (the affirmative answer): "between" is read strictly,
`n^{1+ε} < p < (n+1)^{1+ε}`, with real powers.
-/

namespace OMA.S_mo_267017

theorem main :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ (1 + ε) < p ∧ (p : ℝ) < ((n : ℝ) + 1) ^ (1 + ε) := by
  sorry

end OMA.S_mo_267017
