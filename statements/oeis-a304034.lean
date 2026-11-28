import Mathlib

/-!
# Sun's squarefree power-sum conjecture (OEIS A304034)

The sequence counts representations. Its positivity above 11 is equivalent to
the existence of the three witnesses below.

Source: https://oeis.org/A304034
-/

namespace OMA.S_oeis_a304034

theorem main : ∀ n : ℕ, 11 < n →
    ∃ p k m : ℕ, p.Prime ∧ 0 < k ∧ 0 < m ∧
      Squarefree (2 ^ k + (1 + n % 2) * 3 ^ m) ∧
      n = p + 2 ^ k + (1 + n % 2) * 3 ^ m := by
  sorry

end OMA.S_oeis_a304034