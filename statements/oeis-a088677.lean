import Mathlib

/-!
# OEIS A088677: sums of two sixth powers in only one way

Source: https://oeis.org/A088677
Numbers that can be represented as `j⁶ + k⁶`, `0 < j < k`, in exactly one way. Conjecture: no
number can be expressed as such a sum in more than one way.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a088677

theorem main :
    ∀ j k j' k' : ℕ, 0 < j → j < k → 0 < j' → j' < k' →
      j ^ 6 + k ^ 6 = j' ^ 6 + k' ^ 6 → j = j' ∧ k = k' := by
  sorry

end OMA.S_oeis_a088677
