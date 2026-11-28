import Mathlib

/-!
# The square-sum problem

Source: https://math.stackexchange.com/questions/2637546
The square-sum problem (popularised by Matt Parker): for all sufficiently large `n`, the
numbers `1, …, n` can be arranged in a row so that every two adjacent numbers sum to a perfect
square. The question quotes the threshold `n ≥ 89`; the standard form of the conjecture uses
`n ≥ 25`, which `main` states (it implies the quoted form).

Conventions. An arrangement is a bijection `p : Fin n ≃ Fin n`, the number at position `i`
being `p i + 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_2637546

theorem main :
    ∀ n : ℕ, 25 ≤ n → ∃ p : Equiv.Perm (Fin n),
      ∀ i j : Fin n, j.val = i.val + 1 → IsSquare ((p i).val + 1 + ((p j).val + 1)) := by
  sorry

end OMA.S_mse_2637546
