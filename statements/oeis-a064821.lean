import Mathlib

/-!
# OEIS A064821: prime-sum arrangements of 1..n exist

Source: https://oeis.org/A064821
`a n` is the number of ways to write `1, …, n` in a sequence so that the sum of any two
adjacent numbers is prime (reversal not counted as different): 0, 1, 1, 4, 2, 8, … from
`n = 1`. Conjecture: `a n > 0` for all `n ≥ 2`.

Conventions. An arrangement is a bijection `p : Fin n ≃ Fin n`, the number at position `i`
being `p i + 1`; `a n > 0` means some arrangement exists.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a064821

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ p : Equiv.Perm (Fin n),
      ∀ i j : Fin n, j.val = i.val + 1 → ((p i).val + 1 + ((p j).val + 1)).Prime := by
  sorry

end OMA.S_oeis_a064821
