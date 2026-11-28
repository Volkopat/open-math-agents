import Mathlib

/-!
# A032446: Carmichael's Totient Conjecture for Even Values

Source: https://oeis.org/A032446
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A032446(n) is the number of positive integers `k` such that `φ(k) = 2 * n`.

Conjecture (Carmichael's conjecture): For every `n ≥ 1`, `A032446(n) ≠ 1`.
-/

namespace OMA.S_oeis_a032446

/-- Number of positive integers `k` with `φ(k) = 2 * n`. -/
noncomputable def totientPreimageCard (n : ℕ) : ℕ :=
  Set.ncard { k : ℕ | 0 < k ∧ Nat.totient k = 2 * n }

theorem main :
    ∀ n : ℕ, 1 ≤ n → totientPreimageCard n ≠ 1 := by
  sorry

end OMA.S_oeis_a032446
