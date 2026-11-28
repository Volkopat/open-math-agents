import Mathlib

/-!
# OEIS A006521: two conjectures on n ∣ 2^n + 1

Source: https://oeis.org/A006521
`A006521` lists the `n` with `n ∣ 2^n + 1`. The entry records two conjectures:
1. if `n ∣ 2^n + 1`, then `(2^n + 1)/n` is squarefree;
2. for every `k > 1`, the congruence `k^m ≡ 1 - k (mod m)` has infinitely many positive
   solutions `m`.
`main` is their conjunction.

Conventions. In 2 the congruence is taken in `ℤ`: `m ∣ k^m - (1 - k)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a006521

theorem main :
    (∀ n : ℕ, 1 ≤ n → n ∣ 2 ^ n + 1 → Squarefree ((2 ^ n + 1) / n)) ∧
    (∀ k : ℕ, 1 < k →
      {m : ℕ | 0 < m ∧ (m : ℤ) ∣ (k : ℤ) ^ m - (1 - k)}.Infinite) := by
  sorry

end OMA.S_oeis_a006521
