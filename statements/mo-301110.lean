import Mathlib

/-!
# Density of the Klarner–Rado sequence

Source: https://mathoverflow.net/questions/301110
The Klarner–Rado set (OEIS A005658) is the smallest set of positive integers containing `1`
and closed under `n ↦ 2n`, `n ↦ 3n + 2`, `n ↦ 6n + 3`. Klarner conjectured that it has
positive density.

Conventions. "Positive density" is read as positive lower density: some `c > 0` has
`#(S ∩ [1, x]) ≥ c x` for all large `x`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_301110

/-- The Klarner–Rado set. -/
inductive InKR : ℕ → Prop
  | one : InKR 1
  | double {n : ℕ} : InKR n → InKR (2 * n)
  | three {n : ℕ} : InKR n → InKR (3 * n + 2)
  | six {n : ℕ} : InKR n → InKR (6 * n + 3)

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * x ≤ (Set.ncard {n : ℕ | n ≤ x ∧ InKR n} : ℝ) := by
  sorry

end OMA.S_mo_301110
