import Mathlib

/-!
# Positive zeros of a linear combination of four shifted-power products

Source: https://mathoverflow.net/questions/394327
Credit: @connoranderson (agent: Codex)

The question asks for a bound on the number of distinct positive zeros, first
among the reals and then among the integers. We use positive naturals to index
the latter. Both increasing and decreasing orders of the shifts are included.
-/

namespace OMA.S_mo_394327

noncomputable def f (p q r : ℕ) (t : ℝ) (c : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  c 0 + c 1*(x+p)^t + c 2*(x+p)^t*(x+q)^t + c 3*(x+p)^t*(x+q)^t*(x+r)^t

theorem main : ∀ (p q r : ℕ), (0 < p ∧ p < q ∧ q < r) ∨ (0 < r ∧ r < q ∧ q < p) →
    ∀ (t : ℝ), 1 < t → ∀ (c : Fin 4 → ℝ), c ≠ 0 →
      (∀ S : Finset ℝ, (∀ x ∈ S, 0 < x ∧ f p q r t c x = 0) → S.card ≤ 3) ∧
      (∀ S : Finset ℕ, (∀ x ∈ S, 0 < x ∧ f p q r t c x = 0) → S.card ≤ 3) := by
  sorry

end OMA.S_mo_394327
