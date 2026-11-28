import Mathlib

/-!
# Complete vector field on $\mathbb{R}^2$ with all orbits dense

Source: https://math.stackexchange.com/questions/705193/does-there-exist-a-vector-field-s-t-all-orbits-are-dense-on-mathbbr2
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Does there exist a smooth complete vector field on $\mathbb{R}^2$ such that every orbit of
its flow is dense in $\mathbb{R}^2$?
-/

namespace OMA.S_mse_705193

theorem main :
    ∃ (V : (ℝ × ℝ) → (ℝ × ℝ)) (Φ : ℝ → (ℝ × ℝ) → (ℝ × ℝ)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      (∀ x : ℝ × ℝ, Φ 0 x = x) ∧
      (∀ s t : ℝ, ∀ x : ℝ × ℝ, Φ (s + t) x = Φ s (Φ t x)) ∧
      (∀ (x : ℝ × ℝ) (t : ℝ), HasDerivAt (fun τ => Φ τ x) (V (Φ t x)) t) ∧
      (∀ x : ℝ × ℝ, Dense (Set.range (fun t : ℝ => Φ t x))) := by
  sorry

end OMA.S_mse_705193
