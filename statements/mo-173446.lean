import Mathlib

/-!
# Subspaces of `l₁` are not Lipschitz complemented in `l₁`

Source: https://mathoverflow.net/questions/173446/subspaces-of-l-1-are-not-lipschitz-complemented-in-l-1
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: is there a subspace `U` of `l₁` such that `l₁ / U` is isomorphic to `L₁(μ)` for some
measure `μ`, but `U` is not Lipschitz complemented in `l₁`? `main` states the positive answer
suggested by the title; a proof of its negation answers no.

Conventions:
* Real scalars; `l₁ = lp (fun _ : ℕ => ℝ) 1`. Subspaces are closed linear subspaces, and
  `l₁ / U` carries the quotient norm. Isomorphic means linearly homeomorphic.
* `L₁(μ)` is `MeasureTheory.Lp ℝ 1 μ` for a measure `μ` on some measurable space.
* `U` is Lipschitz complemented when there is a Lipschitz retraction of `l₁` onto `U`: a
  Lipschitz map `r : l₁ → U` with `r u = u` for `u ∈ U`.
-/

namespace OMA.S_mo_173446

/-- The sequence space `l₁`. -/
abbrev L1 := lp (fun _ : ℕ => ℝ) 1

theorem main :
    ∃ U : Submodule ℝ L1, IsClosed (U : Set L1) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
        Nonempty ((L1 ⧸ U) ≃L[ℝ] MeasureTheory.Lp ℝ 1 μ)) ∧
      ¬ ∃ (K : NNReal) (r : L1 → U), LipschitzWith K r ∧ ∀ u : U, r u = u := by
  sorry

end OMA.S_mo_173446
