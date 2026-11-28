import Mathlib

/-!
# Normal curvature of Veronese embedding

Source: https://mathoverflow.net/questions/445819
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Petrunin): does the Veronese embedding minimize the maximal normal curvature among all
smooth embeddings `ℝPⁿ ↪ Sᴺ`? The Veronese embedding has normal curvature
`κ_n = sqrt((n-1)/(n+1))` at every point in every direction, so the question asks whether every
smooth embedding `ℝPⁿ ↪ Sᴺ` has normal curvature at least `κ_n` at some point in some direction.
The question is yes/no; `main` states the answer yes.

Conventions:
* A smooth embedding `ℝPⁿ ↪ Sᴺ` is given by a smooth map `f : ℝⁿ⁺¹ → ℝᴺ⁺¹` (any smooth extension of
  the map on `Sⁿ`) that sends `Sⁿ` into `Sᴺ`, is even on `Sⁿ` (`f(-x) = f(x)`), is injective on
  `Sⁿ` up to `x ↦ -x`, and whose derivative at each `x ∈ Sⁿ` is injective on the tangent space
  `x^⊥`.
* For `x ∈ Sⁿ` and a unit vector `v ⊥ x`, let `γ(t) = f(cos t · x + sin t · v)`. The normal space of
  the image `M` inside `Sᴺ` at `p = f(x)` is the orthogonal complement of `K = T_pM + ℝ p`, and the
  normal curvature of `M` in `Sᴺ` in the direction `γ'(0)` is `dist(γ''(0), K) / ‖γ'(0)‖²`
  (the norm of the second fundamental form `II(w, w)` for the unit vector `w = γ'(0)/‖γ'(0)‖`;
  it does not depend on the curve through `p` with that velocity).
-/

namespace OMA.S_mo_445819

open Metric

/-- `ℝᵐ`. -/
abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- `f` restricted to `Sⁿ` induces a smooth embedding `ℝPⁿ ↪ Sᴺ`. -/
def IsRPEmbedding {n N : ℕ} (f : E (n + 1) → E (N + 1)) : Prop :=
  ContDiff ℝ ⊤ f ∧
    (∀ x ∈ sphere (0 : E (n + 1)) 1, ‖f x‖ = 1 ∧ f (-x) = f x) ∧
    (∀ x ∈ sphere (0 : E (n + 1)) 1, ∀ y ∈ sphere (0 : E (n + 1)) 1,
      f x = f y → y = x ∨ y = -x) ∧
    (∀ x ∈ sphere (0 : E (n + 1)) 1, ∀ v : E (n + 1),
      inner ℝ x v = 0 → fderiv ℝ f x v = 0 → v = 0)

/-- The subspace `K = T_{f x} M + ℝ f(x)`. -/
noncomputable def K {n N : ℕ} (f : E (n + 1) → E (N + 1)) (x : E (n + 1)) : Submodule ℝ (E (N + 1)) :=
  Submodule.span ℝ ((fderiv ℝ f x) '' {v | inner ℝ x v = 0} ∪ {f x})

/-- The curve `t ↦ f(cos t · x + sin t · v)`. -/
noncomputable def γ {n N : ℕ} (f : E (n + 1) → E (N + 1)) (x v : E (n + 1)) : ℝ → E (N + 1) :=
  fun t => f (Real.cos t • x + Real.sin t • v)

/-- The normal curvature of the image in `Sᴺ` at `f x` in the direction of `γ'(0)`. -/
noncomputable def normalCurvature {n N : ℕ} (f : E (n + 1) → E (N + 1)) (x v : E (n + 1)) : ℝ :=
  infDist (deriv (deriv (γ f x v)) 0) (K f x : Set (E (N + 1))) / ‖deriv (γ f x v) 0‖ ^ 2

theorem main :
    ∀ (n N : ℕ) (f : E (n + 1) → E (N + 1)), IsRPEmbedding f →
      ∃ x ∈ sphere (0 : E (n + 1)) 1, ∃ v : E (n + 1), ‖v‖ = 1 ∧ inner ℝ x v = 0 ∧
        Real.sqrt (((n : ℝ) - 1) / (n + 1)) ≤ normalCurvature f x v := by
  sorry

end OMA.S_mo_445819
