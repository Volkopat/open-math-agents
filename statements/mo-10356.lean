import Mathlib

/-!
# Topological "interpolation"?

Source: https://mathoverflow.net/questions/10356
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: let `E` be a normed space and `T : E* → E*` a (nonlinear) map which is continuous for
the norm topology and continuous for the weak-* topology. Must `T` be continuous for the weak
topology? The question is yes/no; `main` states the answer yes.

Conventions: real scalars; `E* = E →L[ℝ] ℝ` with its norm topology. The weak-* topology is the
topology induced by the evaluations `φ ↦ φ x` (`x ∈ E`), and the weak topology is the topology
induced by all norm-continuous linear functionals `ℓ : E** = E* →L[ℝ] ℝ`, `φ ↦ ℓ φ`. Continuity
"from `(E*, τ)` to itself" uses `τ` on both sides.
-/

namespace OMA.S_mo_10356

/-- The weak-* topology on `E*`. -/
noncomputable def weakStar (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (E →L[ℝ] ℝ) :=
  TopologicalSpace.induced (fun φ : E →L[ℝ] ℝ => fun x : E => φ x) inferInstance

/-- The weak topology on `E*`. -/
noncomputable def weak (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (E →L[ℝ] ℝ) :=
  TopologicalSpace.induced
    (fun φ : E →L[ℝ] ℝ => fun ℓ : (E →L[ℝ] ℝ) →L[ℝ] ℝ => ℓ φ) inferInstance

theorem main :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (T : (E →L[ℝ] ℝ) → (E →L[ℝ] ℝ)),
      Continuous T → @Continuous _ _ (weakStar E) (weakStar E) T →
        @Continuous _ _ (weak E) (weak E) T := by
  sorry

end OMA.S_mo_10356
