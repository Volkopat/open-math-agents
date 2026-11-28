import Mathlib

/-!
# Second duals of Grothendieck spaces

Source: https://mathoverflow.net/questions/149326 (asked by Diestel, 1973)
Is the second dual of a Grothendieck space again a Grothendieck space? `main` states the
affirmative answer.

Conventions. A real Banach space `X` is a Grothendieck space when every weak-* convergent
sequence in `X*` converges weakly, i.e. if `φₙ x → φ x` for all `x ∈ X` then `ψ φₙ → ψ φ`
for all `ψ ∈ X**`. Duals are spaces of continuous linear functionals `X →L[ℝ] ℝ`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_149326

open Filter Topology

/-- `X` is a Grothendieck space. -/
def IsGrothendieck (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (φ : ℕ → (X →L[ℝ] ℝ)) (φ₀ : (X →L[ℝ] ℝ)),
    (∀ x : X, Tendsto (fun n => φ n x) atTop (𝓝 (φ₀ x))) →
    ∀ ψ : ((X →L[ℝ] ℝ) →L[ℝ] ℝ), Tendsto (fun n => ψ (φ n)) atTop (𝓝 (ψ φ₀))

theorem main :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
      IsGrothendieck X → IsGrothendieck (((X →L[ℝ] ℝ) →L[ℝ] ℝ)) := by
  sorry

end OMA.S_mo_149326
