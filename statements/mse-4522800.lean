import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic
/-!
# Uniform ball and closure formulations of the open mapping theorem

Source: https://math.stackexchange.com/questions/4522800/another-generalization-of-open-mapping-theorem
Credit: @etaubman

All three conditions in the source are equivalent. They quantify over every
center and every positive radius. The field assumptions cover real and complex
Banach spaces, as well as other nontrivially normed fields.
-/

namespace OMA.S_mse_4522800

open Function Metric Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

def uniformBallImage (T : E →L[𝕜] F) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ x : E, ∀ ε : ℝ, 0 < ε →
    ball (T x) (r * ε) ⊆ T '' ball x ε

def uniformBallClosure (T : E →L[𝕜] F) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ x : E, ∀ ε : ℝ, 0 < ε →
    ball (T x) (r * ε) ⊆ closure (T '' ball x ε)

theorem main : ∀ (T : E →L[𝕜] F),
    (Surjective T ↔ uniformBallImage T) ∧
    (Surjective T ↔ uniformBallClosure T) := by
  sorry

end OMA.S_mse_4522800
