import Mathlib

/-! Source: https://mathoverflow.net/questions/119813 -/

open Set

namespace OMA.S_mo_119813

/-- Smooth averaging weights supported on the unit time interval and normalized to mass one. -/
def IsAveragingWeight (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ ∧ Function.support φ ⊆ Icc 0 1 ∧ (∫ t in (0 : ℝ)..1, φ t) = 1

def SolvesODE {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E → E) (x : ℝ → E) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x (v (x t)) (Icc 0 1) t

/-- The proposed existence of a single weight that determines every trajectory
of a given smooth autonomous vector field on the unit time interval. -/
theorem main : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : E → E),
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) v →
    ∃ φ : ℝ → ℝ, IsAveragingWeight φ ∧
      ∀ (x y : ℝ → E), SolvesODE v x → SolvesODE v y →
        (∫ t in (0 : ℝ)..1, φ t • x t) = (∫ t in (0 : ℝ)..1, φ t • y t) →
        EqOn x y (Icc 0 1) := by
  sorry

end OMA.S_mo_119813
