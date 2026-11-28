import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

namespace OMA.S_mo_354118

universe u

/-- Supremum of the absolute value of the polynomial on the open unit disk. -/
noncomputable def diskSup (p : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, ‖z‖ < 1 ∧ r = ‖p.eval z‖}

/-- A Banach space isomorphic to a Hilbert space can fail the weak von Neumann bound. -/
theorem main :
    ∃ (E H : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
      (_ : CompleteSpace E) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H),
      Nonempty (E ≃L[ℂ] H) ∧
        ∀ C : ℝ, 0 < C →
          ∃ (T : E →L[ℂ] E) (p : Polynomial ℂ),
            ‖T‖ ≤ 1 ∧ C * diskSup p < ‖Polynomial.aeval T p‖ := by
  sorry

end OMA.S_mo_354118
