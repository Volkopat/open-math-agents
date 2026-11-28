import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Periodic

/-!
The question asks whether the complexification of a real planar polynomial
vector field can have a nonempty compact invariant set containing neither
an equilibrium nor a periodic orbit.

Source: https://mathoverflow.net/questions/255238
-/

namespace OMA.S_mo_255238

noncomputable def complexEval (P : MvPolynomial (Fin 2) ℝ) (z : ℂ × ℂ) : ℂ :=
  MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun i => if i = 0 then z.1 else z.2) P

def IsTrajectory (P Q : MvPolynomial (Fin 2) ℝ) (u : ℝ → ℂ × ℂ) : Prop :=
  ∀ t : ℝ, HasDerivAt (fun s => (u s).1) (complexEval P (u t)) t ∧
    HasDerivAt (fun s => (u s).2) (complexEval Q (u t)) t

theorem main :
    ∃ (P Q : MvPolynomial (Fin 2) ℝ) (K : Set (ℂ × ℂ)),
      K.Nonempty ∧ IsCompact K ∧
      (∀ z ∈ K, ∃ u : ℝ → ℂ × ℂ, u 0 = z ∧ IsTrajectory P Q u ∧ ∀ t, u t ∈ K) ∧
      (∀ z ∈ K, complexEval P z ≠ 0 ∨ complexEval Q z ≠ 0) ∧
      (∀ u : ℝ → ℂ × ℂ, IsTrajectory P Q u → (∀ t, u t ∈ K) →
        ¬ ∃ τ : ℝ, 0 < τ ∧ Function.Periodic u τ) := by
  sorry

end OMA.S_mo_255238
