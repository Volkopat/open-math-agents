import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# On the upper bound for the real part of the logarithmic derivative of a polynomial

Source: https://mathoverflow.net/questions/371077
Question by user159888, licensed CC BY-SA 4.0.
Credit: @etaubman

A nonzero polynomial has degree n = natDegree, with a₀ = coeff 0 and
aₙ = leadingCoeff. The source's maximum condition is written as an upper
bound on the unit circle together with attainment of the value 1.
-/

namespace OMA.S_mo_371077

open Polynomial

noncomputable def Normalized (p : ℂ[X]) : Prop :=
  (∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ 1) ∧
    (∃ z : ℂ, ‖z‖ = 1 ∧ ‖p.eval z‖ = 1)

theorem main :
    ∀ (p : ℂ[X]), p ≠ 0 → Normalized p →
      ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0 →
        (z * p.derivative.eval z / p.eval z).re ≤
          (p.natDegree : ℝ) -
            (1 + ‖p.coeff 0‖ - ‖p.leadingCoeff‖) /
              (1 + ‖p.coeff 0‖ + ‖p.leadingCoeff‖) := by
  sorry

end OMA.S_mo_371077
