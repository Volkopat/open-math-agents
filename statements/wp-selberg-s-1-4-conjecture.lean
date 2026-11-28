import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

namespace OMA.S_wp_selberg_s_1_4_conjecture

open MeasureTheory
open scoped ContDiff MatrixGroups UpperHalfPlane

/-- A positive Laplace eigenvalue on the hyperbolic quotient by a congruence subgroup
is at least one quarter. Square integrability is checked on modular-domain translates. -/
theorem main :
    ∀ (Γ : Subgroup SL(2, ℤ)), CongruenceSubgroup.IsCongruenceSubgroup Γ →
    ∀ (f : ℂ → ℂ) (eigenvalue : ℝ), 0 < eigenvalue →
      ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} →
      (∃ z : ℍ, f (z : ℂ) ≠ 0) →
      (∀ (g : Γ) (z : ℍ), f (((g : SL(2, ℤ)) • z : ℍ) : ℂ) = f (z : ℂ)) →
      (∀ g : SL(2, ℤ),
        IntegrableOn (fun z : ℍ => ‖f ((g • z : ℍ) : ℂ)‖ ^ 2) ModularGroup.fd) →
      (∀ z : ℍ, (-(z.im ^ 2)) • Laplacian.laplacian f (z : ℂ) = eigenvalue • f (z : ℂ)) →
      1 / 4 ≤ eigenvalue := by
  sorry

end OMA.S_wp_selberg_s_1_4_conjecture
