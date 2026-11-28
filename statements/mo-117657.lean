import Mathlib

/-! Source: https://mathoverflow.net/questions/117657 -/

open Real Set

namespace OMA.S_mo_117657

noncomputable def speed (x y : ℝ → ℝ) (t : ℝ) :=
  √((deriv x t)^2 + (deriv y t)^2)

noncomputable def absCurvature (x y : ℝ → ℝ) (t : ℝ) :=
  |deriv x t * deriv (deriv y) t - deriv y t * deriv (deriv x) t| / (speed x y t)^3

noncomputable def curveLength (x y : ℝ → ℝ) :=
  ∫ t in (0 : ℝ)..2 * π, speed x y t

noncomputable def totalAbsCurvature (x y : ℝ → ℝ) :=
  ∫ t in (0 : ℝ)..2 * π, absCurvature x y t * speed x y t

noncomputable def curvatureVariation (x y : ℝ → ℝ) :=
  ∫ t in (0 : ℝ)..2 * π, |deriv (absCurvature x y) t|

noncomputable def enclosedArea (x y : ℝ → ℝ) :=
  |∫ t in (0 : ℝ)..2 * π, x t * deriv y t - y t * deriv x t| / 2

/-- A smooth regular simple closed plane curve, parameterized with period 2π. -/
def SmoothSimpleClosed (x y : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ENat) : WithTop ENat) x ∧ ContDiff ℝ ((⊤ : ENat) : WithTop ENat) y ∧
  Function.Periodic x (2 * π) ∧ Function.Periodic y (2 * π) ∧
  (∀ t, 0 < speed x y t) ∧
  InjOn (fun t => (x t, y t)) (Ico 0 (2 * π))

/-- The proposed monotone comparison of enclosed area with variation of
absolute curvature for smooth simple closed curves of equal length and
equal total absolute curvature. The curvature variation integral uses the
periodic parameter, since ∫|dκ/dt| dt = ∫|dκ/ds| ds for arc length s. -/
theorem main : ∀ (x y x' y' : ℝ → ℝ),
    SmoothSimpleClosed x y → SmoothSimpleClosed x' y' →
    curveLength x y = curveLength x' y' →
    totalAbsCurvature x y = totalAbsCurvature x' y' →
    curvatureVariation x' y' ≤ curvatureVariation x y →
    enclosedArea x y ≤ enclosedArea x' y' := by
  sorry

end OMA.S_mo_117657
