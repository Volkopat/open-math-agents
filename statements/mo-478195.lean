import Mathlib

/-!
# Dependence of the nearest point on a compact convex set

Source: Justthisguy, https://mathoverflow.net/questions/478195 (CC BY-SA 4.0).
Credit: @connoranderson. We identify the Euclidean plane with the complex plane
as a real inner product space. With a uniform positive diameter bound, the
square-root modulus still cannot be improved to a Lipschitz bound.
-/

namespace OMA.S_mo_478195
open Set Metric
def Nearest {E : Type*} [Norm E] (K : Set E) (p : E) : Prop :=
  p ∈ K ∧ ∀ z ∈ K, ‖p‖ ≤ ‖z‖
def Body (K : Set ℂ) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ K ⊆ ball 0 1 ∧ (1/2 : ℝ) ≤ diam K

theorem main :
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K L : Set E)
      (p q : E), IsCompact K → IsCompact L → Convex ℝ K → Convex ℝ L →
      Nearest K p → Nearest L q →
      dist p q ^2 ≤ (‖p‖+‖q‖)*hausdorffDist K L) ∧
    (∀ t : ℝ, 0<t → t<1/4 → ∃ (K L : Set ℂ) (p q : ℂ), Body K ∧ Body L ∧
      Nearest K p ∧ Nearest L q ∧ hausdorffDist K L ≤ 4*t^2 ∧ t ≤ dist p q) ∧
    (∀ C : ℝ, 0≤C → ∃ (K L : Set ℂ) (p q : ℂ), Body K ∧ Body L ∧ Nearest K p ∧
      Nearest L q ∧ C * hausdorffDist K L < dist p q) := by
  sorry
end OMA.S_mo_478195
