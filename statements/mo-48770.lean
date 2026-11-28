import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A Lipschitz supremum bound on Hausdorff-convergent compact domains

Source: https://mathoverflow.net/questions/48770/controlling-the-lipschitz-norm-of-the-limit-of-a-sequence-of-functions
Question author: Tom LaGatta, 9 December 2010.

The extended nonnegative supremum is used so that the expression is defined even for
continuous functions that are not Lipschitz. At finite nonnegative bounds it is exactly
the maximum of the supremum norm and the Lipschitz constant.
-/

open Filter Topology Set Metric
open scoped ENNReal

namespace OMA.S_mo_48770

noncomputable def lipschitzSupNorm {X : Type*} [MetricSpace X] (s : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ s, ENNReal.ofReal |f x|) ⊔
    (⨆ x ∈ s, ⨆ y ∈ s, ENNReal.ofReal (|f x - f y| / dist x y))


theorem main : ∀ (d : ℕ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (Dseq : ℕ → Set (EuclideanSpace ℝ (Fin d)))
    (F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℝ) (h0 : 0 ≤ h) (hD : IsCompact D) (hK : ∀ n, IsCompact (Dseq n))
    (hFcont : ∀ n, Continuous (F n)) (hf : Continuous f)
    (hHaus : Tendsto (fun n ↦ hausdorffEDist (Dseq n) D) atTop (𝓝 0))
    (hF : ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      Tendsto (fun n ↦ lipschitzSupNorm K (fun x ↦ F n x - f x)) atTop (𝓝 0))
    (hBounds : ∀ n, lipschitzSupNorm (Dseq n) (F n) ≤ ENNReal.ofReal h),
    lipschitzSupNorm D f ≤ ENNReal.ofReal h := by
  sorry

end OMA.S_mo_48770
