import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1
import Mathlib

-- Credit: @marcusbuffett

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1_H2_R1

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap unitInterval Topology
open Metric ContinuousMap
open Set

private theorem nearHomotopy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : (Metric.sphere (0 : V) 1) → (Metric.sphere (0 : V) 1)) (hg : Continuous g) (near : ∀ y, dist (g y) y < 1) :
    ∃ H : C(I × (Metric.sphere (0 : V) 1),(Metric.sphere (0 : V) 1)), (∀ y,H (0,y) = g y) ∧ ∀ y,H (1,y) = y := by
  let v (p : I × (Metric.sphere (0 : V) 1)) : V := (p.2 : V) + (1 - p.1.val) • ((g p.2 : V) - p.2)
  have hv : Continuous v := continuous_subtype_val.comp continuous_snd |>.add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (((continuous_subtype_val.comp hg).comp continuous_snd).sub (continuous_subtype_val.comp continuous_snd)))
  have unit (y : (Metric.sphere (0 : V) 1)) : ‖(y : V)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
  have nz (p : I × (Metric.sphere (0 : V) 1)) : v p ≠ 0 := by
    intro hz
    have len : ‖((g p.2 : V) - (p.2 : V))‖ < 1 := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using near p.2
    have h : ‖(1 - p.1.val) • ((g p.2 : V) - (p.2 : V))‖ < 1 := by
      rw [norm_smul,Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.1.property.2)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [p.1.property.1])).trans_lt len
    have heq : (1 - p.1.val) • ((g p.2 : V) - (p.2 : V)) = -(p.2 : V) :=
      eq_neg_of_add_eq_zero_right hz
    rw [heq,norm_neg,unit] at h
    exact (lt_irrefl _ h)
  let F (p : I × (Metric.sphere (0 : V) 1)) : (Metric.sphere (0 : V) 1) := ⟨‖v p‖⁻¹ • v p, by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (nz p))]⟩
  have hc : Continuous F := ((hv.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (nz p))).smul hv).subtype_mk _
  refine ⟨⟨F,hc⟩, ?_, ?_⟩ <;> intro y <;> apply Subtype.ext <;> simp [F,v,unit]

/-- The smoothing input: approximate the given topological parametrization within
unit chordal distance by a smooth map regular in a neighborhood of every point. -/
def H1 : Prop :=
  let S := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SecondCountableTopology M] (e : M ≃ₜ S),
    ∃ f : M → S, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f ∧ ∀ x, dist (f x) (e x) < 1

/-- A covering with connected total space and a homotopy section has one sheet. -/
def H2 : Prop :=
  ∀ (E Y : Type) [TopologicalSpace E] [TopologicalSpace Y] [PreconnectedSpace E] [Nonempty Y]
    (f : E → Y), IsCoveringMap f → ∀ (s₀ : C(Y,E)) (H : C(I × Y,Y)),
    (∀ y, H (0,y) = f (s₀ y)) → (∀ y, H (1,y) = y) → Function.Bijective f


theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1.H2 := by
  intro approx covering M _ _ _ _ _ _ e
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  have rankGt : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  let _ : ConnectedSpace S := isConnected_iff_connectedSpace.mp
    (isConnected_sphere rankGt 0 (by norm_num : (0:ℝ) ≤ 1))
  let _ : ConnectedSpace M := e.connectedSpace_iff.mpr inferInstance
  obtain ⟨f,hf,hnear⟩ := approx M e
  let g : S → S := f ∘ e.symm
  have hg : Continuous g := hf.isLocalHomeomorph.continuous.comp e.symm.continuous
  obtain ⟨H,h₀,h₁⟩ := nearHomotopy g hg (fun y => by simpa [g] using hnear (e.symm y))
  have hcov : IsCoveringMap f := isLocalHomeomorph_iff_isCoveringMap.mp hf.isLocalHomeomorph
  exact ⟨hf.diffeomorphOfBijective (covering M S f hcov ⟨e.symm,e.symm.continuous⟩ H h₀ h₁)⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_for_three_R1_H2_R1
