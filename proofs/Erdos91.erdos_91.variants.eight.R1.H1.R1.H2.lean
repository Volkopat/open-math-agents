import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1_H1_R1
import Mathlib

/-!
# Intersecting circles in the Euclidean plane

Subtracting the squared-distance equations places every common point on a
line perpendicular to the difference of the centres. A line through a point
of a circle contains at most one further point of that circle.
-/

namespace OMA.TwoCircles

open EuclideanGeometry InnerProductSpace Finset

theorem solution (p q : ℝ²) (r d : ℝ) (hne : p ≠ q) (W : Finset ℝ²)
    (hW : ∀ w ∈ W, dist p w = r ∧ dist q w = d) :
    W.card ≤ 2 := by
  classical
  by_cases hn : W.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp hn]
  obtain ⟨a,ha⟩ := hn
  let L : Submodule ℝ ℝ² := (ℝ ∙ (q-p))ᗮ
  have hDim : Module.finrank ℝ L = 1 := by
    have hs := (ℝ ∙ (q-p)).finrank_add_finrank_orthogonal
    have hSub : q-p ≠ 0 := sub_ne_zero.mpr hne.symm
    rw [finrank_span_singleton hSub] at hs
    have hd : Module.finrank ℝ ℝ² = 2 := by simp
    change 1 + Module.finrank ℝ L = _ at hs
    omega
  have hneL : L ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hDim
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hneL
  have he : ℝ ∙ v = L := by
    apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv))
    rw [finrank_span_singleton hv0, hDim]
  have hOrth (x : ℝ²) (hx : x ∈ W) : x-a ∈ L := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have hp : (dist p x)^2 = (dist p a)^2 := by rw [(hW x hx).1, (hW a ha).1]
    have hq : (dist q x)^2 = (dist q a)^2 := by rw [(hW x hx).2, (hW a ha).2]
    simp only [dist_eq_norm, norm_sub_sq_real] at hp hq
    simp only [inner_sub_left, inner_sub_right]
    linarith
  let S : EuclideanGeometry.Sphere ℝ² := ⟨p,r⟩
  have hs (x : ℝ²) (hx : x ∈ W) : x ∈ S := by
    change dist x p = r
    rw [dist_comm]
    exact (hW x hx).1
  have hSub : W ⊆ {a, S.secondInter a v} := by
    intro x hx
    have hLine : x ∈ AffineSubspace.mk' a (ℝ ∙ v) := by
      rw [AffineSubspace.mem_mk', he]
      exact hOrth x hx
    have h := (Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem (hs a ha) hLine).mpr (hs x hx)
    exact mem_insert.mpr (h.imp_right mem_singleton.mpr)
  exact (card_le_card hSub).trans card_le_two

end OMA.TwoCircles

theorem OMA.solution : OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1.H2 :=
  OMA.TwoCircles.solution
