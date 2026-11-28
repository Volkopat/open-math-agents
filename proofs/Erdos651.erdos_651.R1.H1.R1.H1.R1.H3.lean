import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1_H1_R1
import Mathlib

/-!
# Generic orthant perturbation by continuity

The positive-basis construction and projection argument follow
@justusklocke-cloud's PR24481. This version uses continuity of matrix inversion
and finite intersections of dense open sets in place of explicit norm bounds.
-/

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace Erdos651Stability
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma stable {α : Type*} (U : Finset α) (v : α → n → ℝ)
    (hU : ∀ u ∈ U, ∀ i, v u i < 0) :
    ∃ S : Set (Matrix n n ℝ), IsOpen S ∧ (1 : Matrix n n ℝ) ∈ S ∧
      ∀ M ∈ S, IsUnit M.det ∧ ∀ u ∈ U, ∀ i, (M⁻¹ *ᵥ v u) i < 0 := by
  have hi : ContinuousAt (fun M : Matrix n n ℝ => M⁻¹) 1 := by
    apply continuousAt_matrix_inv
    simpa only [Matrix.det_one, Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  have hd : ∀ᶠ M : Matrix n n ℝ in 𝓝 1, IsUnit M.det := by
    have h := (isOpen_ne.preimage continuous_id.matrix_det).mem_nhds
      (show (1 : Matrix n n ℝ).det ≠ 0 by simp)
    filter_upwards [h] with M hM
    exact isUnit_iff_ne_zero.mpr hM
  have hu : ∀ u ∈ U, ∀ i, ∀ᶠ M : Matrix n n ℝ in 𝓝 1,
      (M⁻¹ *ᵥ v u) i < 0 := by
    intro u hu i
    have hc : ContinuousAt (fun M : Matrix n n ℝ => (M⁻¹ *ᵥ v u) i) 1 :=
      ((continuous_apply i).comp
        (continuous_id.matrix_mulVec (continuous_const (y := v u)))).continuousAt.comp hi
    exact hc.eventually_lt_const (by simpa using hU u hu i)
  have hvec : ∀ᶠ M : Matrix n n ℝ in 𝓝 1, ∀ u ∈ U, ∀ i, (M⁻¹ *ᵥ v u) i < 0 := by
    simpa only [Filter.eventually_all_finset, Filter.eventually_all] using hu
  obtain ⟨S, hS, hopen, hmem⟩ := mem_nhds_iff.mp (hd.and hvec)
  exact ⟨S, hopen, hmem, fun M hM => hS hM⟩

lemma choose_matrix {a : Type*} [Finite a]
    (L : n → a → Submodule ℝ (n → ℝ)) (hL : ∀ j k, L j k ≠ ⊤)
    {S : Set (Matrix n n ℝ)} (hS : IsOpen S) (hI : (1 : Matrix n n ℝ) ∈ S) :
    ∃ M ∈ S, (∀ i j, 0 < M i j) ∧ ∀ j k, (fun i => M i j) ∉ L j k := by
  let path (t : ℝ) : Matrix n n ℝ := 1 + t • (fun _ _ => 1)
  have hc : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  have hz : path 0 = 1 := by
    ext i j
    change (1 : Matrix n n ℝ) i j + (0 : ℝ) * 1 = (1 : Matrix n n ℝ) i j
    ring
  have ht : Tendsto path (𝓝 (0 : ℝ)) (𝓝 (1 : Matrix n n ℝ)) := by
    simpa only [hz] using hc.tendsto 0
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), path t ∈ S :=
    nhdsWithin_le_nhds (ht (hS.mem_nhds hI))
  obtain ⟨t, hmem, hpos⟩ := (hm.and self_mem_nhdsWithin).exists
  have hpositive : ∀ i j, 0 < path t i j := by
    intro i j
    change 0 < (1 : Matrix n n ℝ) i j + t * 1
    have hn : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    simpa only [mul_one] using add_pos_of_nonneg_of_pos hn hpos
  let col (j : n) : Matrix n n ℝ →ₗ[ℝ] (n → ℝ) :=
    { toFun := fun M i => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let bad (p : n × a) : Submodule ℝ (Matrix n n ℝ) := (L p.1 p.2).comap (col p.1)
  have proper (p : n × a) : bad p ≠ ⊤ := by
    intro h
    apply hL p.1 p.2
    apply top_unique
    intro v _
    have hv : (fun i _ => v i) ∈ bad p := by rw [h]; trivial
    exact hv
  letI : BaireSpace (Matrix n n ℝ) := inferInstanceAs (BaireSpace (n → n → ℝ))
  have hd : Dense (⋂ p, ((bad p : Set (Matrix n n ℝ))ᶜ)) :=
    dense_iInter_of_isOpen
      (fun p => (bad p).closed_of_finiteDimensional.isOpen_compl) (fun p => by
        apply interior_eq_empty_iff_dense_compl.mp
        exact Set.not_nonempty_iff_eq_empty.mp
          (fun h => proper p ((bad p).eq_top_of_nonempty_interior' h)))
  obtain ⟨M, ⟨hMS, hMp⟩, hav⟩ := hd.inter_open_nonempty
    {M ∈ S | ∀ i j, 0 < M i j} (hS.inter isOpen_Ioi.matrix) ⟨path t, hmem, hpositive⟩
  exact ⟨M, hMS, hMp, fun j k => Set.mem_iInter.mp hav (j, k)⟩

end Erdos651Stability

namespace Erdos651MatrixBridge
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def inversePiEquiv (M : Matrix n n ℝ) (hM : IsUnit M.det) :
    (n → ℝ) ≃ₗ[ℝ] (n → ℝ) where
  __ := M⁻¹.mulVecLin
  invFun := M.mulVec
  left_inv x := by
    change M *ᵥ (M⁻¹ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  right_inv x := by
    change M⁻¹ *ᵥ (M *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]

noncomputable def inverseEuclideanEquiv (M : Matrix n n ℝ) (hM : IsUnit M.det) :
    EuclideanSpace ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ n :=
  (WithLp.linearEquiv 2 ℝ (n → ℝ)).trans
    ((inversePiEquiv M hM).trans (WithLp.linearEquiv 2 ℝ (n → ℝ)).symm)

noncomputable def shrink (M : Matrix n n ℝ) (hM : IsUnit M.det)
    (e : EuclideanSpace ℝ n ≃ᵃ[ℝ] EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n ≃ᵃ[ℝ] EuclideanSpace ℝ n :=
  e.trans (inverseEuclideanEquiv M hM).toAffineEquiv

lemma shrink_apply (M : Matrix n n ℝ) (hM : IsUnit M.det)
    (e : EuclideanSpace ℝ n ≃ᵃ[ℝ] EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ n) (i : n) :
    shrink M hM e x i = (M⁻¹ *ᵥ (fun j => e x j)) i := rfl

lemma exists_shrink_with_generic_columns {a : Type*} [Finite a]
    (U : Finset (EuclideanSpace ℝ n))
    (e : EuclideanSpace ℝ n ≃ᵃ[ℝ] EuclideanSpace ℝ n)
    (hU : ∀ u ∈ U, ∀ i, e u i < 0)
    (L : n → a → Submodule ℝ (n → ℝ)) (hL : ∀ j k, L j k ≠ ⊤) :
    ∃ M : Matrix n n ℝ, ∃ hM : IsUnit M.det,
      (∀ i j, 0 < M i j) ∧ (∀ j k, (fun i => M i j) ∉ L j k) ∧
      (∀ u ∈ U, ∀ i, shrink M hM e u i ≤ 0) ∧
      {x | ∀ i, shrink M hM e x i ≤ 0} ⊆ {x | ∀ i, e x i ≤ 0} := by
  obtain ⟨S, hS, hI, hstable⟩ := Erdos651Stability.stable U (fun u i => e u i) hU
  obtain ⟨M, hM, hpos, hav⟩ := Erdos651Stability.choose_matrix L hL hS hI
  have hdet := (hstable M hM).1
  refine ⟨M, hdet, hpos, hav, fun u hu i => ((hstable M hM).2 u hu i).le, ?_⟩
  intro x hx i
  have he : M *ᵥ (fun j => shrink M hdet e x j) = (fun j => e x j) := by
    simp only [shrink_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet,
      Matrix.one_mulVec]
  rw [← congrFun he i]
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hpos i j).le (hx j))

end Erdos651MatrixBridge


namespace Erdos651Avoidance

theorem vectorSpan_range_three_ne_top
    {ι : Type*} [Fintype ι] (p : ι → Fin 3 → ℝ) (hc : Fintype.card ι ≤ 3) :
    vectorSpan ℝ (Set.range p) ≠ ⊤ := by
  intro ht
  rcases isEmpty_or_nonempty ι with hi | hi
  · have hr : Set.range p = ∅ := by simpa using hi
    rw [hr, vectorSpan_empty] at ht
    exact bot_ne_top ht
  · have h := finrank_vectorSpan_range_add_one_le ℝ p
    rw [ht] at h
    simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
    omega

end Erdos651Avoidance


open Matrix
namespace Erdos651Projection

noncomputable def deleteAfterInverse {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (j : Fin (n+1)) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (LinearMap.funLeft ℝ ℝ j.succAbove).comp (M⁻¹).mulVecLin

/-- The vectorSpan reindexing follows the checked projection argument in PR #24481. -/
theorem affineIndependent_deleteAfterInverse {n : ℕ} {ι : Type*}
    {p : ι → Fin (n+1) → ℝ} (hp : AffineIndependent ℝ p)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : IsUnit M.det) (j : Fin (n+1))
    (hcol : (fun i => M i j) ∉ vectorSpan ℝ (Set.range p)) :
    AffineIndependent ℝ (deleteAfterInverse M j ∘ p) := by
  let F := deleteAfterInverse M j
  have hd : Disjoint (vectorSpan ℝ (Set.range p)) (LinearMap.ker F) := by
    apply (Submodule.disjoint_span_singleton_of_notMem hcol).mono_right
    intro x hx
    let w := M⁻¹ *ᵥ x
    have hw (s : Fin n) : w (j.succAbove s) = 0 :=
      congrFun (LinearMap.mem_ker.mp hx) s
    have hs : w = Pi.single j (w j) := by
      ext i
      by_cases hi : i = j
      · subst i; simp
      · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hi
        simpa using hw s
    refine Submodule.mem_span_singleton.mpr ⟨w j, ?_⟩
    calc
      _ = M *ᵥ w := by rw [hs]; ext i; simp [mul_comm]
      _ = x := by
        dsimp [w]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  rcases isEmpty_or_nonempty ι with h | h
  · exact affineIndependent_of_subsingleton ℝ _
  obtain ⟨i⟩ := h
  rw [vectorSpan_range_eq_span_range_vsub_right_ne ℝ p i] at hd
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p i] at hp
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (deleteAfterInverse M j ∘ p) i]
  simpa only [Function.comp_def, vsub_eq_sub, map_sub] using hp.map hd

end Erdos651Projection

open scoped EuclideanGeometry
open Erdos651Avoidance Erdos651Projection Erdos651MatrixBridge

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1.H3 := by
  classical
  intro Y U e hY hU
  let F := Y.powerset.filter (fun Z => Z.card ≤ 3)
  let L (_j : Fin 3) (Z : ↥F) : Submodule ℝ (Fin 3 → ℝ) :=
    vectorSpan ℝ (Set.range (fun z : ↥Z.val => fun i => e z i))
  have hL (j : Fin 3) (Z : ↥F) : L j Z ≠ ⊤ :=
    vectorSpan_range_three_ne_top _ (by simpa using (Finset.mem_filter.mp Z.property).2)
  obtain ⟨M, hM, _, hcol, hint, hsub⟩ :=
    exists_shrink_with_generic_columns U e hU L hL
  refine ⟨shrink M hM e, hint, hsub, ?_⟩
  intro j Z hZY hZ
  have hav := hcol j ⟨Z, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hZY, hZ⟩⟩
  have hind : AffineIndependent ℝ
      (fun z : ↥(Z : Set (ℝ^3)) => fun i => e z i) :=
    (e.trans (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toAffineEquiv).affineIndependent_iff.mpr
      (hY Z hZY (by omega))
  exact affineIndependent_deleteAfterInverse hind M hM j hav

