import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1_H2_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1: hypothesis H1 of reduction PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1.H2.R1.H1.R1.H2.R1
-- Credit: @ZenimXD

open Geometry Set Filter Metric ContinuousLinearMap
open scoped Topology unitInterval

namespace PoincareH1

variable {m : ℕ}

private abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

private noncomputable def closedStar (K : SimplicialComplex ℝ (E m)) (s : Finset (E m)) : Set (E m) :=
  letI : DecidableEq (E m) := Classical.decEq (E m)
  ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set (E m))

private def transGrass (K : SimplicialComplex ℝ (E m)) (s : Finset (E m)) : Type :=
  {P : Submodule ℝ (E m) //
    Module.finrank ℝ P + 3 = m ∧
    ∀ x ∈ closedStar K s, ∀ y ∈ closedStar K s, x - y ∈ P → x = y}

private noncomputable def transGrassTopo (K : SimplicialComplex ℝ (E m)) (s : Finset (E m)) :
    TopologicalSpace (transGrass K s) :=
  TopologicalSpace.induced (fun P : transGrass K s => P.val.starProjection) inferInstance

private def skel (K : SimplicialComplex ℝ (E m)) (k : ℕ) : Set (E m) :=
  ⋃ s ∈ {s | s ∈ K.faces ∧ s.card ≤ k}, convexHull ℝ (s : Set (E m))

private lemma closedStar_anti (K : SimplicialComplex ℝ (E m)) {s₁ s₂ : Finset (E m)}
    (hs : s₁ ⊆ s₂) : closedStar K s₂ ⊆ closedStar K s₁ := by
  letI : DecidableEq (E m) := Classical.decEq (E m)
  intro x hx
  simp only [closedStar, mem_iUnion, mem_setOf_eq] at hx ⊢
  rcases hx with ⟨t, ⟨ht, hs₂t⟩, hxt⟩
  have hsub : s₁ ∪ t ⊆ s₂ ∪ t := Finset.union_subset_union_left hs
  have hne : (s₁ ∪ t).Nonempty := (K.nonempty_of_mem_faces ht).mono Finset.subset_union_right
  exact ⟨t, ⟨ht, K.down_closed hs₂t hsub hne⟩, hxt⟩

private lemma transGrass_mono (K : SimplicialComplex ℝ (E m)) {s₁ s₂ : Finset (E m)}
    (hs : s₁ ⊆ s₂) {P : Submodule ℝ (E m)}
    (hdim : Module.finrank ℝ P + 3 = m)
    (hsec : ∀ x ∈ closedStar K s₁, ∀ y ∈ closedStar K s₁, x - y ∈ P → x = y) :
    ∀ x ∈ closedStar K s₂, ∀ y ∈ closedStar K s₂, x - y ∈ P → x = y := by
  intro x hx y hy hxy
  exact hsec x (closedStar_anti K hs hx) y (closedStar_anti K hs hy) hxy

private lemma isCompact_convexHull_finset (s : Finset (E m)) :
    IsCompact (convexHull ℝ (s : Set (E m))) :=
  (Finset.finite_toSet s).isCompact_convexHull ℝ

private lemma isCompact_skel (K : SimplicialComplex ℝ (E m)) (hfin : K.faces.Finite) (k : ℕ) :
    IsCompact (skel K k) := by
  have hsub : ({s | s ∈ K.faces ∧ s.card ≤ k} : Set (Finset (E m))).Finite :=
    hfin.subset (fun _ hs => hs.1)
  exact hsub.isCompact_biUnion (fun s _ => isCompact_convexHull_finset s)

private lemma isClosed_skel (K : SimplicialComplex ℝ (E m)) (hfin : K.faces.Finite) (k : ℕ) :
    IsClosed (skel K k) :=
  (isCompact_skel K hfin k).isClosed

private lemma skel_mono (K : SimplicialComplex ℝ (E m)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    skel K k₁ ⊆ skel K k₂ := by
  intro x hx
  simp only [skel, mem_iUnion, mem_setOf_eq] at hx ⊢
  rcases hx with ⟨s, ⟨hs, hcard⟩, hxs⟩
  exact ⟨s, ⟨hs, le_trans hcard hk⟩, hxs⟩

private lemma skel_four_eq_space (K : SimplicialComplex ℝ (E m))
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) :
    skel K 4 = K.space := by
  ext x
  simp only [skel, SimplicialComplex.mem_space_iff, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨s, ⟨hs, _⟩, hxs⟩
    exact ⟨s, hs, hxs⟩
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨t, _, hst, ht4⟩ := hpure s hs
    exact ⟨s, ⟨hs, ht4 ▸ Finset.card_le_card hst⟩, hxs⟩

private lemma convexHull_inter_skel_of_card (K : SimplicialComplex ℝ (E m))
    {s : Finset (E m)} (hs : s ∈ K.faces) (k : ℕ) :
    ∀ x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k,
      ∃ r : Finset (E m), r ∈ K.faces ∧ r ⊆ s ∧ r.card ≤ k ∧ x ∈ convexHull ℝ (r : Set (E m)) := by
  classical
  rintro x ⟨hxs, hxsk⟩
  simp only [skel, mem_iUnion, mem_setOf_eq] at hxsk
  rcases hxsk with ⟨t, ⟨ht, htcard⟩, hxt⟩
  have hinter : x ∈ convexHull ℝ ((s ∩ t : Finset (E m)) : Set (E m)) := by
    have h1 : x ∈ convexHull ℝ (s : Set (E m)) ∩ convexHull ℝ (t : Set (E m)) := ⟨hxs, hxt⟩
    rw [K.convexHull_inter_convexHull hs ht] at h1
    simpa [Finset.coe_inter] using h1
  have hne : (s ∩ t).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hinter
  refine ⟨s ∩ t, K.down_closed hs Finset.inter_subset_left hne,
    Finset.inter_subset_left, le_trans (Finset.card_le_card Finset.inter_subset_right) htcard,
    hinter⟩

private lemma good_all_faces_of_skel (K : SimplicialComplex ℝ (E m)) (k : ℕ)
    {P : Submodule ℝ (E m)} {x : E m} (hx : x ∈ skel K k)
    (hdim : Module.finrank ℝ P + 3 = m)
    (hsk : ∀ r ∈ K.faces, r.card ≤ k → x ∈ convexHull ℝ (r : Set (E m)) →
      ∀ u ∈ closedStar K r, ∀ v ∈ closedStar K r, u - v ∈ P → u = v) :
    ∀ s ∈ K.faces, x ∈ convexHull ℝ (s : Set (E m)) →
      ∀ u ∈ closedStar K s, ∀ v ∈ closedStar K s, u - v ∈ P → u = v := by
  intro s hs hxs
  obtain ⟨r, hr, hrs, hrcard, hxr⟩ := convexHull_inter_skel_of_card K hs k x ⟨hxs, hx⟩
  exact transGrass_mono K hrs hdim (hsk r hr hrcard hxr)

private lemma extend_on_simplex (K : SimplicialComplex ℝ (E m))
    (hfin : K.faces.Finite) {k : ℕ} (hk : 1 ≤ k)
    {s : Finset (E m)} (hs : s ∈ K.faces) (hscard : s.card = k + 1)
    (hcontr : @ContractibleSpace (transGrass K s) (transGrassTopo K s))
    (f : E m → Submodule ℝ (E m))
    (hf_cont : ContinuousOn (fun x => (f x).starProjection) (skel K k))
    (hf_dim : ∀ x ∈ skel K k, Module.finrank ℝ (f x) + 3 = m)
    (hf_sec : ∀ x ∈ skel K k, ∀ r ∈ K.faces, x ∈ convexHull ℝ (r : Set (E m)) →
      ∀ u ∈ closedStar K r, ∀ v ∈ closedStar K r, u - v ∈ f x → u = v) :
    ∃ g : E m → Submodule ℝ (E m),
      ContinuousOn (fun x => (g x).starProjection) (convexHull ℝ (s : Set (E m))) ∧
      (∀ x ∈ convexHull ℝ (s : Set (E m)), Module.finrank ℝ (g x) + 3 = m) ∧
      (∀ x ∈ convexHull ℝ (s : Set (E m)),
        ∀ u ∈ closedStar K s, ∀ v ∈ closedStar K s, u - v ∈ g x → u = v) ∧
      (∀ x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k, g x = f x) := by
  classical
  letI : TopologicalSpace (transGrass K s) := transGrassTopo K s
  haveI : ContractibleSpace (transGrass K s) := hcontr
  have hs_ne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hscard_pos : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast (show 0 < s.card by omega)
  -- Extend s to an affine basis of E m
  have hindep : AffineIndependent ℝ (Subtype.val : ↥(s : Set (E m)) → E m) := K.indep hs
  obtain ⟨t, hst, ht_indep, ht_span⟩ := exists_subset_affineIndependent_affineSpan_eq_top hindep
  let b : AffineBasis (↥t) ℝ (E m) := ⟨Subtype.val, ht_indep, by simpa using ht_span⟩
  let w : E m → E m → ℝ := fun v x =>
    if hv : v ∈ t then b.coord ⟨v, hv⟩ x else 0
  have hw_cont : ∀ v ∈ s, Continuous (w v) := by
    intro v hv
    have hvt : v ∈ t := hst hv
    have : w v = fun x => b.coord ⟨v, hvt⟩ x := by
      ext x
      simp [w, hvt]
    rw [this]
    exact continuous_barycentric_coord b ⟨v, hvt⟩
  -- Barycentric coordinate identities for points in convexHull r (r ⊆ s)
  have hw_hull : ∀ {r : Finset (E m)}, r ⊆ s → ∀ x ∈ convexHull ℝ (r : Set (E m)),
      (∀ v ∈ s, 0 ≤ w v x) ∧ (∑ v ∈ s, w v x = 1) ∧
      (∑ v ∈ s, w v x • v = x) ∧ (∀ v ∈ s, v ∉ r → w v x = 0) := by
    intro r hrs x hx
    rw [Finset.convexHull_eq] at hx
    rcases hx with ⟨c, hc_nonneg, hc_sum, rfl⟩
    let c' : ↥t → ℝ := fun p => if (p : E m) ∈ r then c p else 0
    let r' : Finset (↥t) := r.attach.map ⟨fun p => ⟨p.1, hst (hrs p.2)⟩, by
      intro a b hab; exact Subtype.ext (congrArg (Subtype.val : ↥t → E m) hab)⟩
    have hfin_r : r'.sum c' = 1 := by
      rw [Finset.sum_map]
      have : ∑ p ∈ r.attach, c' ⟨p.1, hst (hrs p.2)⟩ = ∑ p ∈ r, c p := by
        calc
          ∑ p ∈ r.attach, c' ⟨p.1, hst (hrs p.2)⟩
              = ∑ p ∈ r.attach, c p.1 := Finset.sum_congr rfl (fun p _ => if_pos p.2)
          _ = ∑ p ∈ r, c p := Finset.sum_attach r c
      exact this.trans hc_sum
    have hcomb : r.centerMass c id = r'.affineCombination ℝ b c' := by
      rw [r.centerMass_eq_of_sum_1 id hc_sum, Finset.affineCombination_eq_linear_combination _ _ _ hfin_r]
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, id_eq]
      calc
        ∑ p ∈ r, c p • p = ∑ p ∈ r.attach, c p.1 • p.1 := (Finset.sum_attach r (fun p => c p • p)).symm
        _ = ∑ p ∈ r.attach, c' ⟨p.1, hst (hrs p.2)⟩ • b ⟨p.1, hst (hrs p.2)⟩ :=
          Finset.sum_congr rfl (fun p _ => by
            change c p.1 • p.1 = (if p.1 ∈ r then c p.1 else 0) • p.1
            rw [if_pos p.2])
    have hw_eq : ∀ v ∈ s, w v (r.centerMass c id) = if v ∈ r then c v else 0 := by
      intro v hv
      have hvt : v ∈ t := hst hv
      rw [hcomb]
      simp only [w, hvt, dite_true]
      by_cases hvr : v ∈ r
      · have hmem : (⟨v, hvt⟩ : ↥t) ∈ r' := by
          simp only [r', Finset.mem_map, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk]
          exact ⟨⟨v, hvr⟩, rfl⟩
        rw [b.coord_apply_combination_of_mem hmem hfin_r]
      · have hnot : (⟨v, hvt⟩ : ↥t) ∉ r' := by
          simp only [r', Finset.mem_map, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
            not_exists]
          intro p hp
          have hp' : p.1 = v := congrArg (Subtype.val : ↥t → E m) hp
          exact hvr (hp' ▸ p.2)
        rw [b.coord_apply_combination_of_notMem hnot hfin_r]
        simp [hvr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hw_eq v hv]
      split_ifs with hvr
      · exact hc_nonneg v hvr
      · exact le_rfl
    · calc
        ∑ v ∈ s, w v (r.centerMass c id)
            = ∑ v ∈ s, (if v ∈ r then c v else 0) := Finset.sum_congr rfl hw_eq
        _ = ∑ v ∈ r, c v := by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hrs]
        _ = 1 := hc_sum
    · calc
        ∑ v ∈ s, w v (r.centerMass c id) • v
            = ∑ v ∈ s, (if v ∈ r then c v else 0) • v := Finset.sum_congr rfl (fun v hv => by rw [hw_eq v hv])
        _ = ∑ v ∈ s, (if v ∈ r then c v • v else 0) := Finset.sum_congr rfl (fun v _ => by split_ifs <;> simp)
        _ = ∑ v ∈ r, c v • v := by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hrs]
        _ = r.centerMass c id := (r.centerMass_eq_of_sum_1 id hc_sum).symm
    · intro v hv hvr
      rw [hw_eq v hv, if_neg hvr]
  -- Barycenter c_s
  let cs : E m := ((s.card : ℝ)⁻¹) • ∑ v ∈ s, v
  have hcs_mem : cs ∈ convexHull ℝ (s : Set (E m)) := by
    rw [Finset.convexHull_eq]
    refine ⟨fun _ => (s.card : ℝ)⁻¹, fun _ _ => inv_nonneg.mpr hscard_pos.le, ?_, ?_⟩
    · simp [hscard_pos.ne']
    · rw [s.centerMass_eq_of_sum_1 id (by simp [hscard_pos.ne'])]
      simp [cs, Finset.smul_sum]
  have hw_cs : ∀ v ∈ s, w v cs = (s.card : ℝ)⁻¹ := by
    intro v hv
    have hvt : v ∈ t := hst hv
    have hsum1 : ∑ _ ∈ s, (s.card : ℝ)⁻¹ = 1 := by simp [hscard_pos.ne']
    have hcs_cm : cs = s.centerMass (fun _ => (s.card : ℝ)⁻¹) id := by
      rw [s.centerMass_eq_of_sum_1 id hsum1]
      simp [cs, Finset.smul_sum]
    let s' : Finset (↥t) := s.attach.map ⟨fun p => ⟨p.1, hst p.2⟩, by
      intro a b hab; exact Subtype.ext (congrArg (Subtype.val : ↥t → E m) hab)⟩
    have hsum' : s'.sum (fun _ => (s.card : ℝ)⁻¹) = 1 := by
      rw [Finset.sum_map]
      simp [hscard_pos.ne']
    have hcomb : cs = s'.affineCombination ℝ b (fun _ => (s.card : ℝ)⁻¹) := by
      rw [hcs_cm, s.centerMass_eq_of_sum_1 id hsum1,
        Finset.affineCombination_eq_linear_combination _ _ _ hsum', Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, id_eq]
      exact (Finset.sum_attach s (fun p => (s.card : ℝ)⁻¹ • p)).symm
    have hmem : (⟨v, hvt⟩ : ↥t) ∈ s' := by
      simp only [s', Finset.mem_map, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk]
      exact ⟨⟨v, hv⟩, rfl⟩
    rw [hcomb]
    simp only [w, hvt, dite_true]
    exact b.coord_apply_combination_of_mem hmem hsum'
  -- Minimum coordinate function and scaling lambda
  let minW : E m → ℝ := fun x => s.inf' hs_ne (fun v => w v x)
  have hminW_cont : Continuous minW := by
    have : ∀ (r : Finset (E m)) (hr : r.Nonempty), r ⊆ s →
        Continuous (fun x => r.inf' hr (fun v => w v x)) := by
      intro r hr hrs
      induction r using Finset.induction_on with
      | empty => exact (Finset.not_nonempty_empty hr).elim
      | @insert a r' ha ih =>
        by_cases hr' : r'.Nonempty
        · have hsub : r' ⊆ s := Finset.Subset.trans (Finset.subset_insert a r') hrs
          have ha_s : a ∈ s := hrs (Finset.mem_insert_self a r')
          have heq : (fun x => (insert a r').inf' hr (fun v => w v x)) =
              fun x => min (w a x) (r'.inf' hr' (fun v => w v x)) := by
            ext x
            exact Finset.inf'_insert hr' (f := fun v => w v x)
          rw [heq]
          exact (hw_cont a ha_s).min (ih hr' hsub)
        · rw [Finset.not_nonempty_iff_eq_empty] at hr'
          subst hr'
          have ha_s : a ∈ s := hrs (Finset.mem_insert_self a ∅)
          simpa using hw_cont a ha_s
    exact this s hs_ne (Finset.Subset.refl s)
  let lam : E m → ℝ := fun x => (s.card : ℝ) * minW x
  have hlam_cont : Continuous lam := continuous_const.mul hminW_cont
  have hlam_nonneg : ∀ x ∈ convexHull ℝ (s : Set (E m)), 0 ≤ lam x := by
    intro x hx
    have h1 := (hw_hull (Finset.Subset.refl s) x hx).1
    have hmin : 0 ≤ minW x := (Finset.le_inf'_iff hs_ne _).mpr h1
    exact mul_nonneg hscard_pos.le hmin
  have hlam_le_one : ∀ x ∈ convexHull ℝ (s : Set (E m)), lam x ≤ 1 := by
    intro x hx
    have hsum := (hw_hull (Finset.Subset.refl s) x hx).2.1
    have hle : ∑ _ ∈ s, minW x ≤ ∑ v ∈ s, w v x :=
      Finset.sum_le_sum (fun v hv => Finset.inf'_le (fun u => w u x) hv)
    rw [Finset.sum_const, nsmul_eq_mul, hsum] at hle
    exact hle
  have hlam_cs : lam cs = 1 := by
    have hmin : minW cs = (s.card : ℝ)⁻¹ := by
      apply le_antisymm
      · obtain ⟨v, hv⟩ := hs_ne
        exact le_trans (Finset.inf'_le (fun u => w u cs) hv) (hw_cs v hv).le
      · exact (Finset.le_inf'_iff hs_ne _).mpr (fun v hv => (hw_cs v hv).ge)
    simp [lam, hmin, hscard_pos.ne']
  have hlam_eq_one_iff : ∀ x ∈ convexHull ℝ (s : Set (E m)), lam x = 1 ↔ x = cs := by
    intro x hx
    constructor
    · intro h1
      have hmin_eq : minW x = (s.card : ℝ)⁻¹ := by
        have : (s.card : ℝ) * minW x = 1 := h1
        field_simp [hscard_pos.ne'] at this ⊢
        linarith
      have hge : ∀ v ∈ s, (s.card : ℝ)⁻¹ ≤ w v x := by
        intro v hv
        rw [← hmin_eq]
        exact Finset.inf'_le (fun u => w u x) hv
      have hsum := (hw_hull (Finset.Subset.refl s) x hx).2.1
      have hsum_eq : ∑ v ∈ s, (w v x - (s.card : ℝ)⁻¹) = 0 := by
        rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul,
          mul_inv_cancel₀ hscard_pos.ne', sub_self]
      have hall : ∀ v ∈ s, w v x = (s.card : ℝ)⁻¹ := by
        intro v hv
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun u hu => sub_nonneg.mpr (hge u hu))).mp hsum_eq v hv
        linarith
      have hx_eq := (hw_hull (Finset.Subset.refl s) x hx).2.2.1
      rw [← hx_eq]
      calc
        ∑ v ∈ s, w v x • v = ∑ v ∈ s, (s.card : ℝ)⁻¹ • v :=
          Finset.sum_congr rfl (fun v hv => by rw [hall v hv])
        _ = cs := by simp [cs, Finset.smul_sum]
    · rintro rfl
      exact hlam_cs
  have hlam_bdry : ∀ x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k, lam x = 0 := by
    intro x hx
    obtain ⟨r, _, hrs, hrcard, hxr⟩ := convexHull_inter_skel_of_card K hs k x hx
    have hlt : r.card < s.card := by omega
    have hnot_sub : ¬ s ⊆ r := fun hsr => not_lt_of_ge (Finset.card_le_card hsr) hlt
    obtain ⟨v₀, hv₀s, hv₀r⟩ := Finset.not_subset.mp hnot_sub
    have hw0 : w v₀ x = 0 := (hw_hull hrs x hxr).2.2.2 v₀ hv₀s hv₀r
    have hmin_le : minW x ≤ 0 := hw0 ▸ Finset.inf'_le (fun u => w u x) hv₀s
    have hmin_ge : 0 ≤ minW x := (Finset.le_inf'_iff hs_ne _).mpr (hw_hull (Finset.Subset.refl s) x hx.1).1
    have hmin0 : minW x = 0 := le_antisymm hmin_le hmin_ge
    simp [lam, hmin0]
  -- Radial projection onto boundary
  let rad : E m → E m := fun x => (1 - lam x)⁻¹ • (x - lam x • cs)
  have hrad_bdry : ∀ x ∈ convexHull ℝ (s : Set (E m)), lam x < 1 →
      rad x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k := by
    intro x hx hlt
    have hpos : 0 < 1 - lam x := sub_pos.mpr hlt
    obtain ⟨v₀, hv₀s, hv₀_min⟩ := Finset.exists_min_image s (fun v => w v x) hs_ne
    have hmin_eq : minW x = w v₀ x := by
      apply le_antisymm
      · exact Finset.inf'_le (fun u => w u x) hv₀s
      · exact (Finset.le_inf'_iff hs_ne _).mpr hv₀_min
    let r : Finset (E m) := s.erase v₀
    have hrs : r ⊆ s := Finset.erase_subset v₀ s
    have hrcard : r.card = k := by
      rw [Finset.card_erase_of_mem hv₀s, hscard]
      omega
    have hr_ne : r.Nonempty := Finset.card_pos.mp (by omega)
    have hr_face : r ∈ K.faces := K.down_closed hs hrs hr_ne
    let c : E m → ℝ := fun v => (w v x - w v₀ x) / (1 - lam x)
    have hc_nonneg : ∀ v ∈ r, 0 ≤ c v := by
      intro v hv
      exact div_nonneg (sub_nonneg.mpr (hv₀_min v (hrs hv))) hpos.le
    have hc_v0 : c v₀ = 0 := by simp [c]
    have hc_sum : ∑ v ∈ r, c v = 1 := by
      have h1 : ∑ v ∈ r, c v = ∑ v ∈ s, c v := by
        rw [← Finset.add_sum_erase s c hv₀s, hc_v0, zero_add]
      rw [h1]
      have hsum_w := (hw_hull (Finset.Subset.refl s) x hx).2.1
      calc
        ∑ v ∈ s, (w v x - w v₀ x) / (1 - lam x)
            = (∑ v ∈ s, (w v x - w v₀ x)) / (1 - lam x) := (Finset.sum_div _ _ _).symm
        _ = (1 - (s.card : ℝ) * w v₀ x) / (1 - lam x) := by
          rw [Finset.sum_sub_distrib, hsum_w, Finset.sum_const, nsmul_eq_mul]
        _ = (1 - lam x) / (1 - lam x) := by rw [← hmin_eq]
        _ = 1 := div_self hpos.ne'
    have hrad_eq : rad x = r.centerMass c id := by
      rw [r.centerMass_eq_of_sum_1 id hc_sum]
      simp only [id_eq]
      have h1 : ∑ v ∈ r, c v • v = ∑ v ∈ s, c v • v := by
        rw [← Finset.add_sum_erase s (fun v => c v • v) hv₀s, hc_v0, zero_smul, zero_add]
      rw [h1]
      have hsum_v := (hw_hull (Finset.Subset.refl s) x hx).2.2.1
      have hlam_cs_eq : lam x • cs = w v₀ x • ∑ v ∈ s, v := by
        simp only [lam, hmin_eq, cs, smul_smul]
        congr 1
        field_simp [hscard_pos.ne']
      calc
        rad x = (1 - lam x)⁻¹ • (∑ v ∈ s, w v x • v - w v₀ x • ∑ v ∈ s, v) := by
          dsimp only [rad]
          rw [hsum_v, hlam_cs_eq]
        _ = (1 - lam x)⁻¹ • ∑ v ∈ s, (w v x - w v₀ x) • v := by
          rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [sub_smul]
        _ = ∑ v ∈ s, c v • v := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          simp only [c, div_eq_inv_mul, mul_smul]
    have hrad_r : rad x ∈ convexHull ℝ (r : Set (E m)) := by
      rw [Finset.convexHull_eq]
      exact ⟨c, hc_nonneg, hc_sum, hrad_eq.symm⟩
    refine ⟨convexHull_mono (Finset.coe_subset.mpr hrs) hrad_r, ?_⟩
    simp only [skel, mem_iUnion, mem_setOf_eq]
    exact ⟨r, ⟨hr_face, hrcard.le⟩, hrad_r⟩
  have hrad_id : ∀ x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k, rad x = x := by
    intro x hx
    simp [rad, hlam_bdry x hx]
  -- Contracting homotopy on transGrass K s
  obtain ⟨p₀, ⟨H⟩⟩ := id_nullhomotopic (transGrass K s)
  -- Helper to lift f x into transGrass K s for x ∈ Δ_s ∩ skel K k
  let liftF : ∀ x, x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k → transGrass K s :=
    fun x hx => ⟨f x, hf_dim x hx.2, hf_sec x hx.2 s hs hx.1⟩
  -- Define φ : Δ_s → transGrass K s
  let Δ : Set (E m) := convexHull ℝ (s : Set (E m))
  let φ : Δ → transGrass K s := fun x =>
    if h : lam x.1 < 1 then
      H (⟨lam x.1, hlam_nonneg x.1 x.2, hlam_le_one x.1 x.2⟩,
        liftF (rad x.1) (hrad_bdry x.1 x.2 h))
    else
      p₀
  have hφ_cont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hlt : lam x.1 < 1
    · -- Away from barycenter: open set {y : Δ | lam y.1 < 1}
      let U : Set Δ := {y : Δ | lam y.1 < 1}
      have hU_open : IsOpen U := isOpen_lt (hlam_cont.comp continuous_subtype_val) continuous_const
      have hxU : x ∈ U := hlt
      have hlam_I : Continuous (fun y : Δ =>
          (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩ : I)) :=
        Continuous.subtype_mk (hlam_cont.comp continuous_subtype_val) _
      have hrad_contAt : ContinuousAt (fun y : Δ => rad y.1) x := by
        have hsub : ContinuousAt (fun y : Δ => 1 - lam y.1) x :=
          continuousAt_const.sub (hlam_cont.continuousAt.comp continuous_subtype_val.continuousAt)
        have hne : 1 - lam x.1 ≠ 0 := (sub_pos.mpr hlt).ne'
        have hvec : ContinuousAt (fun y : Δ => y.1 - lam y.1 • cs) x :=
          continuous_subtype_val.continuousAt.sub
            ((hlam_cont.continuousAt.comp continuous_subtype_val.continuousAt).smul continuousAt_const)
        exact (hsub.inv₀ hne).smul hvec
      have hf_rad_contAt : ContinuousAt (fun y : Δ => (f (rad y.1)).starProjection) x := by
        have hmem_sk : rad x.1 ∈ skel K k := (hrad_bdry x.1 x.2 hlt).2
        have hwithin : ContinuousWithinAt (fun z => (f z).starProjection) (skel K k) (rad x.1) :=
          hf_cont (rad x.1) hmem_sk
        have hmaps : ∀ᶠ y in 𝓝 x, rad y.1 ∈ skel K k := by
          filter_upwards [hU_open.mem_nhds hxU] with y hy
          exact (hrad_bdry y.1 y.2 hy).2
        exact hwithin.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hrad_contAt hmaps)
      have hind : Topology.IsInducing (fun P : transGrass K s => P.val.starProjection) := ⟨rfl⟩
      have hlift_contAt : ContinuousAt (fun y : Δ =>
          if h : lam y.1 < 1 then liftF (rad y.1) (hrad_bdry y.1 y.2 h) else p₀) x := by
        rw [hind.continuousAt_iff]
        have hev : (fun y : Δ => (if h : lam y.1 < 1 then liftF (rad y.1) (hrad_bdry y.1 y.2 h) else p₀).val.starProjection)
            =ᶠ[𝓝 x] (fun y : Δ => (f (rad y.1)).starProjection) := by
          filter_upwards [hU_open.mem_nhds hxU] with y hy
          have hylt : lam y.1 < 1 := hy
          simp [hylt, liftF]
        exact hf_rad_contAt.congr hev.symm
      have hcomp_contAt : ContinuousAt (fun y : Δ =>
          H (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩,
            if h : lam y.1 < 1 then liftF (rad y.1) (hrad_bdry y.1 y.2 h) else p₀)) x :=
        H.continuous.continuousAt.comp (hlam_I.continuousAt.prodMk hlift_contAt)
      have hev_φ : φ =ᶠ[𝓝 x] (fun y : Δ =>
          H (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩,
            if h : lam y.1 < 1 then liftF (rad y.1) (hrad_bdry y.1 y.2 h) else p₀)) := by
        filter_upwards [hU_open.mem_nhds hxU] with y hy
        have hylt : lam y.1 < 1 := hy
        simp only [φ, hylt, dite_true]
      exact hcomp_contAt.congr hev_φ.symm
    · -- At barycenter: lam x.1 = 1, use compactness of boundary + tube lemma
      have hlam1 : lam x.1 = 1 := le_antisymm (hlam_le_one x.1 x.2) (not_lt.mp hlt)
      have hφx : φ x = p₀ := by simp [φ, hlt]
      rw [ContinuousAt, hφx, _root_.tendsto_nhds]
      intro U hU_open hp₀U
      let Bset : Set (E m) := Δ ∩ skel K k
      have hBset_compact : IsCompact Bset :=
        (isCompact_convexHull_finset s).inter_right (isClosed_skel K hfin k)
      let liftB : Bset → transGrass K s := fun y => liftF y.1 y.2
      have hind : Topology.IsInducing (fun P : transGrass K s => P.val.starProjection) := ⟨rfl⟩
      have hliftB_cont : Continuous liftB := by
        rw [hind.continuous_iff]
        have hcomp : (fun P : transGrass K s => P.val.starProjection) ∘ liftB =
            (fun z => (f z).starProjection) ∘ (Subtype.val : Bset → E m) := rfl
        rw [hcomp]
        exact (hf_cont.mono Set.inter_subset_right).comp_continuous continuous_subtype_val (fun y => y.2)
      let B : Set (transGrass K s) := liftB '' Set.univ
      have hB_compact : IsCompact B := by
        haveI : CompactSpace Bset := isCompact_iff_compactSpace.mp hBset_compact
        exact isCompact_univ.image hliftB_cont
      have htube_sub : ({(1 : I)} : Set I) ×ˢ B ⊆ H ⁻¹' U := by
        rintro ⟨t', q⟩ ⟨ht', _⟩
        rw [Set.mem_singleton_iff] at ht'
        subst ht'
        simpa [Set.mem_preimage] using hp₀U
      obtain ⟨u, v, hu_open, _, h1u, hBv, huv⟩ :=
        generalized_tube_lemma isCompact_singleton hB_compact (hU_open.preimage H.continuous) htube_sub
      have hlam_I : Continuous (fun y : Δ =>
          (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩ : I)) :=
        Continuous.subtype_mk (hlam_cont.comp continuous_subtype_val) _
      have hpre_open : IsOpen ((fun y : Δ =>
          (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩ : I)) ⁻¹' u) :=
        hu_open.preimage hlam_I
      have hx_pre : x ∈ (fun y : Δ =>
          (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩ : I)) ⁻¹' u := by
        have h1eq : (⟨lam x.1, hlam_nonneg x.1 x.2, hlam_le_one x.1 x.2⟩ : I) = 1 :=
          Subtype.ext hlam1
        simpa [Set.mem_preimage, h1eq] using h1u (Set.mem_singleton (1 : I))
      filter_upwards [hpre_open.mem_nhds hx_pre] with y hy
      change φ y ∈ U
      by_cases hylt : lam y.1 < 1
      · simp only [φ, hylt, dite_true]
        have hmemB : liftF (rad y.1) (hrad_bdry y.1 y.2 hylt) ∈ B :=
          ⟨⟨rad y.1, hrad_bdry y.1 y.2 hylt⟩, Set.mem_univ _, rfl⟩
        have hyu : (⟨lam y.1, hlam_nonneg y.1 y.2, hlam_le_one y.1 y.2⟩ : I) ∈ u := hy
        exact huv ⟨hyu, hBv hmemB⟩
      · simp only [φ, hylt, dite_false]
        exact hp₀U
  -- Define total function g : E m → Submodule ℝ (E m)
  let g : E m → Submodule ℝ (E m) := fun x =>
    if hx : x ∈ Δ then (φ ⟨x, hx⟩).val else p₀.val
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hproj_cont : Continuous (fun x : Δ => (φ x).val.starProjection) :=
      continuous_induced_dom.comp hφ_cont
    have heq : (convexHull ℝ (s : Set (E m))).domRestrict (fun x => (g x).starProjection) =
        fun x : Δ => (φ x).val.starProjection := by
      funext x
      change (g x.1).starProjection = (φ x).val.starProjection
      have hgx : g x.1 = (φ x).val := dif_pos x.2
      rw [hgx]
    rw [heq]
    exact hproj_cont
  · intro x hx
    have hgx : g x = (φ ⟨x, hx⟩).val := dif_pos hx
    generalize hP : g x = P
    have hP' : P = (φ ⟨x, hx⟩).val := hP.symm.trans hgx
    subst hP'
    exact (φ ⟨x, hx⟩).2.1
  · intro x hx
    have hgx : g x = (φ ⟨x, hx⟩).val := dif_pos hx
    rw [hgx]
    exact (φ ⟨x, hx⟩).2.2
  · intro x hx
    have hlam0 : lam x = 0 := hlam_bdry x hx
    have hlt : lam x < 1 := by linarith
    have hradx : rad x = x := hrad_id x hx
    have hgx : g x = (φ ⟨x, hx.1⟩).val := dif_pos hx.1
    rw [hgx]
    dsimp only [φ]
    rw [dif_pos hlt]
    have h0eq : (⟨lam x, hlam_nonneg x hx.1, hlam_le_one x hx.1⟩ : I) = 0 := Subtype.ext hlam0
    have hlift_eq : liftF (rad x) (hrad_bdry x hx.1 hlt) = liftF x hx := by
      apply Subtype.ext
      simp [liftF, hradx]
    rw [h0eq, hlift_eq]
    change (H (0, liftF x hx)).val = f x
    rw [H.apply_zero]
    rfl

private lemma continuousOn_biUnion_of_isClosed {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} {s : Set ι} (hs : s.Finite) {t : ι → Set α} {f : α → β}
    (ht : ∀ i ∈ s, IsClosed (t i)) (hf : ∀ i ∈ s, ContinuousOn f (t i)) :
    ContinuousOn f (⋃ i ∈ s, t i) := by
  classical
  have hU : (⋃ i ∈ s, t i) = ⋃ i ∈ hs.toFinset, t i := by
    ext x
    simp
  rw [hU]
  have ht' : ∀ i ∈ hs.toFinset, IsClosed (t i) := fun i hi => ht i (hs.mem_toFinset.mp hi)
  have hf' : ∀ i ∈ hs.toFinset, ContinuousOn f (t i) := fun i hi => hf i (hs.mem_toFinset.mp hi)
  suffices h : ∀ (S : Finset ι), (∀ i ∈ S, IsClosed (t i)) → (∀ i ∈ S, ContinuousOn f (t i)) →
      ContinuousOn f (⋃ i ∈ S, t i) by
    exact h hs.toFinset ht' hf'
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | @insert a S _ ih =>
    intro htS hfS
    have hins : (⋃ i ∈ insert a S, t i) = t a ∪ ⋃ i ∈ S, t i := by
      ext x
      simp
    rw [hins]
    have hcl_u : IsClosed (⋃ i ∈ S, t i) :=
      S.finite_toSet.isClosed_biUnion (fun i hi => htS i (Finset.mem_insert_of_mem hi))
    exact (hfS a (Finset.mem_insert_self a S)).union_of_isClosed
      (ih (fun i hi => htS i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfS i (Finset.mem_insert_of_mem hi)))
      (htS a (Finset.mem_insert_self a S)) hcl_u

private lemma skel_extension (K : SimplicialComplex ℝ (E m))
    (hfin : K.faces.Finite)
    (h1 : ∀ s ∈ K.faces, s.card = 1 → Nonempty (transGrass K s))
    (h2 : ∀ s ∈ K.faces, 2 ≤ s.card → @ContractibleSpace (transGrass K s) (transGrassTopo K s)) :
    ∀ k : ℕ, 1 ≤ k →
      ∃ f : E m → Submodule ℝ (E m),
        ContinuousOn (fun x => (f x).starProjection) (skel K k) ∧
        (∀ x ∈ skel K k, Module.finrank ℝ (f x) + 3 = m) ∧
        (∀ x ∈ skel K k, ∀ s ∈ K.faces, x ∈ convexHull ℝ (s : Set (E m)) →
          ∀ u ∈ closedStar K s, ∀ v ∈ closedStar K s, u - v ∈ f x → u = v) := by
  classical
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    -- Base case k = 1: skel K 1 is a finite set of vertices
    let f : E m → Submodule ℝ (E m) := fun x =>
      if h : {x} ∈ K.faces then (Classical.choice (h1 {x} h (Finset.card_singleton x))).val else ⊥
    have hsk1_fin : (skel K 1).Finite := by
      have hsub : ({s | s ∈ K.faces ∧ s.card ≤ 1} : Set (Finset (E m))).Finite :=
        hfin.subset (fun _ hs => hs.1)
      refine hsub.biUnion (fun s hs => ?_)
      have hcard1 : s.card = 1 :=
        le_antisymm hs.2 (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs.1))
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard1
      simp
    have hmem_sk1 : ∀ x ∈ skel K 1, {x} ∈ K.faces := by
      intro x hx
      simp only [skel, mem_iUnion, mem_setOf_eq] at hx
      rcases hx with ⟨s, ⟨hs, hcard⟩, hxs⟩
      have hcard1 : s.card = 1 :=
        le_antisymm hcard (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs))
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard1
      simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hxs
      subst hxs
      exact hs
    refine ⟨f, ?_, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_restrict]
      haveI : Finite (skel K 1) := hsk1_fin.to_subtype
      exact continuous_of_discreteTopology
    · intro x hx
      have hx' : {x} ∈ K.faces := hmem_sk1 x hx
      have hfx : f x = (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).val := dif_pos hx'
      generalize hP : f x = P
      have hP' : P = (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).val := hP.symm.trans hfx
      subst hP'
      exact (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).2.1
    · intro x hx
      have hx' : {x} ∈ K.faces := hmem_sk1 x hx
      have hfx : f x = (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).val := dif_pos hx'
      have hdim : Module.finrank ℝ (f x) + 3 = m := by
        generalize hP : f x = P
        have hP' : P = (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).val := hP.symm.trans hfx
        subst hP'
        exact (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).2.1
      refine good_all_faces_of_skel K 1 hx hdim ?_
      intro r hr hrcard hxr
      have hcard1 : r.card = 1 :=
        le_antisymm hrcard (Finset.card_pos.mpr (K.nonempty_of_mem_faces hr))
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard1
      simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hxr
      subst hxr
      rw [hfx]
      exact (Classical.choice (h1 {x} hx' (Finset.card_singleton x))).2.2
  | succ k hk ih =>
    obtain ⟨f, hf_cont, hf_dim, hf_sec⟩ := ih
    let F : Set (Finset (E m)) := {s | s ∈ K.faces ∧ s.card = k + 1}
    have hF_fin : F.Finite := hfin.subset (fun _ hs => hs.1)
    -- For each s ∈ F, choose an extension g s on convexHull ℝ s
    have hex : ∀ s ∈ F, ∃ g : E m → Submodule ℝ (E m),
        ContinuousOn (fun x => (g x).starProjection) (convexHull ℝ (s : Set (E m))) ∧
        (∀ x ∈ convexHull ℝ (s : Set (E m)), Module.finrank ℝ (g x) + 3 = m) ∧
        (∀ x ∈ convexHull ℝ (s : Set (E m)),
          ∀ u ∈ closedStar K s, ∀ v ∈ closedStar K s, u - v ∈ g x → u = v) ∧
        (∀ x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k, g x = f x) := by
      intro s hs
      have hscard : s.card = k + 1 := hs.2
      exact extend_on_simplex K hfin hk hs.1 hscard (h2 s hs.1 (by omega)) f hf_cont hf_dim hf_sec
    let g : ∀ s : Finset (E m), s ∈ F → E m → Submodule ℝ (E m) :=
      fun s hs => Classical.choose (hex s hs)
    have hg_spec : ∀ (s : Finset (E m)) (hs : s ∈ F),
        ContinuousOn (fun x => (g s hs x).starProjection) (convexHull ℝ (s : Set (E m))) ∧
        (∀ x ∈ convexHull ℝ (s : Set (E m)), Module.finrank ℝ (g s hs x) + 3 = m) ∧
        (∀ x ∈ convexHull ℝ (s : Set (E m)),
          ∀ u ∈ closedStar K s, ∀ v ∈ closedStar K s, u - v ∈ g s hs x → u = v) ∧
        (∀ x ∈ convexHull ℝ (s : Set (E m)) ∩ skel K k, g s hs x = f x) :=
      fun s hs => Classical.choose_spec (hex s hs)
    -- Glue f on skel K k and g s on convexHull ℝ s for s ∈ F
    let f' : E m → Submodule ℝ (E m) := fun x =>
      if x ∈ skel K k then f x
      else if h : ∃ s ∈ F, x ∈ convexHull ℝ (s : Set (E m)) then
        g h.choose h.choose_spec.1 x
      else ⊥
    -- Pairwise intersections of distinct (k+1)-simplices lie in skel K k
    have hinter_F : ∀ s₁ ∈ F, ∀ s₂ ∈ F, s₁ ≠ s₂ →
        convexHull ℝ (s₁ : Set (E m)) ∩ convexHull ℝ (s₂ : Set (E m)) ⊆ skel K k := by
      intro s₁ hs₁ s₂ hs₂ hne x ⟨hx₁, hx₂⟩
      have h1 : x ∈ convexHull ℝ ((s₁ ∩ s₂ : Finset (E m)) : Set (E m)) := by
        have h := (K.convexHull_inter_convexHull hs₁.1 hs₂.1).subset ⟨hx₁, hx₂⟩
        simpa [Finset.coe_inter] using h
      have hne_inter : (s₁ ∩ s₂).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        simp [hemp] at h1
      have hcard_lt : (s₁ ∩ s₂).card < k + 1 := by
        have hssub : s₁ ∩ s₂ ⊂ s₁ := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
          intro heq
          have hsub : s₁ ⊆ s₂ := heq ▸ Finset.inter_subset_right
          exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hs₁.2, hs₂.2]))
        calc
          (s₁ ∩ s₂).card < s₁.card := Finset.card_lt_card hssub
          _ = k + 1 := hs₁.2
      simp only [skel, mem_iUnion, mem_setOf_eq]
      exact ⟨s₁ ∩ s₂, ⟨K.down_closed hs₁.1 Finset.inter_subset_left hne_inter, Nat.lt_succ_iff.mp hcard_lt⟩, h1⟩
    have hf'_on_sk : ∀ x ∈ skel K k, f' x = f x := by
      intro x hx
      simp [f', hx]
    have hf'_on_s : ∀ (s : Finset (E m)) (hs : s ∈ F), ∀ x ∈ convexHull ℝ (s : Set (E m)),
        f' x = g s hs x := by
      intro s hs x hxs
      by_cases hxsk : x ∈ skel K k
      · rw [hf'_on_sk x hxsk]
        exact ((hg_spec s hs).2.2.2 x ⟨hxs, hxsk⟩).symm
      · have hex_s : ∃ r ∈ F, x ∈ convexHull ℝ (r : Set (E m)) := ⟨s, hs, hxs⟩
        simp only [f', hxsk, if_false, hex_s, dite_true]
        have hch_eq : hex_s.choose = s := by
          by_contra hne
          exact hxsk (hinter_F hex_s.choose hex_s.choose_spec.1 s hs hne ⟨hex_s.choose_spec.2, hxs⟩)
        have hg_eq : ∀ (r₁ r₂ : Finset (E m)) (hr₁ : r₁ ∈ F) (hr₂ : r₂ ∈ F), r₁ = r₂ → g r₁ hr₁ x = g r₂ hr₂ x := by
          rintro r₁ r₂ hr₁ hr₂ rfl
          rfl
        exact hg_eq hex_s.choose s hex_s.choose_spec.1 hs hch_eq
    have hsk_succ_eq : skel K (k + 1) = skel K k ∪ ⋃ s ∈ F, convexHull ℝ (s : Set (E m)) := by
      ext x
      simp only [skel, F, mem_union, mem_iUnion, mem_setOf_eq]
      constructor
      · rintro ⟨s, ⟨hs, hcard⟩, hxs⟩
        rcases Nat.le_succ_iff.mp hcard with hle | heq
        · exact Or.inl ⟨s, ⟨hs, hle⟩, hxs⟩
        · exact Or.inr ⟨s, ⟨hs, heq⟩, hxs⟩
      · rintro (⟨s, ⟨hs, hle⟩, hxs⟩ | ⟨s, ⟨hs, heq⟩, hxs⟩)
        · exact ⟨s, ⟨hs, Nat.le_succ_of_le hle⟩, hxs⟩
        · exact ⟨s, ⟨hs, heq.le⟩, hxs⟩
    refine ⟨f', ?_, ?_, ?_⟩
    · rw [hsk_succ_eq]
      have hcont_sk : ContinuousOn (fun x => (f' x).starProjection) (skel K k) :=
        hf_cont.congr (fun x hx => by rw [hf'_on_sk x hx])
      have hcont_F : ContinuousOn (fun x => (f' x).starProjection) (⋃ s ∈ F, convexHull ℝ (s : Set (E m))) :=
        continuousOn_biUnion_of_isClosed hF_fin
          (fun s _ => (isCompact_convexHull_finset s).isClosed)
          (fun s hs => (hg_spec s hs).1.congr (fun x hx => by rw [hf'_on_s s hs x hx]))
      have hcl_F : IsClosed (⋃ s ∈ F, convexHull ℝ (s : Set (E m))) :=
        hF_fin.isClosed_biUnion (fun s _ => (isCompact_convexHull_finset s).isClosed)
      exact hcont_sk.union_of_isClosed hcont_F (isClosed_skel K hfin k) hcl_F
    · intro x hx
      rw [hsk_succ_eq] at hx
      rcases hx with hxsk | hxF
      · rw [hf'_on_sk x hxsk]
        exact hf_dim x hxsk
      · simp only [mem_iUnion] at hxF
        rcases hxF with ⟨s, hs, hxs⟩
        rw [hf'_on_s s hs x hxs]
        exact (hg_spec s hs).2.1 x hxs
    · intro x hx
      have hdim_x : Module.finrank ℝ (f' x) + 3 = m := by
        rw [hsk_succ_eq] at hx
        rcases hx with hxsk | hxF
        · rw [hf'_on_sk x hxsk]; exact hf_dim x hxsk
        · simp only [mem_iUnion] at hxF
          rcases hxF with ⟨s, hs, hxs⟩
          rw [hf'_on_s s hs x hxs]; exact (hg_spec s hs).2.1 x hxs
      refine good_all_faces_of_skel K (k + 1) hx hdim_x ?_
      intro r hr hrcard hxr
      by_cases hxsk : x ∈ skel K k
      · rw [hf'_on_sk x hxsk]
        exact hf_sec x hxsk r hr hxr
      · have hrcard_eq : r.card = k + 1 := by
          rcases Nat.le_succ_iff.mp hrcard with hle | heq
          · exfalso
            apply hxsk
            simp only [skel, mem_iUnion, mem_setOf_eq]
            exact ⟨r, ⟨hr, hle⟩, hxr⟩
          · exact heq
        have hrF : r ∈ F := ⟨hr, hrcard_eq⟩
        rw [hf'_on_s r hrF x hxr]
        exact (hg_spec r hrF).2.2.1 x hxr

end PoincareH1

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro m K
  dsimp only
  intro hfin hpure h1 h2
  obtain ⟨f, hf_cont, hf_dim, hf_sec⟩ := PoincareH1.skel_extension K hfin h1 h2 4 (by omega)
  have hsk4 : PoincareH1.skel K 4 = K.space := PoincareH1.skel_four_eq_space K hpure
  rw [hsk4] at hf_cont hf_dim hf_sec
  refine ⟨fun x => f x.1, ?_, ?_, ?_⟩
  · exact (continuousOn_iff_continuous_restrict.mp hf_cont)
  · intro x
    exact hf_dim x.1 x.2
  · intro x s hs hxs
    exact hf_sec x.1 x.2 s hs hxs
