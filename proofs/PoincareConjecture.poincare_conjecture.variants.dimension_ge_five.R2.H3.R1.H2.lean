import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2_H3_R1
import Mathlib

/-!
# Brown's Monotone Union Theorem for Open n-Cells

An elementary radial-engulfing proof of Morton Brown's 1961 theorem (Proc. AMS 12, 812-814):
any Hausdorff space exhausted by an increasing sequence of open subsets homeomorphic to
`EuclideanSpace ℝ (Fin n)` is itself homeomorphic to `EuclideanSpace ℝ (Fin n)`.
-/

-- Credit: @Jakeybakeypants
-- The radial construction and the Hausdorff case below were formalized by @nijv.

namespace BrownMonotoneUnion

open Set Topology Metric

section RadialHomeo

/-- Piecewise-linear radial profile fixing [0, c] and [S, infty) and mapping [c, a] onto [c, b]. -/
noncomputable def plFunc (c a b S t : ℝ) : ℝ :=
  if t ≤ c then t
  else if t ≤ a then c + (b - c) / (a - c) * (t - c)
  else if t ≤ S then b + (S - b) / (S - a) * (t - a)
  else t

/-- Continuous radial scale factor equal to plFunc t / t for t > c and 1 for t <= c. -/
noncomputable def plScale (c a b S t : ℝ) : ℝ :=
  if t ≤ c then 1
  else plFunc c a b S t / max t c

lemma plFunc_continuous {c a b S : ℝ} (hca : c < a) (haS : a < S) :
    Continuous (plFunc c a b S) := by
  unfold plFunc
  have h1 : Continuous (fun t : ℝ =>
      if t ≤ S then b + (S - b) / (S - a) * (t - a) else t) := by
    apply Continuous.if_le
    · fun_prop
    · exact continuous_id
    · exact continuous_id
    · exact continuous_const
    · intro x hx
      rw [hx]
      have hSa : S - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt haS)
      field_simp [hSa]
      ring
  have h2 : Continuous (fun t : ℝ =>
      if t ≤ a then c + (b - c) / (a - c) * (t - c)
      else if t ≤ S then b + (S - b) / (S - a) * (t - a) else t) := by
    apply Continuous.if_le
    · fun_prop
    · exact h1
    · exact continuous_id
    · exact continuous_const
    · intro x hx
      rw [hx, if_pos (le_of_lt haS)]
      have hac : a - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hca)
      field_simp [hac]
      ring
  apply Continuous.if_le
  · exact continuous_id
  · exact h2
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    rw [hx, if_pos (le_of_lt hca)]
    ring

lemma plScale_continuous {c a b S : ℝ} (hc : 0 < c) (hca : c < a) (haS : a < S) :
    Continuous (plScale c a b S) := by
  unfold plScale
  apply Continuous.if_le
  · exact continuous_const
  · refine (plFunc_continuous hca haS).div (continuous_id.max continuous_const) ?_
    intro t
    exact ne_of_gt (lt_of_lt_of_le hc (le_max_right t c))
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    rw [hx]
    simp [plFunc, ne_of_gt hc]

lemma plScale_pos {c a b S : ℝ} (hc : 0 < c) (hca : c < a) (hcb : c < b)
    (haS : a < S) (hbS : b < S) (t : ℝ) :
    0 < plScale c a b S t := by
  unfold plScale
  split_ifs with htc
  · exact one_pos
  · push Not at htc
    have hmax : max t c = t := max_eq_left (le_of_lt htc)
    rw [hmax]
    apply div_pos _ (lt_trans hc htc)
    unfold plFunc
    rw [if_neg (not_le.mpr htc)]
    split_ifs with hta htS
    · have h1 : 0 < (b - c) / (a - c) * (t - c) :=
        mul_pos (div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)) (sub_pos.mpr htc)
      linarith
    · push Not at hta
      have h1 : 0 < (S - b) / (S - a) * (t - a) :=
        mul_pos (div_pos (sub_pos.mpr hbS) (sub_pos.mpr haS)) (sub_pos.mpr hta)
      linarith
    · linarith

lemma plScale_mul {c a b S : ℝ} (hc : 0 < c) (t : ℝ) :
    plScale c a b S t * t = plFunc c a b S t := by
  unfold plScale
  split_ifs with htc
  · simp [plFunc, htc]
  · push Not at htc
    have hmax : max t c = t := max_eq_left (le_of_lt htc)
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hc htc)
    rw [hmax, div_mul_cancel₀ _ ht0]

lemma plFunc_invol {c a b S : ℝ} (hca : c < a) (hcb : c < b)
    (haS : a < S) (hbS : b < S) (t : ℝ) :
    plFunc c b a S (plFunc c a b S t) = t := by
  have hac : a - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hca)
  have hbc : b - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcb)
  have hSa : S - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt haS)
  have hSb : S - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbS)
  by_cases htc : t ≤ c
  · simp [plFunc, htc]
  · push Not at htc
    by_cases hta : t ≤ a
    · have hu_eq : plFunc c a b S t = c + (b - c) / (a - c) * (t - c) := by
        simp [plFunc, not_le.mpr htc, hta]
      rw [hu_eq]
      have h1 : c < c + (b - c) / (a - c) * (t - c) := by
        have := mul_pos (div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)) (sub_pos.mpr htc)
        linarith
      have h2 : c + (b - c) / (a - c) * (t - c) ≤ b := by
        have hfrac : (t - c) / (a - c) ≤ 1 :=
          (div_le_one (sub_pos.mpr hca)).mpr (by linarith)
        have hmul : (b - c) / (a - c) * (t - c) ≤ b - c := by
          have : (b - c) / (a - c) * (t - c) = (b - c) * ((t - c) / (a - c)) := by ring
          rw [this]
          nlinarith [sub_pos.mpr hcb]
        linarith
      unfold plFunc
      rw [if_neg (not_le.mpr h1), if_pos h2]
      field_simp [hac, hbc]
      ring
    · push Not at hta
      by_cases htS : t ≤ S
      · have hu_eq : plFunc c a b S t = b + (S - b) / (S - a) * (t - a) := by
          simp [plFunc, not_le.mpr htc, not_le.mpr hta, htS]
        rw [hu_eq]
        have h1 : b < b + (S - b) / (S - a) * (t - a) := by
          have := mul_pos (div_pos (sub_pos.mpr hbS) (sub_pos.mpr haS)) (sub_pos.mpr hta)
          linarith
        have h1' : c < b + (S - b) / (S - a) * (t - a) := lt_trans hcb h1
        have h2 : b + (S - b) / (S - a) * (t - a) ≤ S := by
          have hfrac : (t - a) / (S - a) ≤ 1 :=
            (div_le_one (sub_pos.mpr haS)).mpr (by linarith)
          have hmul : (S - b) / (S - a) * (t - a) ≤ S - b := by
            have : (S - b) / (S - a) * (t - a) = (S - b) * ((t - a) / (S - a)) := by ring
            rw [this]
            nlinarith [sub_pos.mpr hbS]
          linarith
        unfold plFunc
        rw [if_neg (not_le.mpr h1'), if_neg (not_le.mpr h1), if_pos h2]
        field_simp [hSa, hSb]
        ring
      · push Not at htS
        have hu_eq : plFunc c a b S t = t := by
          simp [plFunc, not_le.mpr htc, not_le.mpr hta, not_le.mpr htS]
        rw [hu_eq]
        have htc' : ¬ t ≤ c := not_le.mpr htc
        have htb' : ¬ t ≤ b := not_le.mpr (lt_trans hbS htS)
        have htS' : ¬ t ≤ S := not_le.mpr htS
        simp [plFunc, htc', htb', htS']

lemma plFunc_le_b {c a b S : ℝ} (hca : c < a) (hcb : c < b) {t : ℝ} (hta : t ≤ a) :
    plFunc c a b S t ≤ b := by
  unfold plFunc
  split_ifs with htc
  · linarith
  · push Not at htc
    have hfrac : (t - c) / (a - c) ≤ 1 := (div_le_one (sub_pos.mpr hca)).mpr (by linarith)
    have hmul : (b - c) / (a - c) * (t - c) ≤ b - c := by
      have : (b - c) / (a - c) * (t - c) = (b - c) * ((t - c) / (a - c)) := by ring
      rw [this]
      nlinarith [sub_pos.mpr hcb]
    linarith

lemma plFunc_le_S {c a b S : ℝ} (hca : c < a) (hcb : c < b) (haS : a < S) (hbS : b < S)
    {t : ℝ} (htS : t ≤ S) :
    plFunc c a b S t ≤ S := by
  by_cases hta : t ≤ a
  · exact le_trans (plFunc_le_b hca hcb hta) (le_of_lt hbS)
  · push Not at hta
    have htc : ¬ t ≤ c := not_le.mpr (lt_trans hca hta)
    unfold plFunc
    rw [if_neg htc, if_neg (not_le.mpr hta), if_pos htS]
    have hfrac : (t - a) / (S - a) ≤ 1 := (div_le_one (sub_pos.mpr haS)).mpr (by linarith)
    have hmul : (S - b) / (S - a) * (t - a) ≤ S - b := by
      have : (S - b) / (S - a) * (t - a) = (S - b) * ((t - a) / (S - a)) := by ring
      rw [this]
      nlinarith [sub_pos.mpr hbS]
    linarith

lemma plScale_eq_one_of_le {c a b S t : ℝ} (htc : t ≤ c) :
    plScale c a b S t = 1 := by
  simp [plScale, htc]

lemma plScale_eq_one_of_ge {c a b S t : ℝ} (hc : 0 < c) (hca : c < a) (haS : a < S)
    (hSt : S ≤ t) :
    plScale c a b S t = 1 := by
  have htc : c < t := lt_of_lt_of_le (lt_trans hca haS) hSt
  have hta : a < t := lt_of_lt_of_le haS hSt
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans hc htc)
  unfold plScale
  rw [if_neg (not_le.mpr htc), max_eq_left (le_of_lt htc)]
  unfold plFunc
  rw [if_neg (not_le.mpr htc), if_neg (not_le.mpr hta)]
  split_ifs with htS
  · have hEq : t = S := le_antisymm htS hSt
    rw [hEq]
    have hSa : S - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt haS)
    have hnum : b + (S - b) / (S - a) * (S - a) = S := by
      field_simp [hSa]
      ring
    rw [hnum, div_self (hEq ▸ ht0)]
  · exact div_self ht0

/-- Radial homeomorphism of EuclideanSpace ℝ (Fin n) fixing closedBall 0 c and the complement of
ball 0 S, while mapping closedBall 0 a onto closedBall 0 b. -/
noncomputable def radialAnnulusHomeo (n : ℕ) (c a b S : ℝ)
    (hc : 0 < c) (hca : c < a) (hcb : c < b) (haS : a < S) (hbS : b < S) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun v := plScale c a b S ‖v‖ • v
  invFun v := plScale c b a S ‖v‖ • v
  left_inv v := by
    dsimp only
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hs1 : 0 < plScale c a b S ‖v‖ := plScale_pos hc hca hcb haS hbS ‖v‖
      have hnw : ‖plScale c a b S ‖v‖ • v‖ = plFunc c a b S ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs1, plScale_mul hc]
      rw [hnw, smul_smul]
      have hprod : plScale c b a S (plFunc c a b S ‖v‖) * plScale c a b S ‖v‖ = 1 := by
        have h1 : plScale c b a S (plFunc c a b S ‖v‖) * plFunc c a b S ‖v‖ = ‖v‖ := by
          rw [plScale_mul hc, plFunc_invol hca hcb haS hbS]
        have h2 : (plScale c b a S (plFunc c a b S ‖v‖) * plScale c a b S ‖v‖) * ‖v‖ = 1 * ‖v‖ := by
          rw [mul_assoc, plScale_mul hc, h1, one_mul]
        exact mul_right_cancel₀ (ne_of_gt hnv) h2
      rw [hprod, one_smul]
  right_inv v := by
    dsimp only
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hs1 : 0 < plScale c b a S ‖v‖ := plScale_pos hc hcb hca hbS haS ‖v‖
      have hnw : ‖plScale c b a S ‖v‖ • v‖ = plFunc c b a S ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs1, plScale_mul hc]
      rw [hnw, smul_smul]
      have hprod : plScale c a b S (plFunc c b a S ‖v‖) * plScale c b a S ‖v‖ = 1 := by
        have h1 : plScale c a b S (plFunc c b a S ‖v‖) * plFunc c b a S ‖v‖ = ‖v‖ := by
          rw [plScale_mul hc, plFunc_invol hcb hca hbS haS]
        have h2 : (plScale c a b S (plFunc c b a S ‖v‖) * plScale c b a S ‖v‖) * ‖v‖ = 1 * ‖v‖ := by
          rw [mul_assoc, plScale_mul hc, h1, one_mul]
        exact mul_right_cancel₀ (ne_of_gt hnv) h2
      rw [hprod, one_smul]
  continuous_toFun :=
    ((plScale_continuous hc hca haS).comp continuous_norm).smul continuous_id
  continuous_invFun :=
    ((plScale_continuous hc hcb hbS).comp continuous_norm).smul continuous_id

lemma norm_radialAnnulusHomeo {n : ℕ} {c a b S : ℝ}
    (hc : 0 < c) (hca : c < a) (hcb : c < b) (haS : a < S) (hbS : b < S)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖radialAnnulusHomeo n c a b S hc hca hcb haS hbS v‖ = plFunc c a b S ‖v‖ := by
  change ‖plScale c a b S ‖v‖ • v‖ = plFunc c a b S ‖v‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (plScale_pos hc hca hcb haS hbS ‖v‖), plScale_mul hc]

lemma norm_radialAnnulusHomeo_symm {n : ℕ} {c a b S : ℝ}
    (hc : 0 < c) (hca : c < a) (hcb : c < b) (haS : a < S) (hbS : b < S)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖(radialAnnulusHomeo n c a b S hc hca hcb haS hbS).symm v‖ = plFunc c b a S ‖v‖ := by
  change ‖plScale c b a S ‖v‖ • v‖ = plFunc c b a S ‖v‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (plScale_pos hc hcb hca hbS haS ‖v‖), plScale_mul hc]

lemma radialAnnulusHomeo_eq_self_of_le {n : ℕ} {c a b S : ℝ}
    (hc : 0 < c) (hca : c < a) (hcb : c < b) (haS : a < S) (hbS : b < S)
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ c) :
    radialAnnulusHomeo n c a b S hc hca hcb haS hbS v = v := by
  change plScale c a b S ‖v‖ • v = v
  rw [plScale_eq_one_of_le hv, one_smul]

lemma radialAnnulusHomeo_eq_self_of_ge {n : ℕ} {c a b S : ℝ}
    (hc : 0 < c) (hca : c < a) (hcb : c < b) (haS : a < S) (hbS : b < S)
    {v : EuclideanSpace ℝ (Fin n)} (hv : S ≤ ‖v‖) :
    radialAnnulusHomeo n c a b S hc hca hcb haS hbS v = v := by
  change plScale c a b S ‖v‖ • v = v
  rw [plScale_eq_one_of_ge hc hca haS hv, one_smul]

end RadialHomeo

section ExtendHomeo

open Classical

/-- Turn an open embedding into a homeomorphism onto its range. -/
noncomputable def openEmbeddingHomeoRange {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) : X ≃ₜ range φ where
  toEquiv := Equiv.ofInjective φ hφ.injective
  continuous_toFun := hφ.continuous.subtype_mk _
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    have hpre : (Equiv.ofInjective φ hφ.injective).symm ⁻¹' U = Subtype.val ⁻¹' (φ '' U) := by
      ext ⟨y, hy⟩
      simp only [mem_preimage, mem_image]
      constructor
      · intro h
        refine ⟨(Equiv.ofInjective φ hφ.injective).symm ⟨y, hy⟩, h, ?_⟩
        exact congrArg Subtype.val ((Equiv.ofInjective φ hφ.injective).apply_symm_apply ⟨y, hy⟩)
      · rintro ⟨x, hx, hxy⟩
        have hEq : (⟨y, hy⟩ : range φ) = Equiv.ofInjective φ hφ.injective x := by
          ext; exact hxy.symm
        rw [hEq, Equiv.symm_apply_apply]
        exact hx
    change IsOpen ((Equiv.ofInjective φ hφ.injective).symm ⁻¹' U)
    rw [hpre]
    exact (hφ.isOpenMap U hU).preimage continuous_subtype_val

lemma openEmbeddingHomeoRange_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (x : X) :
    ((openEmbeddingHomeoRange hφ x) : Y) = φ x := rfl

lemma openEmbeddingHomeoRange_symm_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (x : X) :
    (openEmbeddingHomeoRange hφ).symm ⟨φ x, ⟨x, rfl⟩⟩ = x := by
  exact (openEmbeddingHomeoRange hφ).symm_apply_apply x

/-- Function underlying the extension of a compactly supported chart homeomorphism by identity. -/
noncomputable def extendFun {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    (φ : X → N) (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X) (y : N) : N :=
  if hy : y ∈ range φ then φ (ψ ((openEmbeddingHomeoRange hφ).symm ⟨y, hy⟩)) else y

lemma extendFun_apply_mem {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    {φ : X → N} (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X) (x : X) :
    extendFun φ hφ ψ (φ x) = φ (ψ x) := by
  unfold extendFun
  rw [dif_pos ⟨x, rfl⟩, openEmbeddingHomeoRange_symm_apply]

lemma extendFun_apply_not_mem {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    {φ : X → N} (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X) {y : N} (hy : y ∉ range φ) :
    extendFun φ hφ ψ y = y := by
  unfold extendFun
  rw [dif_neg hy]

lemma extendFun_continuous {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] [T2Space N]
    (φ : X → N) (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X)
    (K : Set X) (hK : IsCompact K) (hψ : ∀ x, x ∉ K → ψ x = x) :
    Continuous (extendFun φ hφ ψ) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ range φ
  · have hcontOn : ContinuousOn (extendFun φ hφ ψ) (range φ) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hEq : (range φ).domRestrict (extendFun φ hφ ψ) =
          fun z : range φ => φ (ψ ((openEmbeddingHomeoRange hφ).symm z)) := by
        funext ⟨z, hz⟩
        change extendFun φ hφ ψ z = _
        unfold extendFun
        rw [dif_pos hz]
      rw [hEq]
      exact hφ.continuous.comp (ψ.continuous.comp (openEmbeddingHomeoRange hφ).symm.continuous)
    exact hcontOn.continuousAt (hφ.isOpen_range.mem_nhds hy)
  · have hclosed : IsClosed (φ '' K) := (hK.image hφ.continuous).isClosed
    have hy_compl : y ∈ (φ '' K)ᶜ := by
      intro hmem
      exact hy (image_subset_range φ K hmem)
    have hnbhd : (φ '' K)ᶜ ∈ 𝓝 y := hclosed.isOpen_compl.mem_nhds hy_compl
    have hev : extendFun φ hφ ψ =ᶠ[𝓝 y] id := by
      filter_upwards [hnbhd] with z hz
      by_cases hzr : z ∈ range φ
      · rcases hzr with ⟨x, rfl⟩
        rw [extendFun_apply_mem]
        have hxK : x ∉ K := fun hx => hz ⟨x, hx, rfl⟩
        rw [hψ x hxK]
        rfl
      · rw [extendFun_apply_not_mem hφ ψ hzr]
        rfl
    exact continuousAt_id.congr hev.symm

/-- Extend a compactly supported homeomorphism along an open embedding into a T2 space. -/
noncomputable def extendHomeo {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] [T2Space N]
    (φ : X → N) (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X)
    (K : Set X) (hK : IsCompact K) (hψ : ∀ x, x ∉ K → ψ x = x) :
    N ≃ₜ N where
  toFun := extendFun φ hφ ψ
  invFun := extendFun φ hφ ψ.symm
  left_inv y := by
    by_cases hy : y ∈ range φ
    · rcases hy with ⟨x, rfl⟩
      rw [extendFun_apply_mem, extendFun_apply_mem, ψ.symm_apply_apply]
    · rw [extendFun_apply_not_mem hφ ψ hy, extendFun_apply_not_mem hφ ψ.symm hy]
  right_inv y := by
    by_cases hy : y ∈ range φ
    · rcases hy with ⟨x, rfl⟩
      rw [extendFun_apply_mem, extendFun_apply_mem, ψ.apply_symm_apply]
    · rw [extendFun_apply_not_mem hφ ψ.symm hy, extendFun_apply_not_mem hφ ψ hy]
  continuous_toFun := extendFun_continuous φ hφ ψ K hK hψ
  continuous_invFun := by
    refine extendFun_continuous φ hφ ψ.symm K hK ?_
    intro x hx
    have h1 : ψ x = x := hψ x hx
    calc ψ.symm x = ψ.symm (ψ x) := by rw [h1]
      _ = x := ψ.symm_apply_apply x

lemma extendHomeo_apply_mem {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] [T2Space N]
    {φ : X → N} (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X)
    (K : Set X) (hK : IsCompact K) (hψ : ∀ x, x ∉ K → ψ x = x) (x : X) :
    extendHomeo φ hφ ψ K hK hψ (φ x) = φ (ψ x) :=
  extendFun_apply_mem hφ ψ x

lemma extendHomeo_symm_apply_mem {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] [T2Space N]
    {φ : X → N} (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X)
    (K : Set X) (hK : IsCompact K) (hψ : ∀ x, x ∉ K → ψ x = x) (x : X) :
    (extendHomeo φ hφ ψ K hK hψ).symm (φ x) = φ (ψ.symm x) :=
  extendFun_apply_mem hφ ψ.symm x

lemma extendHomeo_mapsTo_of_range_subset {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [T2Space N] {φ : X → N} (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X)
    (K : Set X) (hK : IsCompact K) (hψ : ∀ x, x ∉ K → ψ x = x)
    {U : Set N} (hU : range φ ⊆ U) {y : N} (hy : y ∈ U) :
    extendHomeo φ hφ ψ K hK hψ y ∈ U := by
  by_cases hyr : y ∈ range φ
  · rcases hyr with ⟨x, rfl⟩
    rw [extendHomeo_apply_mem]
    exact hU ⟨ψ x, rfl⟩
  · change extendFun φ hφ ψ y ∈ U
    rw [extendFun_apply_not_mem hφ ψ hyr]
    exact hy

lemma extendHomeo_symm_mapsTo_of_range_subset {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [T2Space N] {φ : X → N} (hφ : IsOpenEmbedding φ) (ψ : X ≃ₜ X)
    (K : Set X) (hK : IsCompact K) (hψ : ∀ x, x ∉ K → ψ x = x)
    {U : Set N} (hU : range φ ⊆ U) {y : N} (hy : y ∈ U) :
    (extendHomeo φ hφ ψ K hK hψ).symm y ∈ U := by
  by_cases hyr : y ∈ range φ
  · rcases hyr with ⟨x, rfl⟩
    rw [extendHomeo_symm_apply_mem]
    exact hU ⟨ψ.symm x, rfl⟩
  · change extendFun φ hφ ψ.symm y ∈ U
    rw [extendFun_apply_not_mem hφ ψ.symm hyr]
    exact hy

end ExtendHomeo

section Engulfing

/-- Translation homeomorphism v ↦ v + x₀ on EuclideanSpace ℝ (Fin n). -/
def translateHomeo (n : ℕ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun v := v + x₀
  invFun v := v - x₀
  left_inv v := add_sub_cancel_right v x₀
  right_inv v := sub_add_cancel v x₀
  continuous_toFun := continuous_id.add continuous_const
  continuous_invFun := continuous_id.sub continuous_const

/-- Morton Brown's elementary radial-engulfing lemma (1961): given open Euclidean charts
f, g with range f ⊆ range g, a ball closedBall 0 r, and a compact set C ⊆ range g, there is
a homeomorphism Φ : N ≃ₜ N and S ≥ r + 1 such that Φ fixes f '' closedBall 0 r pointwise,
C ⊆ (Φ.symm ∘ f) '' closedBall 0 S, and range (Φ.symm ∘ f) ⊆ range g. -/
lemma brown_engulfing {n : ℕ} {N : Type*} [TopologicalSpace N] [T2Space N]
    {f g : EuclideanSpace ℝ (Fin n) → N} (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hfg : range f ⊆ range g) {r : ℝ} (hr : 0 < r)
    {C : Set N} (hC : IsCompact C) (hCg : C ⊆ range g) :
    ∃ (Φ : N ≃ₜ N) (S : ℝ),
      r + 1 ≤ S ∧
      (∀ x ∈ f '' Metric.closedBall 0 r, Φ x = x) ∧
      C ⊆ (Φ.symm ∘ f) '' Metric.closedBall 0 S ∧
      range (Φ.symm ∘ f) ⊆ range g := by
  let ef := openEmbeddingHomeoRange hf
  let eg := openEmbeddingHomeoRange hg
  let x₀ : EuclideanSpace ℝ (Fin n) := eg.symm ⟨f 0, hfg ⟨0, rfl⟩⟩
  have hgx₀ : g x₀ = f 0 := congrArg Subtype.val (eg.apply_symm_apply ⟨f 0, hfg ⟨0, rfl⟩⟩)
  -- Step 1: Choose ε > 0 with g '' closedBall x₀ (2 * ε) ⊆ range f.
  have hW_open : IsOpen (g ⁻¹' range f) := hf.isOpen_range.preimage hg.continuous
  have hx₀W : x₀ ∈ g ⁻¹' range f := by
    change g x₀ ∈ range f
    rw [hgx₀]
    exact ⟨0, rfl⟩
  obtain ⟨ε₁, hε₁, hball_ε₁⟩ := Metric.isOpen_iff.mp hW_open x₀ hx₀W
  set ε : ℝ := ε₁ / 3 with hε_def
  have hε : 0 < ε := by positivity
  have hg_2ε_sub : g '' Metric.closedBall x₀ (2 * ε) ⊆ range f := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ Metric.ball x₀ ε₁ := by
      rw [Metric.mem_closedBall] at hw
      rw [Metric.mem_ball]
      linarith
    exact hball_ε₁ hw'
  -- Step 2: Choose δ ∈ (0, r) with f '' closedBall 0 δ ⊆ g '' closedBall x₀ ε.
  have hV_open : IsOpen (f ⁻¹' (g '' Metric.ball x₀ ε)) :=
    (hg.isOpenMap _ Metric.isOpen_ball).preimage hf.continuous
  have h0V : (0 : EuclideanSpace ℝ (Fin n)) ∈ f ⁻¹' (g '' Metric.ball x₀ ε) := by
    change f 0 ∈ g '' Metric.ball x₀ ε
    rw [← hgx₀]
    exact ⟨x₀, Metric.mem_ball_self hε, rfl⟩
  obtain ⟨δ₁, hδ₁, hball_δ₁⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
  let δ : ℝ := min (δ₁ / 2) (r / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hf_δ_sub : f '' Metric.closedBall 0 δ ⊆ g '' Metric.closedBall x₀ ε := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ Metric.ball 0 δ₁ := by
      rw [Metric.mem_closedBall] at hv
      rw [Metric.mem_ball]
      have : δ ≤ δ₁ / 2 := min_le_left _ _
      linarith
    rcases hball_δ₁ hv' with ⟨w, hw, hgw⟩
    exact ⟨w, Metric.ball_subset_closedBall hw, hgw⟩
  -- Step 3: Choose S ≥ r + 1 with g '' closedBall x₀ (2 * ε) ⊆ f '' closedBall 0 S.
  let u₁ : Metric.closedBall x₀ (2 * ε) → EuclideanSpace ℝ (Fin n) :=
    fun w => ef.symm ⟨g w.1, hg_2ε_sub ⟨w.1, w.2, rfl⟩⟩
  have hu₁_cont : Continuous u₁ := by
    refine ef.symm.continuous.comp ?_
    exact (hg.continuous.comp continuous_subtype_val).subtype_mk _
  have : CompactSpace (Metric.closedBall x₀ (2 * ε)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall x₀ (2 * ε))
  have hK₁_bdd : Bornology.IsBounded (range u₁) := (isCompact_range hu₁_cont).isBounded
  obtain ⟨M₁, hM₁⟩ := hK₁_bdd.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  let S : ℝ := max (r + 1) M₁
  have hrS_le : r + 1 ≤ S := le_max_left _ _
  have hrS : r < S := by linarith
  have hδS : δ < S := lt_trans hδr hrS
  have hg_2ε_sub_fS : g '' Metric.closedBall x₀ (2 * ε) ⊆ f '' Metric.closedBall 0 S := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨u₁ ⟨w, hw⟩, ?_, ?_⟩
    · have hmem : u₁ ⟨w, hw⟩ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) M₁ :=
        hM₁ ⟨⟨w, hw⟩, rfl⟩
      rw [Metric.mem_closedBall] at hmem ⊢
      exact le_trans hmem (le_max_right _ _)
    · exact congrArg Subtype.val (ef.apply_symm_apply ⟨g w, hg_2ε_sub ⟨w, hw, rfl⟩⟩)
  -- Step 4: Construct H₁ supported in f '' closedBall 0 S shrinking closedBall 0 r into closedBall 0 δ.
  set c₁ : ℝ := δ / 2 with hc₁_def
  have hc₁ : 0 < c₁ := by positivity
  have hc₁δ : c₁ < δ := by linarith
  have hc₁r : c₁ < r := lt_trans hc₁δ hδr
  let ψ₁ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    radialAnnulusHomeo n c₁ r δ S hc₁ hc₁r hc₁δ hrS hδS
  have hψ₁_out : ∀ v, v ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) S → ψ₁ v = v := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    exact radialAnnulusHomeo_eq_self_of_ge hc₁ hc₁r hc₁δ hrS hδS (le_of_lt hv)
  let H₁ : N ≃ₜ N :=
    extendHomeo f hf ψ₁ (Metric.closedBall 0 S) (isCompact_closedBall 0 S) hψ₁_out
  have hH₁_r : H₁ '' (f '' Metric.closedBall 0 r) ⊆ g '' Metric.closedBall x₀ ε := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rw [extendHomeo_apply_mem]
    apply hf_δ_sub
    refine ⟨ψ₁ v, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hv ⊢
    rw [norm_radialAnnulusHomeo]
    exact plFunc_le_b hc₁r hc₁δ hv
  have hH₁_symm_S : H₁.symm '' (f '' Metric.closedBall 0 S) ⊆ f '' Metric.closedBall 0 S := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rw [extendHomeo_symm_apply_mem]
    refine ⟨ψ₁.symm v, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hv ⊢
    rw [norm_radialAnnulusHomeo_symm]
    exact plFunc_le_S hc₁δ hc₁r hδS hrS hv
  have hH₁_g : ∀ y ∈ range g, H₁ y ∈ range g :=
    fun _ hy => extendHomeo_mapsTo_of_range_subset hf ψ₁ _ _ hψ₁_out hfg hy
  have hH₁_symm_g : ∀ y ∈ range g, H₁.symm y ∈ range g :=
    fun _ hy => extendHomeo_symm_mapsTo_of_range_subset hf ψ₁ _ _ hψ₁_out hfg hy
  -- Step 5: Choose R > 2 * ε with H₁ '' C ⊆ g '' closedBall x₀ R.
  have hH₁C_sub_g : H₁ '' C ⊆ range g := by
    rintro _ ⟨y, hy, rfl⟩
    exact hH₁_g y (hCg hy)
  let u₂ : (H₁ '' C) → EuclideanSpace ℝ (Fin n) :=
    fun y => eg.symm ⟨y.1, hH₁C_sub_g y.2⟩
  have hu₂_cont : Continuous u₂ := by
    refine eg.symm.continuous.comp ?_
    exact continuous_subtype_val.subtype_mk _
  have : CompactSpace (H₁ '' C) :=
    isCompact_iff_compactSpace.mp (hC.image H₁.continuous)
  have hK₂_bdd : Bornology.IsBounded (range u₂) := (isCompact_range hu₂_cont).isBounded
  obtain ⟨M₂, hM₂⟩ := hK₂_bdd.subset_closedBall x₀
  let R : ℝ := max (2 * ε + 1) M₂
  have h2εR : 2 * ε < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hεR : ε < R := lt_trans (by linarith) h2εR
  have hε2ε : ε < 2 * ε := by linarith
  have hH₁C_sub_gR : H₁ '' C ⊆ g '' Metric.closedBall x₀ R := by
    intro y hy
    refine ⟨u₂ ⟨y, hy⟩, ?_, ?_⟩
    · have hmem : u₂ ⟨y, hy⟩ ∈ Metric.closedBall x₀ M₂ := hM₂ ⟨⟨y, hy⟩, rfl⟩
      rw [Metric.mem_closedBall] at hmem ⊢
      exact le_trans hmem (le_max_right _ _)
    · exact congrArg Subtype.val (eg.apply_symm_apply ⟨y, hH₁C_sub_g hy⟩)
  -- Step 6: Construct H₂ fixing g '' closedBall x₀ ε and shrinking g '' closedBall x₀ R into g '' closedBall x₀ (2 * ε).
  let S₂ : ℝ := R + 1
  have hRS₂ : R < S₂ := by linarith
  have h2εS₂ : 2 * ε < S₂ := lt_trans h2εR hRS₂
  let ψ₂_0 : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    radialAnnulusHomeo n ε R (2 * ε) S₂ hε hεR hε2ε hRS₂ h2εS₂
  let T := translateHomeo n x₀
  let ψ₂ : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (T.symm.trans ψ₂_0).trans T
  have hψ₂_out : ∀ w, w ∉ Metric.closedBall x₀ S₂ → ψ₂ w = w := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hw
    change ψ₂_0 (w - x₀) + x₀ = w
    rw [radialAnnulusHomeo_eq_self_of_ge hε hεR hε2ε hRS₂ h2εS₂ (le_of_lt hw), sub_add_cancel]
  let H₂ : N ≃ₜ N :=
    extendHomeo g hg ψ₂ (Metric.closedBall x₀ S₂) (isCompact_closedBall x₀ S₂) hψ₂_out
  have hH₂_fix : ∀ y ∈ g '' Metric.closedBall x₀ ε, H₂ y = y := by
    rintro _ ⟨w, hw, rfl⟩
    rw [extendHomeo_apply_mem]
    congr 1
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    change ψ₂_0 (w - x₀) + x₀ = w
    rw [radialAnnulusHomeo_eq_self_of_le hε hεR hε2ε hRS₂ h2εS₂ hw, sub_add_cancel]
  have hH₂_shrink : H₂ '' (g '' Metric.closedBall x₀ R) ⊆ g '' Metric.closedBall x₀ (2 * ε) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rw [extendHomeo_apply_mem]
    refine ⟨ψ₂ w, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
    change ‖ψ₂_0 (w - x₀) + x₀ - x₀‖ ≤ 2 * ε
    rw [add_sub_cancel_right, norm_radialAnnulusHomeo]
    exact plFunc_le_b hεR hε2ε hw
  have hH₂_symm_g : ∀ y ∈ range g, H₂.symm y ∈ range g :=
    fun _ hy => extendHomeo_symm_mapsTo_of_range_subset hg ψ₂ _ _ hψ₂_out (Subset.refl _) hy
  -- Step 7: Form the conjugate Φ = H₁⁻¹ ∘ H₂ ∘ H₁ and verify all four conclusions.
  let Φ : N ≃ₜ N := (H₁.trans H₂).trans H₁.symm
  refine ⟨Φ, S, hrS_le, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : H₁ x ∈ g '' Metric.closedBall x₀ ε := hH₁_r ⟨x, hx, rfl⟩
    change H₁.symm (H₂ (H₁ x)) = x
    rw [hH₂_fix (H₁ x) h1, H₁.symm_apply_apply]
  · intro y hy
    have h1 : H₁ y ∈ g '' Metric.closedBall x₀ R := hH₁C_sub_gR ⟨y, hy, rfl⟩
    have h2 : H₂ (H₁ y) ∈ g '' Metric.closedBall x₀ (2 * ε) := hH₂_shrink ⟨H₁ y, h1, rfl⟩
    have h3 : H₂ (H₁ y) ∈ f '' Metric.closedBall 0 S := hg_2ε_sub_fS h2
    have h4 : Φ y ∈ f '' Metric.closedBall 0 S := hH₁_symm_S ⟨H₂ (H₁ y), h3, rfl⟩
    rcases h4 with ⟨v, hv, hfv⟩
    refine ⟨v, hv, ?_⟩
    change Φ.symm (f v) = y
    rw [hfv, Φ.symm_apply_apply]
  · rintro _ ⟨v, rfl⟩
    change H₁.symm (H₂.symm (H₁ (f v))) ∈ range g
    exact hH₁_symm_g _ (hH₂_symm_g _ (hH₁_g _ (hfg ⟨v, rfl⟩)))

end Engulfing

section MainConstruction

/-- Inductive state for Brown's stabilizing sequence of Euclidean charts. -/
structure Stage (n : ℕ) (N : Type*) [TopologicalSpace N] (U : ℕ → Set N) where
  f : EuclideanSpace ℝ (Fin n) → N
  hf : IsOpenEmbedding f
  r : ℝ
  hr : 0 < r
  m : ℕ
  hsub : range f ⊆ U m

/-- One inductive step of Brown's construction, engulfing the compact set K_k. -/
noncomputable def nextStage {n : ℕ} {N : Type*} [TopologicalSpace N] [T2Space N]
    {U : ℕ → Set N} (hU_mono : Monotone U)
    (φ : ℕ → EuclideanSpace ℝ (Fin n) → N)
    (hφ : ∀ j, IsOpenEmbedding (φ j))
    (hφ_range : ∀ j, range (φ j) = U j)
    (k : ℕ) (st : Stage n N U) :
    { st' : Stage n N U //
      st.r + 1 ≤ st'.r ∧
      (∀ v ∈ Metric.closedBall 0 st.r, st'.f v = st.f v) ∧
      (φ (Nat.unpair k).1 '' Metric.closedBall 0 ((Nat.unpair k).2 : ℝ)) ⊆
        st'.f '' Metric.closedBall 0 st'.r } := by
  let i := (Nat.unpair k).1
  let rad : ℕ := (Nat.unpair k).2
  let m' := max st.m i
  let C : Set N := φ i '' Metric.closedBall 0 (rad : ℝ)
  have hC : IsCompact C := (isCompact_closedBall 0 (rad : ℝ)).image (hφ i).continuous
  have hfg : range st.f ⊆ range (φ m') := by
    rw [hφ_range m']
    exact st.hsub.trans (hU_mono (le_max_left st.m i))
  have hCg : C ⊆ range (φ m') := by
    rw [hφ_range m']
    exact (image_subset_range (φ i) _).trans (by rw [hφ_range i]; exact hU_mono (le_max_right st.m i))
  have hex := brown_engulfing st.hf (hφ m') hfg st.hr hC hCg
  let Φ : N ≃ₜ N := Classical.choose hex
  let S : ℝ := Classical.choose (Classical.choose_spec hex)
  have hspec := Classical.choose_spec (Classical.choose_spec hex)
  refine ⟨⟨Φ.symm ∘ st.f, Φ.symm.isOpenEmbedding.comp st.hf, S, by linarith [st.hr, hspec.1],
      m', by rw [← hφ_range m']; exact hspec.2.2.2⟩, hspec.1, ?_, hspec.2.2.1⟩
  intro v hv
  have hfix : Φ (st.f v) = st.f v := hspec.2.1 (st.f v) ⟨v, hv, rfl⟩
  change Φ.symm (st.f v) = st.f v
  calc Φ.symm (st.f v) = Φ.symm (Φ (st.f v)) := by rw [hfix]
    _ = st.f v := Φ.symm_apply_apply (st.f v)

/-- Recursive sequence of stages. -/
noncomputable def stageSeq {n : ℕ} {N : Type*} [TopologicalSpace N] [T2Space N]
    {U : ℕ → Set N} (hU_mono : Monotone U)
    (φ : ℕ → EuclideanSpace ℝ (Fin n) → N)
    (hφ : ∀ j, IsOpenEmbedding (φ j))
    (hφ_range : ∀ j, range (φ j) = U j) :
    ℕ → Stage n N U
  | 0 => ⟨φ 0, hφ 0, 1, one_pos, 0, by rw [hφ_range 0]⟩
  | k + 1 => (nextStage hU_mono φ hφ hφ_range k (stageSeq hU_mono φ hφ hφ_range k)).1

theorem brown_monotone_union (n : ℕ) (N : Type*) [TopologicalSpace N] [T2Space N]
    (U : ℕ → Set N)
    (hU : ∀ j, IsOpen (U j) ∧ Nonempty (↥(U j) ≃ₜ EuclideanSpace ℝ (Fin n)))
    (hU_inc : ∀ j, U j ⊆ U (j + 1))
    (hU_cov : (⋃ j, U j) = univ) :
    Nonempty (N ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  have hU_mono : Monotone U := monotone_nat_of_le_succ hU_inc
  let e : ∀ j, ↥(U j) ≃ₜ EuclideanSpace ℝ (Fin n) := fun j => Classical.choice (hU j).2
  let φ : ℕ → EuclideanSpace ℝ (Fin n) → N := fun j v => ((e j).symm v : N)
  have hφ : ∀ j, IsOpenEmbedding (φ j) := fun j =>
    (hU j).1.isOpenEmbedding_subtypeVal.comp (e j).symm.isOpenEmbedding
  have hφ_range : ∀ j, range (φ j) = U j := by
    intro j
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ((e j).symm v).2
    · intro hx
      refine ⟨e j ⟨x, hx⟩, ?_⟩
      change (((e j).symm (e j ⟨x, hx⟩)) : N) = x
      rw [(e j).symm_apply_apply]
  let st := stageSeq hU_mono φ hφ hφ_range
  let f : ℕ → EuclideanSpace ℝ (Fin n) → N := fun k => (st k).f
  let r : ℕ → ℝ := fun k => (st k).r
  have hr_step : ∀ k, r k + 1 ≤ r (k + 1) :=
    fun k => (nextStage hU_mono φ hφ hφ_range k (st k)).2.1
  have hf_step : ∀ k v, v ∈ Metric.closedBall 0 (r k) → f (k + 1) v = f k v :=
    fun k => (nextStage hU_mono φ hφ hφ_range k (st k)).2.2.1
  have hK_engulf : ∀ k,
      (φ (Nat.unpair k).1 '' Metric.closedBall 0 ((Nat.unpair k).2 : ℝ)) ⊆
        f (k + 1) '' Metric.closedBall 0 (r (k + 1)) :=
    fun k => (nextStage hU_mono φ hφ hφ_range k (st k)).2.2.2
  have hr_ge : ∀ k : ℕ, (k : ℝ) + 1 ≤ r k := by
    intro k
    induction k with
    | zero =>
      simp [r, st, stageSeq]
    | succ k ih =>
      push_cast
      linarith [hr_step k]
  have hr_mono : Monotone r :=
    monotone_nat_of_le_succ (fun k => by linarith [hr_step k])
  have hf_stab : ∀ {k j : ℕ}, k ≤ j → ∀ v ∈ Metric.closedBall 0 (r k), f j v = f k v := by
    intro k j hkj
    induction hkj with
    | refl => intro v _; rfl
    | @step m hkm ih =>
      intro v hv
      have hvm : v ∈ Metric.closedBall 0 (r m) := by
        rw [Metric.mem_closedBall, dist_zero_right] at hv ⊢
        exact le_trans hv (hr_mono hkm)
      rw [hf_step m v hvm, ih v hv]
  let F : EuclideanSpace ℝ (Fin n) → N := fun v => f ⌊‖v‖⌋₊ v
  have hF_eq : ∀ k v, v ∈ Metric.closedBall 0 (r k) → F v = f k v := by
    intro k v hv
    let j := ⌊‖v‖⌋₊
    have hvj : v ∈ Metric.closedBall 0 (r j) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_of_lt_of_le (Nat.lt_floor_add_one ‖v‖) (hr_ge j))
    rcases le_total j k with hjk | hkj
    · exact (hf_stab hjk v hvj).symm
    · exact hf_stab hkj v hv
  have hF_inj : Function.Injective F := by
    intro v w hvw
    let k := max ⌊‖v‖⌋₊ ⌊‖w‖⌋₊
    have hv : v ∈ Metric.closedBall 0 (r k) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖v‖ < (⌊‖v‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖v‖
      have h2 : ((⌊‖v‖⌋₊ : ℝ) + 1) ≤ (k : ℝ) + 1 :=
        add_le_add (Nat.cast_le.mpr (le_max_left _ _)) le_rfl
      exact le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (hr_ge k))
    have hw : w ∈ Metric.closedBall 0 (r k) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖w‖ < (⌊‖w‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖w‖
      have h2 : ((⌊‖w‖⌋₊ : ℝ) + 1) ≤ (k : ℝ) + 1 :=
        add_le_add (Nat.cast_le.mpr (le_max_right _ _)) le_rfl
      exact le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (hr_ge k))
    rw [hF_eq k v hv, hF_eq k w hw] at hvw
    exact (st k).hf.injective hvw
  have hF_surj : Function.Surjective F := by
    intro x
    have hxU : x ∈ ⋃ i, U i := by rw [hU_cov]; trivial
    rcases mem_iUnion.mp hxU with ⟨i, hxi⟩
    rw [← hφ_range i] at hxi
    rcases hxi with ⟨v, rfl⟩
    obtain ⟨m, hm⟩ := exists_nat_ge ‖v‖
    let k := Nat.pair i m
    have hmemK : φ i v ∈ φ (Nat.unpair k).1 '' Metric.closedBall 0 ((Nat.unpair k).2 : ℝ) := by
      dsimp only [k]
      rw [Nat.unpair_pair]
      exact ⟨v, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
    rcases hK_engulf k hmemK with ⟨w, hw, hfw⟩
    exact ⟨w, by rw [hF_eq (k + 1) w hw, hfw]⟩
  have hF_cont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro v
    let k := ⌊‖v‖⌋₊
    have hvk : v ∈ Metric.ball 0 (r k) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le (Nat.lt_floor_add_one ‖v‖) (hr_ge k)
    have hev : F =ᶠ[𝓝 v] f k := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hvk] with w hw
      exact hF_eq k w (Metric.ball_subset_closedBall hw)
    exact ((st k).hf.continuous.continuousAt).congr hev.symm
  have hF_open : IsOpenMap F := by
    intro W hW
    have hW_eq : W = ⋃ k : ℕ, (W ∩ Metric.ball 0 (r k)) := by
      ext v
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hv
        exact ⟨⌊‖v‖⌋₊, hv, lt_of_lt_of_le (Nat.lt_floor_add_one ‖v‖) (hr_ge ⌊‖v‖⌋₊)⟩
      · rintro ⟨_, hv, _⟩
        exact hv
    rw [hW_eq, image_iUnion]
    apply isOpen_iUnion
    intro k
    have himg : F '' (W ∩ Metric.ball 0 (r k)) = f k '' (W ∩ Metric.ball 0 (r k)) := by
      ext y
      simp only [mem_image]
      constructor
      · rintro ⟨v, ⟨hvW, hvb⟩, rfl⟩
        exact ⟨v, ⟨hvW, hvb⟩, (hF_eq k v (Metric.ball_subset_closedBall hvb)).symm⟩
      · rintro ⟨v, ⟨hvW, hvb⟩, rfl⟩
        exact ⟨v, ⟨hvW, hvb⟩, hF_eq k v (Metric.ball_subset_closedBall hvb)⟩
    rw [himg]
    exact (st k).hf.isOpenMap _ (hW.inter Metric.isOpen_ball)
  let eF : EuclideanSpace ℝ (Fin n) ≃ N := Equiv.ofBijective F ⟨hF_inj, hF_surj⟩
  have hinv_cont : Continuous eF.symm := by
    rw [continuous_def]
    intro W hW
    have hpre : eF.symm ⁻¹' W = F '' W := by
      ext x
      simp only [mem_preimage, mem_image]
      constructor
      · intro h
        exact ⟨eF.symm x, h, eF.apply_symm_apply x⟩
      · rintro ⟨v, hv, rfl⟩
        change eF.symm (eF v) ∈ W
        rwa [eF.symm_apply_apply]
    rw [hpre]
    exact hF_open W hW
  exact ⟨(Homeomorph.mk eF hF_cont hinv_cont).symm⟩

end MainConstruction

end BrownMonotoneUnion

open Set Topology

/-- Two points lie in a single Hausdorff member of the exhaustion. Since that
member is open, its separating neighborhoods are also open in the whole space. -/
theorem BrownMonotoneUnion.t2Space_of_open_exhaustion {X : Type*} [TopologicalSpace X]
    (V : ℕ → Set X) (hOpen : ∀ i, IsOpen (V i)) (hSep : ∀ i, T2Space (V i))
    (hMono : Monotone V) (hCover : (⋃ i, V i) = univ) : T2Space X := by
  constructor
  intro x y hxy
  obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hCover x
  obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hCover y
  let k := max i j
  let a : V k := ⟨x, hMono (le_max_left i j) hi⟩
  let b : V k := ⟨y, hMono (le_max_right i j) hj⟩
  letI : T2Space (V k) := hSep k
  have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
  obtain ⟨s, t, hs, ht, ha, hb, hst⟩ := t2_separation hab
  exact ⟨Subtype.val '' s, Subtype.val '' t,
    (hOpen k).isOpenMap_subtype_val _ hs, (hOpen k).isOpenMap_subtype_val _ ht,
    ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, Set.disjoint_image_of_injective Subtype.val_injective hst⟩

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2_H3_R1.H2 := by
  rintro n X _ ⟨V, hOpen, hCell, hInc, hCover⟩
  letI : T2Space X := BrownMonotoneUnion.t2Space_of_open_exhaustion V hOpen
    (fun i => (Classical.choice (hCell i)).isEmbedding.t2Space)
    (monotone_nat_of_le_succ hInc) hCover
  exact BrownMonotoneUnion.brown_monotone_union n X V (fun i => ⟨hOpen i, hCell i⟩) hInc hCover
