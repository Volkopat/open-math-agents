import OMAStatements.S_mo_249291
import Mathlib

open OMA.S_mo_249291

open scoped InnerProductSpace

lemma mo249291_mem {m : ℕ} (z c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hz : ‖z‖ = 1)
    (hr : 0 ≤ r) : ‖z - c‖ ≤ r ↔ (1 + ‖c‖ ^ 2 - r ^ 2) / 2 ≤ ⟪z, c⟫_ℝ := by
  rw [← sq_le_sq₀ (norm_nonneg _) hr, norm_sub_sq_real, hz]
  constructor <;> intro h <;> linarith

lemma mo249291_perp {m : ℕ} (hm : 1 ≤ m) (e : EuclideanSpace ℝ (Fin (m + 1))) (he : e ≠ 0) :
    ∃ u : EuclideanSpace ℝ (Fin (m + 1)), u ≠ 0 ∧ ⟪e, u⟫_ℝ = 0 := by
  have h1 := (ℝ ∙ e).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he, finrank_euclideanSpace_fin] at h1
  have hne : (ℝ ∙ e)ᗮ ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨u, hu0, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hu⟩

theorem OMA.solution : type_of% @OMA.S_mo_249291.main := by
  intro m hm c r ⟨e, he⟩ x hx y hy α β hα hβ hw
  obtain ⟨hx1, hxr⟩ := hx
  obtain ⟨hy1, hyr⟩ := hy
  have hr : 0 ≤ r := le_trans (norm_nonneg _) hxr
  have htx := (mo249291_mem x c hx1 hr).1 hxr
  have hty := (mo249291_mem y c hy1 hr).1 hyr
  have hwpos : 0 < ‖α • x + β • y‖ := norm_pos_iff.2 hw
  have hz1 : ‖‖α • x + β • y‖⁻¹ • (α • x + β • y)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  refine ⟨hz1, (mo249291_mem _ c hz1 hr).2 ?_⟩
  rw [real_inner_smul_left]
  have hwc : ⟪α • x + β • y, c⟫_ℝ = α * ⟪x, c⟫_ℝ + β * ⟪y, c⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hwn : ‖α • x + β • y‖ ≤ α + β := by
    calc ‖α • x + β • y‖ ≤ ‖α • x‖ + ‖β • y‖ := norm_add_le _ _
      _ = α + β := by
        rw [norm_smul, norm_smul, hx1, hy1, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]
        ring
  rcases lt_or_ge 0 ((1 + ‖c‖ ^ 2 - r ^ 2) / 2) with ht | ht
  · rw [le_inv_mul_iff₀ hwpos, hwc]
    nlinarith
  · exfalso
    have he0 : e ≠ 0 := by
      intro h
      have := he x hx1 hxr
      rw [h, inner_zero_right] at this
      linarith
    obtain ⟨v, hv0, hvc, hve⟩ : ∃ v : EuclideanSpace ℝ (Fin (m + 1)),
        v ≠ 0 ∧ 0 ≤ ⟪v, c⟫_ℝ ∧ ⟪v, e⟫_ℝ ≤ 0 := by
      by_cases hce : ⟪c, e⟫_ℝ < 0
      · refine ⟨-e, neg_ne_zero.2 he0, ?_, ?_⟩
        · rw [inner_neg_left, real_inner_comm]; linarith
        · rw [inner_neg_left, real_inner_self_eq_norm_sq]; nlinarith [norm_nonneg e]
      · push Not at hce
        by_cases hv : (‖e‖ ^ 2) • c - ⟪c, e⟫_ℝ • e = 0
        · obtain ⟨u, hu0, hue⟩ := mo249291_perp hm e he0
          refine ⟨u, hu0, ?_, by rw [real_inner_comm, hue]⟩
          have h2 := congrArg (fun z => ⟪u, z⟫_ℝ) hv
          have hue' : ⟪u, e⟫_ℝ = 0 := by rw [real_inner_comm]; exact hue
          simp only [inner_sub_right, real_inner_smul_right, inner_zero_right, hue', mul_zero,
            sub_zero] at h2
          have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 he0)
          have : ⟪u, c⟫_ℝ = 0 := by
            rcases mul_eq_zero.1 h2 with h | h
            · exact absurd h hne
            · exact h
          rw [this]
        · refine ⟨_, hv, ?_, ?_⟩
          · rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
              real_inner_self_eq_norm_sq, real_inner_comm e c]
            have := real_inner_mul_inner_self_le c e
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
            have hce' : ⟪e, c⟫_ℝ = ⟪c, e⟫_ℝ := real_inner_comm c e
            rw [hce']
            nlinarith [this]
          · rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
              real_inner_self_eq_norm_sq]
            ring_nf; rfl
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hx01 : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    have hx0r : ‖‖v‖⁻¹ • v - c‖ ≤ r := by
      refine (mo249291_mem _ c hx01 hr).2 ?_
      rw [real_inner_smul_left]
      have := mul_nonneg (inv_nonneg.2 (norm_nonneg v)) hvc
      linarith
    have h3 := he _ hx01 hx0r
    rw [real_inner_smul_left] at h3
    have h4 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg v)) hve
    linarith
