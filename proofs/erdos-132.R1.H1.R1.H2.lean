import OMAReductions.R_erdos_132_R1_H1_R1

open scoped Classical

namespace HopfPannwitz

abbrev P2 := EuclideanSpace ℝ (Fin 2)

def det2 (u v : P2) : ℝ := u 0 * v 1 - u 1 * v 0

lemma inner_eq (u v : P2) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma norm_sq_eq (u : P2) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]
  ring

lemma lagrange (u v : P2) : (det2 u v) ^ 2 + (inner ℝ u v) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [det2, inner_eq, norm_sq_eq]
  ring

lemma norm_sub_sq_2d (u v : P2) : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
  simp only [norm_sq_eq, inner_eq, PiLp.sub_apply]
  ring

lemma norm_add_sq_2d (u v : P2) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2 := by
  simp only [norm_sq_eq, inner_eq, PiLp.add_apply]
  ring

lemma norm_lincomb_sq_2d (a b : ℝ) (u v : P2) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 + 2 * a * b * inner ℝ u v + b ^ 2 * ‖v‖ ^ 2 := by
  simp only [norm_sq_eq, inner_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma inner_lincomb_left_2d (a b : ℝ) (u v w : P2) :
    inner ℝ (a • u + b • v) w = a * inner ℝ u w + b * inner ℝ v w := by
  simp only [inner_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma cramer_2d {u v : P2} (h : det2 u v ≠ 0) (w : P2) :
    w = (det2 w v / det2 u v) • u + (det2 u w / det2 u v) • v := by
  ext i
  have h' : u 0 * v 1 - u 1 * v 0 ≠ 0 := h
  fin_cases i
  · simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det2]
    have hnum : (w 0 * v 1 - w 1 * v 0) * u 0 + (u 0 * w 1 - u 1 * w 0) * v 0 =
        w 0 * (u 0 * v 1 - u 1 * v 0) := by ring
    calc w 0 = w 0 * (u 0 * v 1 - u 1 * v 0) / (u 0 * v 1 - u 1 * v 0) :=
          (mul_div_cancel_right₀ _ h').symm
      _ = ((w 0 * v 1 - w 1 * v 0) * u 0 + (u 0 * w 1 - u 1 * w 0) * v 0) /
          (u 0 * v 1 - u 1 * v 0) := by rw [hnum]
      _ = (w 0 * v 1 - w 1 * v 0) / (u 0 * v 1 - u 1 * v 0) * u 0 +
          (u 0 * w 1 - u 1 * w 0) / (u 0 * v 1 - u 1 * v 0) * v 0 := by ring
  · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det2]
    have hnum : (w 0 * v 1 - w 1 * v 0) * u 1 + (u 0 * w 1 - u 1 * w 0) * v 1 =
        w 1 * (u 0 * v 1 - u 1 * v 0) := by ring
    calc w 1 = w 1 * (u 0 * v 1 - u 1 * v 0) / (u 0 * v 1 - u 1 * v 0) :=
          (mul_div_cancel_right₀ _ h').symm
      _ = ((w 0 * v 1 - w 1 * v 0) * u 1 + (u 0 * w 1 - u 1 * w 0) * v 1) /
          (u 0 * v 1 - u 1 * v 0) := by rw [hnum]
      _ = (w 0 * v 1 - w 1 * v 0) / (u 0 * v 1 - u 1 * v 0) * u 1 +
          (u 0 * w 1 - u 1 * w 0) / (u 0 * v 1 - u 1 * v 0) * v 1 := by ring

lemma basis_unique_2d {u v : P2} (h : det2 u v ≠ 0) {a₁ b₁ a₂ b₂ : ℝ}
    (heq : a₁ • u + b₁ • v = a₂ • u + b₂ • v) : a₁ = a₂ ∧ b₁ = b₂ := by
  have h0 : (a₁ • u + b₁ • v) 0 = (a₂ • u + b₂ • v) 0 := congrArg (fun p : P2 => p 0) heq
  have h1 : (a₁ • u + b₁ • v) 1 = (a₂ • u + b₂ • v) 1 := congrArg (fun p : P2 => p 1) heq
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  have hdet : u 0 * v 1 - u 1 * v 0 ≠ 0 := h
  have ha : (a₁ - a₂) * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination v 1 * h0 - v 0 * h1
  have hb : (b₁ - b₂) * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination -u 1 * h0 + u 0 * h1
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right hdet)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hdet)

lemma parallel_eq_or_neg {d : ℝ} {u v : P2}
    (hu : ‖u‖ = d) (hv : ‖v‖ = d) (hdet : det2 u v = 0) : u = v ∨ v = -u := by
  have hlag := lagrange u v
  rw [hdet, hu, hv] at hlag
  have hsq : (inner ℝ u v) ^ 2 = (d ^ 2) ^ 2 := by nlinarith only [hlag]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hin | hin
  · left
    have hns : ‖u - v‖ ^ 2 = 0 := by
      rw [norm_sub_sq_2d, hu, hv, hin]; ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hns))
  · right
    have hns : ‖u + v‖ ^ 2 = 0 := by
      rw [norm_add_sq_2d, hu, hv, hin]; ring
    exact eq_neg_of_add_eq_zero_right (norm_eq_zero.mp (sq_eq_zero_iff.mp hns))

lemma no_parallel_diam {d : ℝ} {a b c e : P2}
    (hab : dist a b = d) (hce : dist c e = d)
    (hac : dist a c ≤ d) (hae : dist a e ≤ d) (hbc : dist b c ≤ d) (hbe : dist b e ≤ d)
    (hne_ac : a ≠ c) (hne_ae : a ≠ e)
    (hdet : det2 (b - a) (e - c) = 0) : False := by
  have hu : ‖b - a‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hab
  have hv : ‖e - c‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hce
  rcases parallel_eq_or_neg hu hv hdet with hpar | hpar
  · have h1 : a - e = (a - c) - (b - a) := by
      have : e = c + (b - a) := eq_add_of_sub_eq' hpar.symm
      rw [this]; abel
    have h2 : b - c = (a - c) + (b - a) := by abel
    have hsum : ‖a - e‖ ^ 2 + ‖b - c‖ ^ 2 = 2 * ‖a - c‖ ^ 2 + 2 * d ^ 2 := by
      rw [h1, h2, norm_sub_sq_2d, norm_add_sq_2d, hu]; ring
    have hpos : 0 < ‖a - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne_ac)
    have hae' : ‖a - e‖ ≤ d := by rwa [← dist_eq_norm]
    have hbc' : ‖b - c‖ ≤ d := by rwa [← dist_eq_norm]
    nlinarith [norm_nonneg (a - e), norm_nonneg (b - c)]
  · have h1 : a - c = (a - e) - (b - a) := by
      have : c = e + (b - a) := by
        have h' : c - e = b - a := by rw [← neg_sub e c, hpar, neg_neg]
        exact eq_add_of_sub_eq' h'
      rw [this]; abel
    have h2 : b - e = (a - e) + (b - a) := by abel
    have hsum : ‖a - c‖ ^ 2 + ‖b - e‖ ^ 2 = 2 * ‖a - e‖ ^ 2 + 2 * d ^ 2 := by
      rw [h1, h2, norm_sub_sq_2d, norm_add_sq_2d, hu]; ring
    have hpos : 0 < ‖a - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne_ae)
    have hac' : ‖a - c‖ ≤ d := by rwa [← dist_eq_norm]
    have hbe' : ‖b - e‖ ≤ d := by rwa [← dist_eq_norm]
    nlinarith [norm_nonneg (a - c), norm_nonneg (b - e)]

lemma no_both_neg {d : ℝ} (hd : 0 < d) {a b c e : P2}
    (hab : dist a b = d) (hce : dist c e = d)
    (hae : dist a e ≤ d) (hbc : dist b c ≤ d)
    (hdet : det2 (b - a) (e - c) ≠ 0)
    {t s : ℝ} (ht : t < 0) (hs : s < 0)
    (hp : a + t • (b - a) = c + s • (e - c)) : False := by
  set u := b - a
  set v := e - c
  set p := a + t • u
  have hp' : p = c + s • v := hp
  have hu : ‖u‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hab
  have hv : ‖v‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hce
  have hap : a - p = (-t) • u := by simp only [p]; module
  have hbp : b - p = (1 - t) • u := by simp only [p, u]; module
  have hcp : c - p = (-s) • v := by rw [hp']; module
  have hep : e - p = (1 - s) • v := by rw [hp']; simp only [v]; module
  have hnap : ‖a - p‖ = (-t) * d := by
    rw [hap, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hu]
  have hnbp : ‖b - p‖ = (1 - t) * d := by
    rw [hbp, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hu]
  have hncp : ‖c - p‖ = (-s) * d := by
    rw [hcp, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hv]
  have hnep : ‖e - p‖ = (1 - s) * d := by
    rw [hep, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hv]
  have htri1 : ‖b - p‖ ≤ ‖b - c‖ + ‖c - p‖ := by
    have : b - p = (b - c) + (c - p) := by abel
    rw [this]; exact norm_add_le _ _
  have htri2 : ‖e - p‖ ≤ ‖e - a‖ + ‖a - p‖ := by
    have : e - p = (e - a) + (a - p) := by abel
    rw [this]; exact norm_add_le _ _
  have hbc' : ‖b - c‖ ≤ d := by rwa [← dist_eq_norm]
  have hea' : ‖e - a‖ ≤ d := by rw [← dist_eq_norm, dist_comm]; exact hae
  have hst : s = t := by nlinarith
  set r := -t
  have hr : 0 < r := by linarith
  have hbc_vec : b - c = (r + 1) • u + (-r) • v := by
    have : b - c = (b - p) - (c - p) := by abel
    rw [this, hbp, hcp, hst]
    simp only [r]
    module
  have hbc_sq : ‖b - c‖ ^ 2 = d ^ 2 + 2 * (r + 1) * r * (d ^ 2 - inner ℝ u v) := by
    rw [hbc_vec, norm_lincomb_sq_2d, hu, hv]; ring
  have hbc_le : ‖b - c‖ ^ 2 ≤ d ^ 2 := by nlinarith only [hbc', norm_nonneg (b - c)]
  have hin_ge : d ^ 2 ≤ inner ℝ u v := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < 2 * (r + 1) * r * (d ^ 2 - inner ℝ u v) :=
      mul_pos (by positivity) (by linarith)
    linarith
  have hlag := lagrange u v
  rw [hu, hv] at hlag
  have hdet_pos : 0 < (det2 u v) ^ 2 := sq_pos_of_ne_zero hdet
  nlinarith only [hlag, hdet_pos, hin_ge, hd]

lemma no_neg_param {d : ℝ} (hd : 0 < d) {a b c e : P2}
    (hab : dist a b = d) (hce : dist c e = d)
    (hac : dist a c ≤ d) (hae : dist a e ≤ d) (hbc : dist b c ≤ d) (hbe : dist b e ≤ d)
    (hdet : det2 (b - a) (e - c) ≠ 0)
    {t s : ℝ} (hp : a + t • (b - a) = c + s • (e - c)) : 0 ≤ t := by
  by_contra hlt
  push Not at hlt
  rcases lt_trichotomy s 0 with hs0 | rfl | hs0
  · exact no_both_neg hd hab hce hae hbc hdet hlt hs0 hp
  · have hbp : b - c = (1 - t) • (b - a) := by
      have : a + t • (b - a) = c := by simpa using hp
      have : b - c = b - (a + t • (b - a)) := by rw [this]
      rw [this]; module
    have hnbp : ‖b - c‖ = (1 - t) * d := by
      rw [hbp, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), ← dist_eq_norm,
        dist_comm, hab]
    have hbc' : ‖b - c‖ ≤ d := by rwa [← dist_eq_norm]
    nlinarith
  · by_cases hs1 : s ≤ 1
    · set p := a + t • (b - a)
      have hp' : p = c + s • (e - c) := hp
      have hbp1 : b - p = (1 - t) • (b - a) := by simp only [p]; module
      have hbp2 : b - p = (1 - s) • (b - c) + s • (b - e) := by
        rw [hp']; module
      have hnorm1 : ‖b - p‖ = (1 - t) * d := by
        rw [hbp1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), ← dist_eq_norm,
          dist_comm, hab]
      have hnorm2 : ‖b - p‖ ≤ (1 - s) * ‖b - c‖ + s * ‖b - e‖ := by
        rw [hbp2]
        calc ‖(1 - s) • (b - c) + s • (b - e)‖
            ≤ ‖(1 - s) • (b - c)‖ + ‖s • (b - e)‖ := norm_add_le _ _
          _ = (1 - s) * ‖b - c‖ + s * ‖b - e‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      have hbc' : ‖b - c‖ ≤ d := by rwa [← dist_eq_norm]
      have hbe' : ‖b - e‖ ≤ d := by rwa [← dist_eq_norm]
      nlinarith
    · push Not at hs1
      have hdet' : det2 (b - a) (c - e) ≠ 0 := by
        intro h0
        apply hdet
        have : det2 (b - a) (e - c) = -det2 (b - a) (c - e) := by
          simp only [det2, PiLp.sub_apply]; ring
        rw [this, h0, neg_zero]
      have hp' : a + t • (b - a) = e + (1 - s) • (c - e) := by
        rw [hp]; module
      exact no_both_neg hd hab (by rwa [dist_comm]) hac hbe hdet' hlt (by linarith) hp'

/-- Key Lemma A: Two disjoint diameter segments in the plane must intersect. -/
lemma diam_segments_intersect {d : ℝ} (hd : 0 < d) {a b c e : P2}
    (hab : dist a b = d) (hce : dist c e = d)
    (hac : dist a c ≤ d) (hae : dist a e ≤ d) (hbc : dist b c ≤ d) (hbe : dist b e ≤ d)
    (hne_ac : a ≠ c) (hne_ae : a ≠ e) :
    ∃ t s : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ s ∧ s ≤ 1 ∧
      (1 - t) • a + t • b = (1 - s) • c + s • e := by
  have hdet : det2 (b - a) (e - c) ≠ 0 :=
    fun h0 => no_parallel_diam hab hce hac hae hbc hbe hne_ac hne_ae h0
  set u := b - a
  set v := e - c
  set t := det2 (c - a) v / det2 u v
  set s := -(det2 u (c - a) / det2 u v)
  have hcr : c - a = t • u + (-s) • v := by
    have := cramer_2d hdet (c - a)
    simpa only [t, s, neg_neg] using this
  have hp : a + t • u = c + s • v := by
    have h1 : c = a + (t • u + (-s) • v) := eq_add_of_sub_eq' hcr
    rw [h1]; module
  have ht0 : 0 ≤ t := no_neg_param hd hab hce hac hae hbc hbe hdet hp
  have hdet_ba : det2 (a - b) (e - c) ≠ 0 := by
    intro h0; apply hdet
    have : det2 (b - a) (e - c) = -det2 (a - b) (e - c) := by
      simp only [det2, PiLp.sub_apply]; ring
    rw [this, h0, neg_zero]
  have hp_ba : b + (1 - t) • (a - b) = c + s • (e - c) := by
    rw [← hp]; simp only [u]; module
  have ht1 : t ≤ 1 := by
    have := no_neg_param hd (by rwa [dist_comm]) hce hbc hbe hac hae hdet_ba hp_ba
    linarith
  have hdet_ce : det2 (e - c) (b - a) ≠ 0 := by
    intro h0; apply hdet
    have : det2 (b - a) (e - c) = -det2 (e - c) (b - a) := by
      simp only [det2, PiLp.sub_apply]; ring
    rw [this, h0, neg_zero]
  have hs0 : 0 ≤ s :=
    no_neg_param hd hce hab (by rwa [dist_comm]) (by rwa [dist_comm])
      (by rwa [dist_comm]) (by rwa [dist_comm]) hdet_ce hp.symm
  have hdet_ec : det2 (c - e) (b - a) ≠ 0 := by
    intro h0; apply hdet
    have : det2 (b - a) (e - c) = det2 (c - e) (b - a) := by
      simp only [det2, PiLp.sub_apply]; ring
    rw [this, h0]
  have hp_ec : e + (1 - s) • (c - e) = a + t • (b - a) := by
    rw [hp]; simp only [v]; module
  have hs1 : s ≤ 1 := by
    have := no_neg_param hd (by rwa [dist_comm]) hab (by rwa [dist_comm]) (by rwa [dist_comm])
      (by rwa [dist_comm]) (by rwa [dist_comm]) hdet_ec hp_ec
    linarith
  refine ⟨t, s, ht0, ht1, hs0, hs1, ?_⟩
  have hL : (1 - t) • a + t • b = a + t • u := by simp only [u]; module
  have hR : (1 - s) • c + s • e = c + s • v := by simp only [v]; module
  rw [hL, hR, hp]

/-- Key Lemma B: Among three diameter-neighbors of x, the middle one has no other diameter-neighbor. -/
lemma middle_neighbor_unique {d : ℝ} (hd : 0 < d) {x y₁ y₂ y₃ w : P2}
    (hx1 : dist x y₁ = d) (hx2 : dist x y₂ = d) (hx3 : dist x y₃ = d)
    (h12_ne : y₁ ≠ y₂) (h13_ne : y₁ ≠ y₃) (h23_ne : y₂ ≠ y₃)
    (h12_le : dist y₁ y₂ ≤ d) (h13_le : dist y₁ y₃ ≤ d) (h23_le : dist y₂ y₃ ≤ d)
    (hmin12 : inner ℝ (y₁ - x) (y₃ - x) ≤ inner ℝ (y₁ - x) (y₂ - x))
    (hmin23 : inner ℝ (y₁ - x) (y₃ - x) ≤ inner ℝ (y₂ - x) (y₃ - x))
    (hw2 : dist y₂ w = d)
    (hwx : dist x w ≤ d) (hw1 : dist y₁ w ≤ d) (hw3 : dist y₃ w ≤ d) :
    w = x := by
  set u₁ := y₁ - x
  set u₂ := y₂ - x
  set u₃ := y₃ - x
  have hu1 : ‖u₁‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hx1
  have hu2 : ‖u₂‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hx2
  have hu3 : ‖u₃‖ = d := by rw [← dist_eq_norm, dist_comm]; exact hx3
  have hin_bounds : ∀ {a b : P2}, ‖a‖ = d → ‖b‖ = d → a ≠ b → ‖a - b‖ ≤ d →
      d ^ 2 ≤ 2 * inner ℝ a b ∧ inner ℝ a b < d ^ 2 := by
    intro a b ha hb hne hle
    have hsq := norm_sub_sq_2d a b
    rw [ha, hb] at hsq
    have hpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hle2 : ‖a - b‖ ^ 2 ≤ d ^ 2 := by nlinarith [norm_nonneg (a - b)]
    constructor <;> nlinarith
  have h12_u : u₁ - u₂ = y₁ - y₂ := by simp only [u₁, u₂]; abel
  have h13_u : u₁ - u₃ = y₁ - y₃ := by simp only [u₁, u₃]; abel
  have h23_u : u₂ - u₃ = y₂ - y₃ := by simp only [u₂, u₃]; abel
  have ⟨hc12_lo, hc12_hi⟩ := hin_bounds hu1 hu2
    (fun h => h12_ne (sub_eq_zero.mp (by rw [← h12_u, h, sub_self])))
    (by rw [h12_u, ← dist_eq_norm]; exact h12_le)
  have ⟨hc13_lo, hc13_hi⟩ := hin_bounds hu1 hu3
    (fun h => h13_ne (sub_eq_zero.mp (by rw [← h13_u, h, sub_self])))
    (by rw [h13_u, ← dist_eq_norm]; exact h13_le)
  have ⟨hc23_lo, hc23_hi⟩ := hin_bounds hu2 hu3
    (fun h => h23_ne (sub_eq_zero.mp (by rw [← h23_u, h, sub_self])))
    (by rw [h23_u, ← dist_eq_norm]; exact h23_le)
  set c₁₂ := inner ℝ u₁ u₂
  set c₁₃ := inner ℝ u₁ u₃
  set c₂₃ := inner ℝ u₂ u₃
  have hdet13 : det2 u₁ u₃ ≠ 0 := by
    intro h0
    have hlag := lagrange u₁ u₃
    rw [h0, hu1, hu3] at hlag
    nlinarith only [hlag, hc13_lo, hc13_hi, hd]
  set α := det2 u₂ u₃ / det2 u₁ u₃
  set β := det2 u₁ u₂ / det2 u₁ u₃
  have hu2_eq : u₂ = α • u₁ + β • u₃ := cramer_2d hdet13 u₂
  have hlin1 : c₁₂ = α * d ^ 2 + β * c₁₃ := by
    have h1 : inner ℝ u₂ u₁ = c₁₂ := real_inner_comm u₁ u₂
    rw [← h1, hu2_eq, inner_lincomb_left_2d, real_inner_self_eq_norm_sq, hu1, real_inner_comm u₁ u₃]
  have hlin3 : c₂₃ = α * c₁₃ + β * d ^ 2 := by
    rw [show c₂₃ = inner ℝ u₂ u₃ from rfl, hu2_eq, inner_lincomb_left_2d,
      real_inner_self_eq_norm_sq, hu3]
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hc13_pos : 0 < c₁₃ := by linarith
  have hden_pos : 0 < d ^ 4 - c₁₃ ^ 2 := by nlinarith only [hc13_pos, hc13_hi, hd2]
  have hα_pos : 0 < α := by
    have hnum : d ^ 2 * c₁₂ - c₁₃ * c₂₃ = α * (d ^ 4 - c₁₃ ^ 2) := by
      rw [hlin1, hlin3]; ring
    have hpos : 0 < d ^ 2 * c₁₂ - c₁₃ * c₂₃ := by
      nlinarith only [hc13_pos, hc23_hi, hmin12, hd2]
    nlinarith only [hnum, hpos, hden_pos]
  have hβ_pos : 0 < β := by
    have hnum : d ^ 2 * c₂₃ - c₁₃ * c₁₂ = β * (d ^ 4 - c₁₃ ^ 2) := by
      rw [hlin1, hlin3]; ring
    have hpos : 0 < d ^ 2 * c₂₃ - c₁₃ * c₁₂ := by
      nlinarith only [hc13_pos, hc12_hi, hmin23, hd2]
    nlinarith only [hnum, hpos, hden_pos]
  have hαβ_gt : 1 < α + β := by
    have hns : d ^ 2 = α ^ 2 * d ^ 2 + 2 * α * β * c₁₃ + β ^ 2 * d ^ 2 := by
      have := norm_lincomb_sq_2d α β u₁ u₃
      rw [← hu2_eq, hu1, hu2, hu3] at this
      exact this
    have hdiff : 0 < 2 * α * β * (d ^ 2 - c₁₃) :=
      mul_pos (by positivity) (by linarith)
    have hsq : d ^ 2 < (α + β) ^ 2 * d ^ 2 := by linarith
    have hgt1 : 1 < (α + β) ^ 2 := by nlinarith only [hsq, hd2]
    nlinarith only [hgt1, hα_pos, hβ_pos]
  by_contra hwx_ne
  have hwy1 : w ≠ y₁ := by
    intro h
    subst h
    have hdist : ‖u₁ - u₂‖ ^ 2 = d ^ 2 := by
      rw [h12_u, ← dist_eq_norm, dist_comm, hw2]
    have hsq := norm_sub_sq_2d u₁ u₂
    rw [hu1, hu2, hdist] at hsq
    have hc12_eq : 2 * c₁₂ = d ^ 2 := by linarith
    have hc13_eq : 2 * c₁₃ = d ^ 2 := by linarith
    have hzero_d : (1 - 2 * α - β) * d ^ 2 = 0 := by
      linear_combination 2 * hlin1 - hc12_eq + β * hc13_eq
    have hsum1 : 1 - 2 * α - β = 0 := (mul_eq_zero.mp hzero_d).resolve_right (ne_of_gt hd2)
    linarith
  have hwy3 : w ≠ y₃ := by
    intro h
    subst h
    have hdist : ‖u₂ - u₃‖ ^ 2 = d ^ 2 := by
      rw [h23_u, ← dist_eq_norm, hw2]
    have hsq := norm_sub_sq_2d u₂ u₃
    rw [hu2, hu3, hdist] at hsq
    have hc23_eq : 2 * c₂₃ = d ^ 2 := by linarith
    have hc13_eq : 2 * c₁₃ = d ^ 2 := by linarith
    have hzero_d : (1 - α - 2 * β) * d ^ 2 = 0 := by
      linear_combination 2 * hlin3 - hc23_eq + α * hc13_eq
    have hsum1 : 1 - α - 2 * β = 0 := (mul_eq_zero.mp hzero_d).resolve_right (ne_of_gt hd2)
    linarith
  have hxy2 : x ≠ y₂ := fun h => by rw [h, dist_self] at hx2; linarith
  obtain ⟨t₁, l₁, ht₁0, _, hl₁0, _, heq1⟩ :=
    diam_segments_intersect hd hx1 hw2 (le_of_eq hx2) hwx h12_le hw1 hxy2 (Ne.symm hwx_ne)
  obtain ⟨t₃, l₃, ht₃0, _, hl₃0, _, heq3⟩ :=
    diam_segments_intersect hd hx3 hw2 (le_of_eq hx2) hwx (by rwa [dist_comm]) hw3 hxy2
      (Ne.symm hwx_ne)
  set a := det2 (w - x) u₃ / det2 u₁ u₃
  set b := det2 u₁ (w - x) / det2 u₁ u₃
  have hwx_eq : w - x = a • u₁ + b • u₃ := cramer_2d hdet13 (w - x)
  have hsub1 : t₁ • u₁ + (0 : ℝ) • u₃ =
      ((1 - l₁) * α + l₁ * a) • u₁ + ((1 - l₁) * β + l₁ * b) • u₃ := by
    have h1 : t₁ • u₁ = (1 - l₁) • u₂ + l₁ • (w - x) := by
      have : ((1 - t₁) • x + t₁ • y₁) - x = ((1 - l₁) • y₂ + l₁ • w) - x :=
        congrArg (fun p : P2 => p - x) heq1
      convert this using 1 <;> simp only [u₁, u₂] <;> module
    rw [zero_smul, add_zero, h1, hu2_eq, hwx_eq]; module
  have hsub3 : (0 : ℝ) • u₁ + t₃ • u₃ =
      ((1 - l₃) * α + l₃ * a) • u₁ + ((1 - l₃) * β + l₃ * b) • u₃ := by
    have h3 : t₃ • u₃ = (1 - l₃) • u₂ + l₃ • (w - x) := by
      have : ((1 - t₃) • x + t₃ • y₃) - x = ((1 - l₃) • y₂ + l₃ • w) - x :=
        congrArg (fun p : P2 => p - x) heq3
      convert this using 1 <;> simp only [u₃, u₂] <;> module
    rw [zero_smul, zero_add, h3, hu2_eq, hwx_eq]; module
  have ⟨hc1a, hc1b⟩ := basis_unique_2d hdet13 hsub1
  have ⟨hc3a, hc3b⟩ := basis_unique_2d hdet13 hsub3
  have hl₁_pos : 0 < l₁ := by
    rcases eq_or_lt_of_le hl₁0 with h0 | hpos
    · rw [← h0] at hc1b; linarith
    · exact hpos
  have hl₃_pos : 0 < l₃ := by
    rcases eq_or_lt_of_le hl₃0 with h0 | hpos
    · rw [← h0] at hc3a; linarith
    · exact hpos
  have hid1 : l₁ * t₃ = (l₁ - l₃) * β := by
    linear_combination l₁ * hc3b - l₃ * hc1b
  have hid3 : l₃ * t₁ = (l₃ - l₁) * α := by
    linear_combination l₃ * hc1a - l₁ * hc3a
  have hle1 : l₃ ≤ l₁ := by nlinarith only [hid1, hl₁_pos, ht₃0, hβ_pos]
  have hle2 : l₁ ≤ l₃ := by nlinarith only [hid3, hl₃_pos, ht₁0, hα_pos]
  have hl_eq : l₁ = l₃ := le_antisymm hle2 hle1
  have ht₁_zero : t₁ = 0 := by
    rw [hl_eq, sub_self, zero_mul] at hid3
    exact (mul_eq_zero.mp hid3).resolve_left (ne_of_gt hl₃_pos)
  have hzero : (1 - l₁) • (y₂ - x) + l₁ • (w - x) = 0 := by
    have : ((1 - t₁) • x + t₁ • y₁) - x = ((1 - l₁) • y₂ + l₁ • w) - x :=
      congrArg (fun p : P2 => p - x) heq1
    rw [ht₁_zero] at this
    have hL : (1 - (0 : ℝ)) • x + (0 : ℝ) • y₁ - x = 0 := by module
    have hR : (1 - l₁) • y₂ + l₁ • w - x = (1 - l₁) • (y₂ - x) + l₁ • (w - x) := by module
    rw [hL, hR] at this
    exact this.symm
  have hvec : y₂ - x = l₁ • (y₂ - w) := by
    have : (y₂ - x) - l₁ • (y₂ - w) = (1 - l₁) • (y₂ - x) + l₁ • (w - x) := by module
    exact sub_eq_zero.mp (this.trans hzero)
  have hnorm : d = l₁ * d := by
    have := congrArg norm hvec
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl₁_pos, ← dist_eq_norm, ← dist_eq_norm,
      dist_comm, hx2, hw2] at this
    exact this
  have hl₁_one : l₁ = 1 := by nlinarith only [hnorm, hd]
  rw [hl₁_one, one_smul] at hvec
  have : w = x := by
    have h1 : x - w = (y₂ - w) - (y₂ - x) := by abel
    rw [← hvec, sub_self] at h1
    exact (sub_eq_zero.mp h1).symm
  exact hwx_ne this

lemma card_offDiag_filter_eq_sum {d : ℝ} (hd : 0 < d) (A : Finset P2) :
    (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card =
      ∑ x ∈ A, (A.filter (fun y => dist x y = d)).card := by
  set S := A.offDiag.filter (fun p => dist p.1 p.2 = d)
  have hfib : S.card = ∑ x ∈ A, (S.filter (fun p => p.1 = x)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).1)
  rw [hfib]
  refine Finset.sum_congr rfl fun x hx => ?_
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpS, hpx⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpO, hpd⟩ := Finset.mem_filter.mp hpS
    obtain ⟨_, hp2, _⟩ := Finset.mem_offDiag.mp hpO
    exact Finset.mem_filter.mpr ⟨hp2, by rwa [← hpx]⟩
  · intro p₁ hp₁ p₂ hp₂ h2
    have hx1 := (Finset.mem_filter.mp hp₁).2
    have hx2 := (Finset.mem_filter.mp hp₂).2
    exact Prod.ext (hx1.trans hx2.symm) h2
  · intro y hy
    obtain ⟨hyA, hdist⟩ := Finset.mem_filter.mp hy
    have hxy : x ≠ y := fun h => by rw [h, dist_self] at hdist; linarith
    exact ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx, hyA, hxy⟩, hdist⟩, rfl⟩, rfl⟩

lemma exists_deg_le_one_of_three_neighbors {d : ℝ} (hd : 0 < d) {A : Finset P2}
    (hle : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d)
    {x : P2} (hx : x ∈ A) (h3 : 2 < (A.filter (fun y => dist x y = d)).card) :
    ∃ y ∈ A, ∀ w ∈ A, dist y w = d → w = x := by
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp h3
  obtain ⟨ha₁A, hd1⟩ := Finset.mem_filter.mp ha₁
  obtain ⟨ha₂A, hd2⟩ := Finset.mem_filter.mp ha₂
  obtain ⟨ha₃A, hd3⟩ := Finset.mem_filter.mp ha₃
  by_cases h1 : inner ℝ (a₁ - x) (a₃ - x) ≤ inner ℝ (a₁ - x) (a₂ - x) ∧
      inner ℝ (a₁ - x) (a₃ - x) ≤ inner ℝ (a₂ - x) (a₃ - x)
  · refine ⟨a₂, ha₂A, fun w hw hdw => ?_⟩
    exact middle_neighbor_unique hd hd1 hd2 hd3 h12 h13 h23
      (hle a₁ ha₁A a₂ ha₂A) (hle a₁ ha₁A a₃ ha₃A) (hle a₂ ha₂A a₃ ha₃A)
      h1.1 h1.2 hdw (hle x hx w hw) (hle a₁ ha₁A w hw) (hle a₃ ha₃A w hw)
  · by_cases h2 : inner ℝ (a₁ - x) (a₂ - x) ≤ inner ℝ (a₂ - x) (a₃ - x)
    · have h1' : inner ℝ (a₁ - x) (a₂ - x) ≤ inner ℝ (a₁ - x) (a₃ - x) := by
        by_contra hlt; push Not at hlt
        exact h1 ⟨le_of_lt hlt, le_trans (le_of_lt hlt) h2⟩
      refine ⟨a₃, ha₃A, fun w hw hdw => ?_⟩
      exact middle_neighbor_unique hd hd1 hd3 hd2 h13 h12 h23.symm
        (hle a₁ ha₁A a₃ ha₃A) (hle a₁ ha₁A a₂ ha₂A) (hle a₃ ha₃A a₂ ha₂A)
        h1' (by rwa [real_inner_comm (a₂ - x) (a₃ - x)])
        hdw (hle x hx w hw) (hle a₁ ha₁A w hw) (hle a₂ ha₂A w hw)
    · push Not at h2
      have h3' : inner ℝ (a₂ - x) (a₃ - x) ≤ inner ℝ (a₁ - x) (a₃ - x) := by
        by_contra hlt; push Not at hlt
        exact h1 ⟨le_trans (le_of_lt hlt) (le_of_lt h2), le_of_lt hlt⟩
      refine ⟨a₁, ha₁A, fun w hw hdw => ?_⟩
      exact middle_neighbor_unique hd hd2 hd1 hd3 h12.symm h23 h13
        (hle a₂ ha₂A a₁ ha₁A) (hle a₂ ha₂A a₃ ha₃A) (hle a₁ ha₁A a₃ ha₃A)
        (by rw [real_inner_comm (a₁ - x) (a₂ - x)]; exact le_of_lt h2)
        h3' hdw (hle x hx w hw) (hle a₂ ha₂A w hw) (hle a₃ ha₃A w hw)

lemma card_diam_pairs_le (d : ℝ) (hd : 0 < d) :
    ∀ n : ℕ, ∀ A : Finset P2, A.card = n →
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) →
      (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card ≤ 2 * A.card := by
  intro n
  induction n with
  | zero =>
    intro A hA _
    rw [Finset.card_eq_zero.mp hA]
    simp
  | succ n ih =>
    intro A hA hle
    by_cases hdeg : ∀ x ∈ A, (A.filter (fun y => dist x y = d)).card ≤ 2
    · rw [card_offDiag_filter_eq_sum hd A]
      calc ∑ x ∈ A, (A.filter (fun y => dist x y = d)).card
          ≤ ∑ _x ∈ A, 2 := Finset.sum_le_sum hdeg
        _ = 2 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · push Not at hdeg
      obtain ⟨x, hx, h3⟩ := hdeg
      obtain ⟨y, hy, hy_uniq⟩ := exists_deg_le_one_of_three_neighbors hd hle hx h3
      set B := A.erase y
      have hBcard : B.card = n := by
        rw [Finset.card_erase_of_mem hy, hA]; omega
      have hBle : ∀ u ∈ B, ∀ v ∈ B, dist u v ≤ d :=
        fun u hu v hv => hle u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)
      have hIH := ih B hBcard hBle
      set S := A.offDiag.filter (fun p => dist p.1 p.2 = d)
      set S' := B.offDiag.filter (fun p => dist p.1 p.2 = d)
      have hsub : S ⊆ S' ∪ ({(x, y), (y, x)} : Finset (P2 × P2)) := by
        intro p hp
        rcases p with ⟨p1, p2⟩
        obtain ⟨hpO, hdist⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp1, hp2, hne⟩ := Finset.mem_offDiag.mp hpO
        by_cases h1 : p1 = y
        · have h2 : p2 = x := hy_uniq p2 hp2 (by rwa [← h1])
          subst h1; subst h2
          exact Finset.mem_union_right _ (by simp)
        · by_cases h2 : p2 = y
          · have h1' : p1 = x := hy_uniq p1 hp1 (by rw [dist_comm, ← h2]; exact hdist)
            subst h1'; subst h2
            exact Finset.mem_union_right _ (by simp)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨Finset.mem_offDiag.mpr
                ⟨Finset.mem_erase.mpr ⟨h1, hp1⟩, Finset.mem_erase.mpr ⟨h2, hp2⟩, hne⟩, hdist⟩)
      have hpair : ({(x, y), (y, x)} : Finset (P2 × P2)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      calc S.card
          ≤ (S' ∪ {(x, y), (y, x)}).card := Finset.card_le_card hsub
        _ ≤ S'.card + ({(x, y), (y, x)} : Finset (P2 × P2)).card := Finset.card_union_le _ _
        _ ≤ 2 * B.card + 2 := Nat.add_le_add hIH hpair
        _ = 2 * A.card := by rw [hBcard, hA]; omega

end HopfPannwitz

theorem OMA.solution : OMA.R_erdos_132_R1_H1_R1.H2 := by
  intro A d hd hmax
  obtain ⟨⟨a, b⟩, hab, hdist⟩ := Finset.mem_image.mp hd
  obtain ⟨_, _, hne⟩ := Finset.mem_offDiag.mp hab
  have hd_pos : 0 < d := by
    rw [← hdist]
    exact dist_pos.mpr hne
  have hle : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy, dist_self]; exact le_of_lt hd_pos
    · exact hmax (dist x y) (Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩)
  unfold OMA.S_erdos_132.pairMultiplicity
  refine Nat.div_le_of_le_mul ?_
  simpa only [Finset.filter_congr_decidable] using
    HopfPannwitz.card_diam_pairs_le d hd_pos A.card A rfl hle
