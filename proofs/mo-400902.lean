import OMAStatements.S_mo_400902

/-!
Largest circular disks inside an ellipsoid.

Source: Nandakumar R, https://mathoverflow.net/questions/400902 (CC BY-SA 4.0).
Pietro Majer identified the middle semiaxis in the discussion.
Formal statement credit: @connoranderson.
Proof credit: @grp06.
-/

open OMA.S_mo_400902

private theorem frame_coords {u v : Point} (h : Frame u v) :
    u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1 ∧
    v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1 ∧
    u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0 := by
  simpa only [Frame, dotProduct, Fin.sum_univ_three] using h

private theorem frame_norm {u v : Point} (h : Frame u v) (s t : ℝ) :
    (s * u 0 + t * v 0)^2 + (s * u 1 + t * v 1)^2 +
      (s * u 2 + t * v 2)^2 = s^2 + t^2 := by
  obtain ⟨hu, hv, huv⟩ := frame_coords h
  calc
    _ = s^2 * (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) +
        t^2 * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) +
        (2 * s * t) * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) := by ring
    _ = _ := by rw [hu, hv, huv]; ring

private theorem quad_span {a b c : ℝ} {u v : Point} (h : Frame u v) (s t : ℝ) :
    quad a b c (s • u + t • v) =
      (s^2 + t^2) / b^2 +
        (gapZ b c * (s * u 2 + t * v 2)^2 - gapX a b * (s * u 0 + t * v 0)^2) := by
  rw [← frame_norm h s t]
  simp only [quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, gapZ, gapX, div_eq_mul_inv, mul_pow, inv_pow]
  ring

private theorem quad_scale (a b c : ℝ) (u v : Point) (k s t : ℝ) :
    quad a b c ((k * s) • u + (k * t) • v) =
      k^2 * quad a b c (s • u + t • v) := by
  simp only [quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem scale_coeffs (s t R : ℝ) (h : 0 < s^2 + t^2) (hR : 0 < R) :
    ∃ k : ℝ, 0 < k ∧ k^2 * (s^2 + t^2) = R^2 := by
  refine ⟨R / Real.sqrt (s^2 + t^2), div_pos hR (Real.sqrt_pos.2 h), ?_⟩
  rw [div_pow, Real.sq_sqrt h.le]
  exact div_mul_cancel₀ _ h.ne'

private theorem null_direction (u v : Point) :
    ∃ s t : ℝ, s^2 + t^2 = 1 ∧ s * u 0 + t * v 0 = 0 := by
  by_cases hu : u 0 = 0
  · exact ⟨1, 0, by norm_num, by simp [hu]⟩
  · have hpos : 0 < (v 0)^2 + (-u 0)^2 := by
      rw [neg_sq]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hu)
    obtain ⟨k, _, hk⟩ := scale_coeffs (v 0) (-u 0) 1 hpos zero_lt_one
    refine ⟨k * v 0, k * (-u 0), ?_, by ring⟩
    calc
      _ = k^2 * ((v 0)^2 + (-u 0)^2) := by ring
      _ = 1 := by simpa using hk

private theorem quad_average (a b c r s t : ℝ) (o u v : Point) :
    quad a b c (o + (r * s) • u + (r * t) • v) +
      quad a b c (o + (-(r * s)) • u + (-(r * t)) • v) =
    2 * (quad a b c o + r^2 * quad a b c (s • u + t • v)) := by
  simp only [quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem disk_bound {a b c r : ℝ} {o u v : Point}
    (hz : 0 ≤ gapZ b c) (hf : Frame u v) (hfit : Fits a b c r o u v) :
    quad a b c o + r^2 / b^2 ≤ 1 := by
  obtain ⟨s, t, hn, hx⟩ := null_direction u v
  have hp : (r * s)^2 + (r * t)^2 ≤ r^2 := by
    calc
      _ = r^2 * (s^2 + t^2) := by ring
      _ ≤ _ := by rw [hn, mul_one]
  have hm : (-(r * s))^2 + (-(r * t))^2 ≤ r^2 := by simpa only [neg_sq] using hp
  have havg := quad_average a b c r s t o u v
  have hq : quad a b c o + r^2 * quad a b c (s • u + t • v) ≤ 1 := by
    linarith only [hfit _ _ hp, hfit _ _ hm, havg]
  have hw : 1 / b^2 ≤ quad a b c (s • u + t • v) := by
    rw [quad_span hf, hn, hx]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero]
    linarith only [mul_nonneg hz (sq_nonneg (s * u 2 + t * v 2))]
  have hmul := mul_le_mul_of_nonneg_left hw (sq_nonneg r)
  rw [← mul_div_assoc, mul_one] at hmul
  linarith only [hq, hmul]

private theorem quad_nonneg (a b c : ℝ) (o : Point) : 0 ≤ quad a b c o := by
  unfold quad
  positivity

private theorem quad_eq_zero {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {o : Point} (h : quad a b c o = 0) : o = 0 := by
  unfold quad at h
  have h0 : (o 0 / a)^2 = 0 := by
    linarith only [h, sq_nonneg (o 0 / a), sq_nonneg (o 1 / b), sq_nonneg (o 2 / c)]
  have h1 : (o 1 / b)^2 = 0 := by
    linarith only [h, sq_nonneg (o 0 / a), sq_nonneg (o 1 / b), sq_nonneg (o 2 / c)]
  have h2 : (o 2 / c)^2 = 0 := by
    linarith only [h, sq_nonneg (o 0 / a), sq_nonneg (o 1 / b), sq_nonneg (o 2 / c)]
  have z0 := (div_eq_zero_iff.mp (sq_eq_zero_iff.mp h0)).resolve_right ha
  have z1 := (div_eq_zero_iff.mp (sq_eq_zero_iff.mp h1)).resolve_right hb
  have z2 := (div_eq_zero_iff.mp (sq_eq_zero_iff.mp h2)).resolve_right hc
  funext i
  fin_cases i
  · exact z0
  · exact z1
  · exact z2

private theorem fitted_directions {a b c : ℝ} {u v : Point} (hb : 0 < b)
    (hf : Frame u v) (hfit : Fits a b c b 0 u v) (s t : ℝ) :
    gapZ b c * (s * u 2 + t * v 2)^2 ≤ gapX a b * (s * u 0 + t * v 0)^2 := by
  by_cases h : s^2 + t^2 = 0
  · have hs : s^2 = 0 := by linarith only [h, sq_nonneg s, sq_nonneg t]
    have ht : t^2 = 0 := by linarith only [h, sq_nonneg s, sq_nonneg t]
    simp [sq_eq_zero_iff.mp hs, sq_eq_zero_iff.mp ht]
  · have hpos : 0 < s^2 + t^2 :=
      lt_of_le_of_ne (add_nonneg (sq_nonneg s) (sq_nonneg t)) (Ne.symm h)
    obtain ⟨k, hkpos, hk⟩ := scale_coeffs s t b hpos hb
    have hn : (k * s)^2 + (k * t)^2 ≤ b^2 := by
      calc
        _ = k^2 * (s^2 + t^2) := by ring
        _ ≤ _ := hk.le
    have hq := hfit _ _ hn
    rw [zero_add, quad_scale] at hq
    have hunit : k^2 * ((s^2 + t^2) / b^2) = 1 := by
      rw [← mul_div_assoc, hk, div_self (pow_ne_zero _ hb.ne')]
    have hle : quad a b c (s • u + t • v) ≤ (s^2 + t^2) / b^2 := by
      refine le_of_mul_le_mul_left ?_ (sq_pos_of_ne_zero hkpos.ne')
      rw [hunit]
      exact hq
    rw [quad_span hf] at hle
    linarith only [hle]

private theorem gap_plane {a b c : ℝ} {u v : Point} (hz : 0 < gapZ b c)
    (hf : Frame u v)
    (h : ∀ s t : ℝ, gapZ b c * (s * u 2 + t * v 2)^2 ≤
      gapX a b * (s * u 0 + t * v 0)^2) :
    ∃ m : ℝ, gapZ b c * m^2 ≤ gapX a b ∧ u 2 = m * u 0 ∧ v 2 = m * v 0 := by
  have hker (s t : ℝ) (hx : s * u 0 + t * v 0 = 0) : s * u 2 + t * v 2 = 0 := by
    have hh := h s t
    rw [hx, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hh
    by_contra hn
    exact (not_lt_of_ge hh) (mul_pos hz (sq_pos_of_ne_zero hn))
  have hdet := hker (v 0) (-u 0) (by ring)
  have hu := h 1 0
  have hv := h 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add] at hu hv
  have hslope (x z m : ℝ) (hx : x ≠ 0) (hm : z = m * x)
      (hle : gapZ b c * z^2 ≤ gapX a b * x^2) : gapZ b c * m^2 ≤ gapX a b := by
    rw [hm, mul_pow, ← mul_assoc] at hle
    exact le_of_mul_le_mul_right hle (sq_pos_of_ne_zero hx)
  by_cases hx : u 0 = 0
  · have hzU : u 2 = 0 := by simpa using hker 1 0 (by simp [hx])
    have hy : v 0 ≠ 0 := by
      intro hy
      have hzV : v 2 = 0 := by simpa using hker 0 1 (by simp [hy])
      obtain ⟨huu, hvv, huv⟩ := frame_coords hf
      simp only [hx, hy, hzU, hzV, zero_mul, zero_add, add_zero] at huu hvv huv
      rcases mul_eq_zero.mp huv with h1 | h1
      · simp [h1] at huu
      · simp [h1] at hvv
    have hmv : v 2 = (v 2 / v 0) * v 0 := by rw [div_mul_cancel₀ _ hy]
    exact ⟨v 2 / v 0, hslope _ _ _ hy hmv hv, by simp [hx, hzU], hmv⟩
  · have hmu : u 2 = (u 2 / u 0) * u 0 := by rw [div_mul_cancel₀ _ hx]
    have hmv : v 2 = (u 2 / u 0) * v 0 := by
      field_simp [hx]
      <;> nlinarith only [hdet]
    exact ⟨u 2 / u 0, hslope _ _ _ hx hmu hu, hmu, hmv⟩

private theorem section_of_coords {a b c x z : ℝ} (hn : x^2 + z^2 = 1)
    (he : gapZ b c * z^2 = gapX a b * x^2) :
    ∃ u v : Point, Frame u v ∧ ∀ s t : ℝ,
      quad a b c (s • u + t • v) = (s^2 + t^2) / b^2 := by
  let u : Point := ![0, 1, 0]
  let v : Point := ![x, 0, z]
  have hf : Frame u v := by
    unfold Frame
    simp only [dotProduct, Fin.sum_univ_three]
    change (0 : ℝ) * 0 + 1 * 1 + 0 * 0 = 1 ∧
      x * x + 0 * 0 + z * z = 1 ∧ 0 * x + 1 * 0 + 0 * z = 0
    exact ⟨by norm_num, by nlinarith only [hn], by ring⟩
  refine ⟨u, v, hf, fun s t => ?_⟩
  rw [quad_span hf]
  change (s^2 + t^2) / b^2 +
    (gapZ b c * (s * 0 + t * z)^2 - gapX a b * (s * 0 + t * x)^2) =
      (s^2 + t^2) / b^2
  simp only [mul_zero, zero_add, mul_pow]
  calc
    _ = (s^2 + t^2) / b^2 + t^2 * (gapZ b c * z^2 - gapX a b * x^2) := by ring
    _ = _ := by rw [he, sub_self, mul_zero, add_zero]

theorem OMA.solution : type_of% @OMA.S_mo_400902.main := by
  intro a b c hc hcb hba
  have hb : 0 < b := hc.trans_le hcb
  have ha : 0 < a := hb.trans_le hba
  have hx : 0 ≤ gapX a b := by
    have hh := (inv_le_inv₀ ha hb).2 hba
    have hp := mul_nonneg (sub_nonneg.mpr hh)
      (add_nonneg (inv_nonneg.mpr hb.le) (inv_nonneg.mpr ha.le))
    unfold gapX
    nlinarith only [hp]
  have hz : 0 ≤ gapZ b c := by
    have hh := (inv_le_inv₀ hb hc).2 hcb
    have hp := mul_nonneg (sub_nonneg.mpr hh)
      (add_nonneg (inv_nonneg.mpr hc.le) (inv_nonneg.mpr hb.le))
    unfold gapZ
    nlinarith only [hp]
  have hstrict (hne : b ≠ c) : 0 < gapZ b c := by
    have hh := (inv_lt_inv₀ hb hc).2 (lt_of_le_of_ne hcb (Ne.symm hne))
    have hp := mul_pos (sub_pos.mpr hh) (add_pos (inv_pos.mpr hc) (inv_pos.mpr hb))
    unfold gapZ
    nlinarith only [hp]
  have hdiag (he : b = c) : gapZ b c = 0 := by simp [gapZ, he]
  refine ⟨?_, ?_, ?_⟩
  · intro r o u v hr hf hfit
    have hbound := disk_bound hz hf hfit
    have hdiv : r^2 / b^2 ≤ 1 := by linarith only [hbound, quad_nonneg a b c o]
    have hrs : r^2 ≤ b^2 := by
      simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_ne_zero hb.ne')).mp hdiv
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (add_pos_of_nonneg_of_pos hr hb)
    nlinarith only [hp, hrs]
  · intro o u v hf
    constructor
    · intro hfit
      have hbound := disk_bound hz hf hfit
      rw [div_self (pow_ne_zero _ hb.ne')] at hbound
      have ho : quad a b c o = 0 := by linarith only [hbound, quad_nonneg a b c o]
      have hcenter := quad_eq_zero ha.ne' hb.ne' hc.ne' ho
      subst o
      refine ⟨rfl, ?_⟩
      by_cases he : b = c
      · exact Or.inl he
      · exact Or.inr (gap_plane (hstrict he) hf (fitted_directions hb hf hfit))
    · rintro ⟨rfl, hor⟩ s t hst
      rw [zero_add, quad_span hf]
      have hle : (s^2 + t^2) / b^2 ≤ 1 := by
        apply (div_le_iff₀ (sq_pos_of_ne_zero hb.ne')).2
        simpa only [one_mul] using hst
      have hgap : gapZ b c * (s * u 2 + t * v 2)^2 ≤
          gapX a b * (s * u 0 + t * v 0)^2 := by
        rcases hor with he | ⟨m, hm, hu, hv⟩
        · rw [hdiag he, zero_mul]
          exact mul_nonneg hx (sq_nonneg _)
        · rw [hu, hv]
          have hfactor : s * (m * u 0) + t * (m * v 0) =
              m * (s * u 0 + t * v 0) := by ring
          rw [hfactor, mul_pow, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)
      linarith only [hle, hgap]
  · by_cases he : b = c
    · exact section_of_coords (x := 0) (z := 1) (by norm_num) (by simp [hdiag he])
    · have hzpos := hstrict he
      let m := Real.sqrt (gapX a b / gapZ b c)
      have hm : m^2 = gapX a b / gapZ b c := Real.sq_sqrt (div_nonneg hx hz)
      have hcomm : gapZ b c * m^2 = gapX a b := by
        rw [hm]
        rw [mul_comm, div_mul_cancel₀ _ hzpos.ne']
      have hnormpos : 0 < 1 + m^2 := add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg m)
      let d := Real.sqrt (1 + m^2)
      have hd : d^2 = 1 + m^2 := Real.sq_sqrt hnormpos.le
      have hdne : d ≠ 0 := (Real.sqrt_pos.2 hnormpos).ne'
      apply section_of_coords (x := 1 / d) (z := m / d)
      · rw [div_pow, div_pow, one_pow, ← add_div, ← hd, div_self (pow_ne_zero _ hdne)]
      · calc
          _ = (gapZ b c * m^2) / d^2 := by simp only [div_eq_mul_inv]; ring
          _ = _ := by rw [hcomm, div_pow, one_pow]; ring
