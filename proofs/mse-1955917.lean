import OMAStatements.S_mse_1955917

-- The normalization and cyclic reduction follow the Math Stack Exchange answer
-- at https://math.stackexchange.com/a/5141397. The scalar estimate below
-- supplies the required inequality when the normalized pair mean is below one.

namespace OMA.Mse1955917

private lemma scalarShape (L : ℝ) (hL : 0 < L) :
    (L - (1 - Real.exp (-L))) / ((1 - Real.exp (-L)) * L) ≤
      1 / (1 + Real.exp (-L) * L) := by
  let x := Real.exp (-L)
  change (L - (1 - x)) / ((1 - x) * L) ≤ 1 / (1 + x * L)
  have hx : 0 < x := Real.exp_pos _
  have hxlt : x < 1 := by
    simpa only [x, Real.exp_zero] using
      Real.exp_lt_exp.mpr (show -L < 0 by linarith)
  have hxexp : x * Real.exp L = 1 := by
    simp [x, ← Real.exp_add]
  have hlinear : 1 + L ≤ Real.exp L := by
    have h := Real.add_one_le_exp L
    linarith
  have hreciprocal : x * (1 + L) ≤ 1 := by
    calc
      x * (1 + L) ≤ x * Real.exp L := mul_le_mul_of_nonneg_left hlinear hx.le
      _ = 1 := hxexp
  have hquadratic : 1 ≤ (1 + L) * (1 - L / 2 + L ^ 2 / 6) := by
    have ht : 0 ≤ (L - 1) ^ 2 + 2 := by
      linarith [sq_nonneg (L - 1)]
    nlinarith only [mul_nonneg hL.le ht]
  have hshape : x ≤ 1 - L / 2 + L ^ 2 / 6 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1 + L by linarith)).mp
    simpa only [mul_comm] using hreciprocal.trans hquadratic
  have hTaylor : 1 + L + L ^ 2 / 2 + L ^ 3 / 6 ≤ Real.exp L := by
    simpa [Finset.sum_range_succ, Nat.factorial] using Real.sum_le_exp_of_nonneg hL.le 4
  have hexp : 1 + L ^ 2 + L * x ≤ Real.exp L := by
    have hmul := mul_le_mul_of_nonneg_left hshape hL.le
    nlinarith only [hTaylor, hmul]
  have hproduct : x * (1 + L ^ 2 + L * x) ≤ 1 := by
    calc
      x * (1 + L ^ 2 + L * x) ≤ x * Real.exp L :=
        mul_le_mul_of_nonneg_left hexp hx.le
      _ = 1 := hxexp
  have hden : 0 < 1 + x * L := by
    linarith [mul_nonneg hx.le hL.le]
  refine (div_le_div_iff₀ (mul_pos (sub_pos.mpr hxlt) hL) hden).mpr ?_
  nlinarith only [hproduct]

private lemma twiceMulLogLeSqSubOne (c : ℝ) (hc : 1 ≤ c) :
    2 * (c * Real.log c) ≤ c ^ 2 - 1 := by
  let f : ℝ → ℝ := fun y => y ^ 2 - 1 - 2 * (y * Real.log y)
  have hderiv (y : ℝ) (hy : 0 < y) :
      HasDerivAt f (2 * y - 2 * (Real.log y + 1)) y := by
    simpa [f, Pi.sub_def] using
      (((hasDerivAt_id y).pow 2).sub_const 1).sub
        ((Real.hasDerivAt_mul_log hy.ne').const_mul 2)
  have hcont : Continuous f :=
    ((continuous_id.pow 2).sub continuous_const).sub
      (continuous_const.mul Real.continuous_mul_log)
  have hmon : MonotoneOn f (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn ?_ ?_
    · intro y hy
      have hy' : 1 ≤ y := interior_subset hy
      exact (hderiv y (zero_lt_one.trans_le hy')).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' : 1 ≤ y := interior_subset hy
      have hy0 : 0 < y := zero_lt_one.trans_le hy'
      rw [(hderiv y hy0).deriv]
      linarith [Real.log_le_sub_one_of_pos hy0]
  have h := hmon (Set.mem_Ici.mpr (le_refl (1 : ℝ))) (Set.mem_Ici.mpr hc) hc
  simp [f] at h
  linarith

private lemma pairBound
    (x c t : ℝ) (hx : 0 < x) (hc : 0 < c) (ht : 0 < t) (htx : t ≤ 2 * x)
    (h : c * Real.log c + t * Real.log x = 0) :
    (x - 1) * (c + t - 1) ≤ t * Real.log x := by
  by_cases hbig : 1 ≤ x
  · have hlog : x - 1 - Real.log x ≤ (x - 1) * Real.log x := by
      nlinarith only [Real.self_sub_one_le_mul_log hx.le]
    have htlog := mul_le_mul_of_nonneg_left hlog ht.le
    have hclog := mul_le_mul_of_nonneg_left (Real.self_sub_one_le_mul_log hc.le)
      (sub_nonneg.mpr hbig)
    have hmul := congrArg (fun v : ℝ => (x - 1) * v) h
    nlinarith only [htlog, hclog, hmul]
  · have hsmall : x < 1 := lt_of_not_ge hbig
    let L := -Real.log x
    have hL : 0 < L := neg_pos.mpr (Real.log_neg hx hsmall)
    have hxL : Real.exp (-L) = x := by
      simpa only [L, neg_neg] using Real.exp_log hx
    have htLc : t * L = c * Real.log c := by
      dsimp [L]
      linarith [h]
    have hclog : 0 < Real.log c := by
      by_contra! hnot
      have hnon := mul_nonpos_of_nonneg_of_nonpos hc.le hnot
      linarith [mul_pos ht hL]
    have hc1 : 1 < c := (Real.log_pos_iff hc.le).mp hclog
    have hclimit : c - 1 ≤ 2 * x * L := calc
      c - 1 ≤ c * Real.log c := Real.self_sub_one_le_mul_log hc.le
      _ = t * L := htLc.symm
      _ ≤ 2 * x * L := mul_le_mul_of_nonneg_right htx hL.le
    have htbound : t * L ≤ (c - 1) * (1 + x * L) := calc
      t * L = c * Real.log c := htLc
      _ ≤ (c ^ 2 - 1) / 2 := by linarith only [twiceMulLogLeSqSubOne c hc1.le]
      _ = (c - 1) * (1 + (c - 1) / 2) := by ring
      _ ≤ (c - 1) * (1 + x * L) :=
        mul_le_mul_of_nonneg_left (by linarith only [hclimit]) (sub_nonneg.mpr hc1.le)
    have hden : 0 < 1 + x * L := by linarith [mul_nonneg hx.le hL.le]
    have hm : (L - (1 - x)) * (1 + x * L) ≤ (1 - x) * L := by
      have hshape := scalarShape L hL
      rw [hxL] at hshape
      simpa only [one_mul] using
        (div_le_div_iff₀ (mul_pos (sub_pos.mpr hsmall) hL) hden).mp hshape
    have hgap : t * (L - (1 - x)) ≤ (1 - x) * (c - 1) := by
      apply (mul_le_mul_iff_of_pos_right hden).mp
      calc
        (t * (L - (1 - x))) * (1 + x * L) =
            t * ((L - (1 - x)) * (1 + x * L)) := by ring
        _ ≤ t * ((1 - x) * L) := mul_le_mul_of_nonneg_left hm ht.le
        _ = (1 - x) * (t * L) := by ring
        _ ≤ (1 - x) * ((c - 1) * (1 + x * L)) :=
          mul_le_mul_of_nonneg_left htbound (sub_nonneg.mpr hsmall.le)
        _ = ((1 - x) * (c - 1)) * (1 + x * L) := by ring
    dsimp [L] at hgap
    nlinarith only [hgap]

private theorem pairMean_lower (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a + b ≤ 2 * Real.exp ((a * Real.log a + b * Real.log b) / (a + b)) := by
  have hsum : 0 < a + b := add_pos ha hb
  have hmid : 0 < (a + b) / 2 := by positivity
  have hj := Real.convexOn_mul_log.2 (show a ∈ Set.Ici (0 : ℝ) from ha.le)
    (show b ∈ Set.Ici (0 : ℝ) from hb.le)
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hm : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (a + b) / 2 := by
    simp only [smul_eq_mul]
    ring
  rw [hm] at hj
  change (a + b) / 2 * Real.log ((a + b) / 2) ≤
    (1 / 2) * (a * Real.log a) + (1 / 2) * (b * Real.log b) at hj
  have hlog : Real.log ((a + b) / 2) ≤ (a * Real.log a + b * Real.log b) / (a + b) := by
    apply (le_div_iff₀ hsum).2
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hmid] at hexp
  linarith

private noncomputable def logMean2 (a b : ℝ) : ℝ :=
  (a * Real.log a + b * Real.log b) / (a + b)

private noncomputable def logMean3 (a b c : ℝ) : ℝ :=
  (a * Real.log a + b * Real.log b + c * Real.log c) / (a + b + c)

private theorem mean2_rpow (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ a * b ^ b) ^ (1 / (a + b)) = Real.exp (logMean2 a b) := by
  have ha' := Real.rpow_pos_of_pos ha a
  have hb' := Real.rpow_pos_of_pos hb b
  rw [← Real.exp_log (Real.rpow_pos_of_pos (mul_pos ha' hb') _),
    Real.log_rpow (mul_pos ha' hb'), Real.log_mul ha'.ne' hb'.ne',
    Real.log_rpow ha, Real.log_rpow hb]
  simp [logMean2, div_eq_mul_inv, mul_comm]

private theorem mean3_rpow (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ a * b ^ b * c ^ c) ^ (1 / (a + b + c)) = Real.exp (logMean3 a b c) := by
  have ha' := Real.rpow_pos_of_pos ha a
  have hb' := Real.rpow_pos_of_pos hb b
  have hc' := Real.rpow_pos_of_pos hc c
  have hab' := mul_pos ha' hb'
  rw [← Real.exp_log (Real.rpow_pos_of_pos (mul_pos hab' hc') _),
    Real.log_rpow (mul_pos hab' hc'), Real.log_mul hab'.ne' hc'.ne',
    Real.log_mul ha'.ne' hb'.ne', Real.log_rpow ha, Real.log_rpow hb, Real.log_rpow hc]
  simp [logMean3, div_eq_mul_inv, mul_comm]

private theorem logMean2_scale (a b g : ℝ) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    logMean2 (a / g) (b / g) = logMean2 a b - Real.log g := by
  unfold logMean2
  rw [Real.log_div ha.ne' hg.ne', Real.log_div hb.ne' hg.ne']
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have hdiv : a / g + b / g ≠ 0 := (add_pos (div_pos ha hg) (div_pos hb hg)).ne'
  field_simp [hg.ne', hab, hdiv]
  ring

private theorem normalized_log_sum (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    let g := Real.exp (logMean3 a b c)
    (a / g) * Real.log (a / g) + (b / g) * Real.log (b / g) +
      (c / g) * Real.log (c / g) = 0 := by
  dsimp only
  have hg := Real.exp_pos (logMean3 a b c)
  rw [Real.log_div ha.ne' hg.ne', Real.log_div hb.ne' hg.ne', Real.log_div hc.ne' hg.ne',
    Real.log_exp]
  unfold logMean3
  have hs : a + b + c ≠ 0 := (add_pos (add_pos ha hb) hc).ne'
  field_simp [hg.ne', hs]
  ring


private theorem pair_step (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * Real.log a + b * Real.log b + c * Real.log c = 0) :
    (Real.exp (logMean2 a b) - 1) * (a + b + c - 1) ≤ a * Real.log a + b * Real.log b := by
  let x := Real.exp (logMean2 a b)
  let t := a + b
  have hx : 0 < x := Real.exp_pos _
  have ht : 0 < t := add_pos ha hb
  have htx : t ≤ 2 * x := pairMean_lower a b ha hb
  have hlog : t * Real.log x = a * Real.log a + b * Real.log b := by
    dsimp [t, x, logMean2]
    rw [Real.log_exp]
    field_simp [(add_pos ha hb).ne']
  have hnormal : c * Real.log c + t * Real.log x = 0 := by rw [hlog]; linarith
  calc
    (x - 1) * (a + b + c - 1) = (x - 1) * (c + t - 1) := by dsimp [t]; ring
    _ ≤ t * Real.log x := pairBound x c t hx hc ht htx hnormal
    _ = a * Real.log a + b * Real.log b := hlog

private theorem normalized_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * Real.log a + b * Real.log b + c * Real.log c = 0) :
    Real.exp (logMean2 a b) + Real.exp (logMean2 b c) + Real.exp (logMean2 c a) ≤ 3 := by
  have hs : 0 < a + b + c - 1 := by
    by_contra! hle
    have ha' := mul_neg_of_pos_of_neg ha (Real.log_neg ha (by linarith))
    have hb' := mul_neg_of_pos_of_neg hb (Real.log_neg hb (by linarith))
    have hc' := mul_neg_of_pos_of_neg hc (Real.log_neg hc (by linarith))
    linarith
  have hab := pair_step a b c ha hb hc h
  have hbc := pair_step b c a hb hc ha (by linarith)
  have hca := pair_step c a b hc ha hb (by linarith)
  have hsum :
      (Real.exp (logMean2 a b) + Real.exp (logMean2 b c) + Real.exp (logMean2 c a) - 3) *
        (a + b + c - 1) ≤ 0 := by
    calc
      _ = (Real.exp (logMean2 a b) - 1) * (a + b + c - 1) +
          (Real.exp (logMean2 b c) - 1) * (b + c + a - 1) +
          (Real.exp (logMean2 c a) - 1) * (c + a + b - 1) := by ring
      _ ≤ 0 := by linarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_left hsum hs)

theorem weighted_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 * (a ^ a * b ^ b * c ^ c) ^ (1 / (a + b + c)) ≥
      (a ^ a * b ^ b) ^ (1 / (a + b)) + (b ^ b * c ^ c) ^ (1 / (b + c)) +
      (c ^ c * a ^ a) ^ (1 / (c + a)) := by
  rw [mean3_rpow a b c ha hb hc, mean2_rpow a b ha hb, mean2_rpow b c hb hc,
    mean2_rpow c a hc ha]
  let g := Real.exp (logMean3 a b c)
  have hg : 0 < g := Real.exp_pos _
  have hn := normalized_bound (a / g) (b / g) (c / g)
    (div_pos ha hg) (div_pos hb hg) (div_pos hc hg) (normalized_log_sum a b c ha hb hc)
  rw [logMean2_scale a b g ha hb hg, logMean2_scale b c g hb hc hg,
    logMean2_scale c a g hc ha hg] at hn
  simp only [Real.exp_sub, Real.exp_log hg] at hn
  rw [← add_div, ← add_div, div_le_iff₀ hg] at hn
  exact hn

end OMA.Mse1955917

theorem OMA.solution : type_of% @OMA.S_mse_1955917.main := by
  exact OMA.Mse1955917.weighted_bound
