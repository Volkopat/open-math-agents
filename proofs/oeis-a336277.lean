import OMAStatements.S_oeis_a336277

namespace OMA.S_oeis_a336277_Proof

open Complex MeasureTheory Filter Topology Finset

/-! Part 1: Non-vanishing of `riemannZeta` on `[0, 2] \ {1}` and holomorphy of `invZeta` -/

private noncomputable def etaTerm (n : ℕ) (s : ℂ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

private noncomputable def etaFun (s : ℂ) : ℂ :=
  ∑' n : ℕ, etaTerm n s

private lemma hasDerivAt_ofReal_cpow_neg {s : ℂ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s) * (t⁻¹ : ℂ)) t := by
  have heq : (fun x : ℝ => (x : ℂ) ^ (-s)) =ᶠ[𝓝 t]
      fun x : ℝ => Complex.exp ((-s) * (Real.log x : ℂ)) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.ofReal_log hx.le, mul_comm]
  have hlog : HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) (t⁻¹ : ℂ) t := by
    have h1 := (Real.hasDerivAt_log ht.ne').ofReal_comp
    exact h1.congr_deriv (by simp)
  have hmul : HasDerivAt (fun x : ℝ => (-s) * (Real.log x : ℂ)) ((-s) * (t⁻¹ : ℂ)) t :=
    hlog.const_mul (-s)
  have hexp := hmul.cexp
  have hval : Complex.exp ((-s) * (Real.log t : ℂ)) = (t : ℂ) ^ (-s) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      Complex.ofReal_log ht.le, mul_comm]
  rw [hval] at hexp
  exact (hexp.congr_of_eventuallyEq heq).congr_deriv (by ring)

private lemma norm_etaTerm_le {δ R : ℝ} (hδ : 0 < δ) {s : ℂ} (hs_re : δ < s.re)
    (hs_norm : ‖s‖ < R) (n : ℕ) :
    ‖etaTerm n s‖ ≤ R * ((n + 1 : ℝ) ^ (δ + 1))⁻¹ := by
  have hR : 0 ≤ R := (norm_nonneg s).trans hs_norm.le
  set a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  set b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha_pos : (0 : ℝ) < a := by positivity
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega)
  have hba : b - a = 1 := by
    dsimp only [a, b]
    push_cast
    ring
  have hbound : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s) * (t⁻¹ : ℂ)) (Set.Icc a b) t ∧
      ‖(-s) * (t : ℂ) ^ (-s) * (t⁻¹ : ℂ)‖ ≤ R * ((n + 1 : ℝ) ^ (δ + 1))⁻¹ := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1
    refine ⟨(hasDerivAt_ofReal_cpow_neg ht_pos).hasDerivWithinAt, ?_⟩
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos,
      Complex.neg_re, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
    have hpow : t ^ (-s.re) * t⁻¹ = (t ^ (s.re + 1))⁻¹ := by
      rw [← Real.rpow_neg ht_pos.le, show -(s.re + 1) = -s.re + -1 by ring,
        Real.rpow_add ht_pos, Real.rpow_neg_one]
    rw [mul_assoc, hpow]
    have ht1 : (n + 1 : ℝ) ≤ t := by
      have h1 : (n + 1 : ℝ) ≤ a := by
        dsimp only [a]
        push_cast
        linarith
      exact h1.trans ht.1
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hle1 : (n + 1 : ℝ) ^ (δ + 1) ≤ (n + 1 : ℝ) ^ (s.re + 1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hle2 : (n + 1 : ℝ) ^ (s.re + 1) ≤ t ^ (s.re + 1) :=
      Real.rpow_le_rpow (by positivity) ht1 (by linarith)
    have hinv : (t ^ (s.re + 1))⁻¹ ≤ ((n + 1 : ℝ) ^ (δ + 1))⁻¹ :=
      inv_anti₀ (by positivity) (hle1.trans hle2)
    exact mul_le_mul hs_norm.le hinv (by positivity) hR
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℝ => (x : ℂ) ^ (-s)) (s := Set.Icc a b)
    (fun t ht => (hbound t ht).1) (fun t ht => (hbound t ht).2) (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_of_nonneg (by linarith), hba, mul_one, norm_sub_rev] at hmvt
  simpa only [etaTerm, a, b, Complex.ofReal_natCast] using hmvt

private lemma differentiableOn_etaTerm (n : ℕ) (U : Set ℂ) :
    DifferentiableOn ℂ (etaTerm n) U := by
  have h1 : Differentiable ℂ (fun s : ℂ => ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) := by
    have heq : (fun s : ℂ => ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) =
        fun s : ℂ => Complex.exp (Complex.log ((2 * n + 1 : ℕ) : ℂ) * (-s)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))]
    rw [heq]
    exact (differentiable_id.neg.const_mul _).cexp
  have h2 : Differentiable ℂ (fun s : ℂ => ((2 * n + 2 : ℕ) : ℂ) ^ (-s)) := by
    have heq : (fun s : ℂ => ((2 * n + 2 : ℕ) : ℂ) ^ (-s)) =
        fun s : ℂ => Complex.exp (Complex.log ((2 * n + 2 : ℕ) : ℂ) * (-s)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))]
    rw [heq]
    exact (differentiable_id.neg.const_mul _).cexp
  exact (h1.sub h2).differentiableOn

private lemma differentiableOn_etaFun : DifferentiableOn ℂ etaFun {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  have hδ : 0 < s₀.re / 2 := by linarith
  set δ : ℝ := s₀.re / 2
  set R : ℝ := ‖s₀‖ + 1
  let V : Set ℂ := {s : ℂ | δ < s.re} ∩ Metric.ball 0 R
  have hV_open : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ V := by
    refine ⟨by change δ < s₀.re; dsimp only [δ]; linarith, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [R]
    linarith
  have hu : Summable (fun n : ℕ => R * ((n + 1 : ℝ) ^ (δ + 1))⁻¹) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (δ + 1))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (δ + 1))⁻¹) :=
      (hbase.comp_injective Nat.succ_injective).congr fun n => by
        simp [Nat.succ_eq_add_one]
    exact hshift.mul_left R
  have hdiffV : DifferentiableOn ℂ etaFun V :=
    Complex.differentiableOn_tsum_of_summable_norm hu (fun n => differentiableOn_etaTerm n V) hV_open
      fun n w hw => norm_etaTerm_le hδ hw.1 (by simpa [Metric.mem_ball, dist_zero_right] using hw.2) n
  exact (hdiffV.differentiableAt (hV_open.mem_nhds hs₀V)).differentiableWithinAt

private lemma etaFun_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    etaFun s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hsum_all : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℂ) ^ (-s)) := by
    have h1 : Summable (fun k : ℕ => 1 / ((k : ℂ) ^ s)) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have h2 : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℂ) ^ s)) :=
      h1.comp_injective Nat.succ_injective
    refine h2.congr fun k => ?_
    rw [one_div, Complex.cpow_neg]
  have hsum_odd : Summable (fun n : ℕ => ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by dsimp only at h; omega
    simpa only [Function.comp_def] using hsum_all.comp_injective hinj
  have hsum_even : Summable (fun n : ℕ => ((2 * n + 2 : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := fun a b h => by dsimp only at h; omega
    simpa only [Function.comp_def] using hsum_all.comp_injective hinj
  have hzeta : riemannZeta s = ∑' k : ℕ, ((k + 1 : ℕ) : ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun k => ?_
    rw [one_div, Complex.cpow_neg, Nat.cast_add, Nat.cast_one]
  have hsum_even' : Summable (fun n : ℕ => (((2 * n + 1) + 1 : ℕ) : ℂ) ^ (-s)) :=
    hsum_even.congr fun n => by
      have : 2 * n + 2 = 2 * n + 1 + 1 := by omega
      rw [this]
  have hsplit : ∑' k : ℕ, ((k + 1 : ℕ) : ℂ) ^ (-s) =
      (∑' n : ℕ, ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) + (∑' n : ℕ, ((2 * n + 2 : ℕ) : ℂ) ^ (-s)) := by
    exact (tsum_even_add_odd (f := fun k : ℕ => ((k + 1 : ℕ) : ℂ) ^ (-s)) hsum_odd hsum_even').symm
  have heven : ∑' n : ℕ, ((2 * n + 2 : ℕ) : ℂ) ^ (-s) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [hzeta, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hmul : (2 * n + 2 : ℕ) = 2 * (n + 1) := by omega
    rw [hmul, Nat.cast_mul, ← Complex.ofReal_natCast 2, ← Complex.ofReal_natCast (n + 1),
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg (n + 1)),
      Complex.ofReal_natCast, Complex.ofReal_natCast, Nat.cast_ofNat]
  have heta : etaFun s =
      (∑' n : ℕ, ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) - (∑' n : ℕ, ((2 * n + 2 : ℕ) : ℂ) ^ (-s)) :=
    hsum_odd.tsum_sub hsum_even
  have h2pow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add 1 (-s) (by norm_num), Complex.cpow_one]
  rw [heta, h2pow]
  have hsub : (∑' n : ℕ, ((2 * n + 1 : ℕ) : ℂ) ^ (-s)) =
      riemannZeta s - (∑' n : ℕ, ((2 * n + 2 : ℕ) : ℂ) ^ (-s)) := by
    rw [hzeta, hsplit]
    ring
  rw [hsub, heven]
  ring

private noncomputable def etaCont : ℂ → ℂ :=
  Function.update (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) 1 (Real.log 2 : ℂ)

private lemma differentiableOn_etaCont : DifferentiableOn ℂ etaCont {s : ℂ | 0 < s.re} := by
  intro s hs
  rcases ne_or_eq s 1 with hs1 | rfl
  · have hdiff1 : DifferentiableAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s := by
      have heq : (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) =
          fun z : ℂ => 1 - Complex.exp (Complex.log (2 : ℂ) * (1 - z)) := by
        funext z
        rw [Complex.cpow_def_of_ne_zero (by norm_num)]
      rw [heq]
      exact (differentiableAt_const 1).sub
        (((differentiableAt_const 1).sub differentiableAt_id).const_mul _).cexp
    have hdiff : DifferentiableAt ℂ etaCont s :=
      (hdiff1.mul (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq
        (by filter_upwards [eventually_ne_nhds hs1] with z hz using Function.update_of_ne hz ..)
    exact hdiff.differentiableWithinAt
  · have hdiff_punct : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ etaCont z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hdiff1 : DifferentiableAt ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) z := by
        have heq : (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) =
            fun w : ℂ => 1 - Complex.exp (Complex.log (2 : ℂ) * (1 - w)) := by
          funext w
          rw [Complex.cpow_def_of_ne_zero (by norm_num)]
        rw [heq]
        exact (differentiableAt_const 1).sub
          (((differentiableAt_const 1).sub differentiableAt_id).const_mul _).cexp
      exact (hdiff1.mul (differentiableAt_riemannZeta hz)).congr_of_eventuallyEq
        (by filter_upwards [eventually_ne_nhds hz] with w hw using Function.update_of_ne hw ..)
    have hcont : ContinuousAt etaCont 1 := by
      rw [etaCont, continuousAt_update_same]
      have hg_deriv : HasDerivAt (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) (Real.log 2 : ℂ) 1 := by
        have heq : (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) =
            fun z : ℂ => 1 - Complex.exp ((Real.log 2 : ℂ) * (1 - z)) := by
          funext z
          rw [Complex.cpow_def_of_ne_zero (by norm_num),
            show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
        rw [heq]
        have h1 : HasDerivAt (fun z : ℂ => (Real.log 2 : ℂ) * (1 - z)) (-(Real.log 2 : ℂ)) 1 := by
          have hd := ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 1)).const_mul
            (Real.log 2 : ℂ)
          exact hd.congr_deriv (by ring)
        have h2 : HasDerivAt (fun z : ℂ => Complex.exp ((Real.log 2 : ℂ) * (1 - z)))
            (-(Real.log 2 : ℂ)) 1 := by
          have hd := h1.cexp
          exact hd.congr_deriv (by simp)
        exact ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub h2).congr_deriv (by ring)
      have hslope : Tendsto (fun z : ℂ => (z - 1)⁻¹ * (1 - (2 : ℂ) ^ (1 - z)))
          (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
        have hs' := hasDerivAt_iff_tendsto_slope.mp hg_deriv
        refine hs'.congr fun z => ?_
        simp [slope, vsub_eq_sub, smul_eq_mul]
      have hprod := hslope.mul riemannZeta_residue_one
      rw [mul_one] at hprod
      refine hprod.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      calc
        (z - 1)⁻¹ * (1 - (2 : ℂ) ^ (1 - z)) * ((z - 1) * riemannZeta z)
            = ((z - 1)⁻¹ * (z - 1)) * ((1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) := by ring
        _ = (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z := by rw [inv_mul_cancel₀ hsub, one_mul]
    exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff_punct hcont
      |>.differentiableAt).differentiableWithinAt

private lemma etaFun_eq_etaCont {s : ℂ} (hs : 0 < s.re) : etaFun s = etaCont s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    have hx' : 0 < x.re := hx
    have hy' : 0 < y.re := hy
    change 0 < (a • x + b • y).re
    simp only [add_re, Complex.real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      rw [hb']
      nlinarith
    · nlinarith [mul_lt_mul_of_pos_left hx' ha', mul_le_mul_of_nonneg_left hy'.le hb]
  have hEq := (differentiableOn_etaFun.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (differentiableOn_etaCont.analyticOnNhd hopen) hconv.isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by simp)
    (by
      refine eventuallyEq_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp : 1 < (2 : ℂ).re))
        fun z hz => ?_
      have hz' : 1 < z.re := hz
      have hz1 : z ≠ 1 := fun h => by
        rw [h, Complex.one_re] at hz'
        linarith
      rw [etaFun_eq_of_one_lt_re hz', etaCont, Function.update_of_ne hz1])
  exact hEq hs

private lemma riemannZeta_ne_zero_of_real_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  have hx_ne : (x : ℂ) ≠ 1 := by
    intro h
    have : x = 1 := Complex.ofReal_injective h
    linarith
  have heq : etaFun (x : ℂ) = (1 - (2 : ℂ) ^ (1 - (x : ℂ))) * riemannZeta (x : ℂ) := by
    rw [etaFun_eq_etaCont (by simpa using hx0), etaCont, Function.update_of_ne hx_ne]
  have hcast_term : ∀ n : ℕ, etaTerm n (x : ℂ) =
      (((2 * n + 1 : ℝ) ^ (-x) - (2 * n + 2 : ℝ) ^ (-x) : ℝ) : ℂ) := by
    intro n
    rw [etaTerm, Complex.ofReal_sub,
      show ((2 * n + 1 : ℕ) : ℂ) = (((2 * n + 1 : ℝ) : ℂ)) by push_cast; rfl,
      show ((2 * n + 2 : ℕ) : ℂ) = (((2 * n + 2 : ℝ) : ℂ)) by push_cast; rfl,
      ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 1),
      ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 2)]
  have hsum_real : Summable (fun n : ℕ => ((2 * n + 1 : ℝ) ^ (-x) - (2 * n + 2 : ℝ) ^ (-x))) := by
    have hnorm : Summable (fun n : ℕ => (‖(x : ℂ)‖ + 1) * ((n + 1 : ℝ) ^ (x / 2 + 1))⁻¹) := by
      have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (x / 2 + 1))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by linarith)
      have hshift : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (x / 2 + 1))⁻¹) :=
        (hbase.comp_injective Nat.succ_injective).congr fun n => by
          simp [Nat.succ_eq_add_one]
      exact hshift.mul_left (‖(x : ℂ)‖ + 1)
    refine hnorm.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · have hlt : (2 * n + 1 : ℝ) < (2 * n + 2 : ℝ) := by linarith
      have hpow : (2 * n + 2 : ℝ) ^ (-x) < (2 * n + 1 : ℝ) ^ (-x) :=
        Real.rpow_lt_rpow_of_neg (by positivity) hlt (by linarith)
      linarith
    · have hnonneg : 0 ≤ (2 * n + 1 : ℝ) ^ (-x) - (2 * n + 2 : ℝ) ^ (-x) := by
        have hlt : (2 * n + 1 : ℝ) < (2 * n + 2 : ℝ) := by linarith
        have hpow : (2 * n + 2 : ℝ) ^ (-x) < (2 * n + 1 : ℝ) ^ (-x) :=
          Real.rpow_lt_rpow_of_neg (by positivity) hlt (by linarith)
        linarith
      have h1 := norm_etaTerm_le (δ := x / 2) (R := ‖(x : ℂ)‖ + 1) (s := (x : ℂ)) (by linarith)
        (by simp only [Complex.ofReal_re]; linarith) (by linarith) n
      rw [hcast_term n, Complex.norm_real, Real.norm_of_nonneg hnonneg] at h1
      exact h1
  have hpos : 0 < ∑' n : ℕ, ((2 * n + 1 : ℝ) ^ (-x) - (2 * n + 2 : ℝ) ^ (-x)) := by
    refine hsum_real.tsum_pos (fun n => ?_) 0 ?_
    · have hlt : (2 * n + 1 : ℝ) < (2 * n + 2 : ℝ) := by linarith
      exact sub_nonneg.mpr (Real.rpow_lt_rpow_of_neg (by positivity) hlt (by linarith)).le
    · have hlt : (2 * (0 : ℕ) + 1 : ℝ) < (2 * (0 : ℕ) + 2 : ℝ) := by norm_num
      exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) hlt (by linarith))
  have heta_eq : etaFun (x : ℂ) =
      ((∑' n : ℕ, ((2 * n + 1 : ℝ) ^ (-x) - (2 * n + 2 : ℝ) ^ (-x)) : ℝ) : ℂ) := by
    rw [etaFun, Complex.ofReal_tsum]
    exact tsum_congr hcast_term
  intro hz
  rw [hz, mul_zero, heta_eq] at heq
  have hzero : (∑' n : ℕ, ((2 * n + 1 : ℝ) ^ (-x) - (2 * n + 2 : ℝ) ^ (-x))) = 0 :=
    Complex.ofReal_injective heq
  linarith

private noncomputable def invZeta : ℂ → ℂ :=
  Function.update (fun w : ℂ => (riemannZeta w)⁻¹) 1 0

private def zetaDomain : Set ℂ :=
  {w : ℂ | w = 1 ∨ riemannZeta w ≠ 0}

private lemma isOpen_zetaDomain : IsOpen zetaDomain := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  rcases hw with rfl | hnz
  · have hne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), (z - 1) * riemannZeta z ≠ 0 :=
      riemannZeta_residue_one.eventually_ne one_ne_zero
    rw [eventually_nhdsWithin_iff] at hne
    filter_upwards [hne] with z hz
    rcases eq_or_ne z 1 with rfl | hz1
    · exact Or.inl rfl
    · exact Or.inr (right_ne_zero_of_mul (hz hz1))
  · rcases eq_or_ne w 1 with rfl | hw1
    · have hne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), (z - 1) * riemannZeta z ≠ 0 :=
        riemannZeta_residue_one.eventually_ne one_ne_zero
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hne] with z hz
      rcases eq_or_ne z 1 with rfl | hz1
      · exact Or.inl rfl
      · exact Or.inr (right_ne_zero_of_mul (hz hz1))
    · have hcont : ContinuousAt riemannZeta w := (differentiableAt_riemannZeta hw1).continuousAt
      filter_upwards [hcont.eventually_ne hnz] with z hz
      exact Or.inr hz

private lemma differentiableOn_invZeta : DifferentiableOn ℂ invZeta zetaDomain := by
  intro w hw
  rcases eq_or_ne w 1 with rfl | hw1
  · have hne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), riemannZeta z ≠ 0 := by
      filter_upwards [riemannZeta_residue_one.eventually_ne one_ne_zero] with z hz
      exact right_ne_zero_of_mul hz
    have hdiff_punct : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ invZeta z := by
      filter_upwards [self_mem_nhdsWithin, hne] with z hz1 hznz
      exact ((differentiableAt_riemannZeta hz1).inv hznz).congr_of_eventuallyEq
        (by filter_upwards [eventually_ne_nhds hz1] with u hu using Function.update_of_ne hu ..)
    have hcont : ContinuousAt invZeta 1 := by
      rw [invZeta, continuousAt_update_same]
      have h1 : Tendsto (fun z : ℂ => z - 1) (𝓝[≠] 1) (𝓝 0) := by
        have hc : ContinuousAt (fun z : ℂ => z - 1) 1 :=
          (continuous_id.sub continuous_const).continuousAt
        simpa only [sub_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun z : ℂ => ((z - 1) * riemannZeta z)⁻¹) (𝓝[≠] 1) (𝓝 1) := by
        simpa using riemannZeta_residue_one.inv₀ one_ne_zero
      have hprod := h1.mul h2
      rw [zero_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hsub, one_mul]
    exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff_punct hcont
      |>.differentiableAt).differentiableWithinAt
  · have hnz : riemannZeta w ≠ 0 := hw.resolve_left hw1
    have hdiff : DifferentiableAt ℂ invZeta w :=
      ((differentiableAt_riemannZeta hw1).inv hnz).congr_of_eventuallyEq
        (by filter_upwards [eventually_ne_nhds hw1] with u hu using Function.update_of_ne hu ..)
    exact hdiff.differentiableWithinAt

private lemma real_Icc_subset_zetaDomain {x : ℝ} (hx0 : 0 ≤ x) :
    (x : ℂ) ∈ zetaDomain := by
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · right
    rw [Complex.ofReal_zero, riemannZeta_zero]
    norm_num
  · rcases lt_trichotomy x 1 with hxlt | rfl | hxgt
    · exact Or.inr (riemannZeta_ne_zero_of_real_Ioo hxpos hxlt)
    · exact Or.inl (by simp)
    · exact Or.inr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hxgt))

/-! Part 2: General Landau / Pringsheim theorem for non-negative Mellin integrals -/

private lemma real_exp_eq_tsum (x : ℝ) : Real.exp x = ∑' m : ℕ, x ^ m / (m.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

private lemma log_pow_mul_rpow_neg_le {t δ : ℝ} (ht : 1 < t) (hδ : 0 < δ) (m : ℕ) :
    (Real.log t) ^ m * t ^ (-δ) ≤ (m.factorial : ℝ) / δ ^ m := by
  have hu : 0 ≤ δ * Real.log t := mul_nonneg hδ.le (Real.log_nonneg ht.le)
  have hsum := Real.sum_le_exp_of_nonneg hu (m + 1)
  have hterm : (δ * Real.log t) ^ m / (m.factorial : ℝ) ≤ Real.exp (δ * Real.log t) := by
    have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
    exact (Finset.single_le_sum (fun i _ => by positivity) hmem).trans hsum
  have hexp : Real.exp (δ * Real.log t) = t ^ δ := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans ht), mul_comm]
  rw [hexp, mul_pow, mul_div_assoc] at hterm
  have h1 : (Real.log t) ^ m ≤ (m.factorial : ℝ) / δ ^ m * t ^ δ := by
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hδp : (0 : ℝ) < δ ^ m := pow_pos hδ m
    rw [div_mul_eq_mul_div, le_div_iff₀ hδp, mul_comm ((Real.log t) ^ m)]
    have h2 : δ ^ m * (Real.log t) ^ m ≤ t ^ δ * (m.factorial : ℝ) := by
      rwa [← mul_div_assoc, div_le_iff₀ hfac] at hterm
    linarith
  have htpos : 0 < t := zero_lt_one.trans ht
  calc
    (Real.log t) ^ m * t ^ (-δ)
        ≤ ((m.factorial : ℝ) / δ ^ m * t ^ δ) * t ^ (-δ) :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg htpos.le _)
    _ = (m.factorial : ℝ) / δ ^ m * (t ^ δ * t ^ (-δ)) := mul_assoc _ _ _
    _ = (m.factorial : ℝ) / δ ^ m := by
      rw [← Real.rpow_add htpos, add_neg_cancel, Real.rpow_zero, mul_one]

private lemma hasDerivAt_ofReal_cpow_neg_add_one {t : ℝ} (ht : 0 < t) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (t : ℂ) ^ (-(z + 1)))
      (-(Real.log t : ℂ) * (t : ℂ) ^ (-(s + 1))) s := by
  have heq : (fun z : ℂ => (t : ℂ) ^ (-(z + 1))) =
      fun z : ℂ => Complex.exp ((Real.log t : ℂ) * (-(z + 1))) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.ofReal_log ht.le]
  rw [heq]
  have h1 : HasDerivAt (fun z : ℂ => (Real.log t : ℂ) * (-(z + 1))) (-(Real.log t : ℂ)) s := by
    have hd := (((hasDerivAt_id s).add_const (1 : ℂ)).neg).const_mul (Real.log t : ℂ)
    exact hd.congr_deriv (by ring)
  have h2 := h1.cexp
  have hval : Complex.exp ((Real.log t : ℂ) * (-(s + 1))) = (t : ℂ) ^ (-(s + 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.ofReal_log ht.le]
  rw [hval] at h2
  exact h2.congr_deriv (by ring)

private noncomputable def mellinDeriv (B : ℝ → ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ), (B t : ℂ) * (-(Real.log t : ℂ)) ^ m * (t : ℂ) ^ (-(s + 1))

private lemma aestronglyMeasurable_mellin_integrand {B : ℝ → ℝ} (hB_meas : Measurable B)
    (m : ℕ) (s : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => (B t : ℂ) * (-(Real.log t : ℂ)) ^ m * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have h1 : Measurable (fun t : ℝ => (B t : ℂ) * (-(Real.log t : ℂ)) ^ m) :=
    (Complex.measurable_ofReal.comp hB_meas).mul
      (((Complex.measurable_ofReal.comp Real.measurable_log).neg).pow_const m)
  have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := fun t ht =>
    (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)

private lemma integrableOn_mellin_real {B : ℝ → ℝ} (hB_meas : Measurable B)
    (hB_nn : ∀ t, 1 < t → 0 ≤ B t) {σ : ℝ}
    (hI : IntegrableOn (fun t : ℝ => B t * t ^ (-σ - 1)) (Set.Ioi (1 : ℝ)))
    (m : ℕ) {c : ℝ} (hc : σ < c) :
    IntegrableOn (fun t : ℝ => B t * (Real.log t) ^ m * t ^ (-c - 1)) (Set.Ioi (1 : ℝ)) := by
  have hδ : 0 < c - σ := sub_pos.mpr hc
  have hmeas : AEStronglyMeasurable (fun t : ℝ => B t * (Real.log t) ^ m * t ^ (-c - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((hB_meas.mul (Real.measurable_log.pow_const m)).mul
      (measurable_id.pow_const (-c - 1))).aestronglyMeasurable
  refine (hI.const_mul ((m.factorial : ℝ) / (c - σ) ^ m)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  have hnn : 0 ≤ B t * (Real.log t) ^ m * t ^ (-c - 1) :=
    mul_nonneg (mul_nonneg (hB_nn t ht) (pow_nonneg (Real.log_nonneg ht.le) m))
      (Real.rpow_nonneg htpos.le _)
  rw [Real.norm_of_nonneg hnn]
  have hpow : t ^ (-c - 1) = t ^ (-σ - 1) * t ^ (-(c - σ)) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  rw [hpow]
  calc
    B t * (Real.log t) ^ m * (t ^ (-σ - 1) * t ^ (-(c - σ)))
        = ((Real.log t) ^ m * t ^ (-(c - σ))) * (B t * t ^ (-σ - 1)) := by ring
    _ ≤ ((m.factorial : ℝ) / (c - σ) ^ m) * (B t * t ^ (-σ - 1)) :=
      mul_le_mul_of_nonneg_right (log_pow_mul_rpow_neg_le ht hδ m)
        (mul_nonneg (hB_nn t ht) (Real.rpow_nonneg htpos.le _))

private lemma hasDerivAt_mellinDeriv {B : ℝ → ℝ} (hB_meas : Measurable B)
    (hB_nn : ∀ t, 1 < t → 0 ≤ B t) {σ : ℝ}
    (hI : IntegrableOn (fun t : ℝ => B t * t ^ (-σ - 1)) (Set.Ioi (1 : ℝ)))
    (m : ℕ) {s₀ : ℂ} (hs₀ : σ < s₀.re) :
    HasDerivAt (mellinDeriv B m) (mellinDeriv B (m + 1) s₀) s₀ := by
  set δ : ℝ := (s₀.re - σ) / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hF_int : IntegrableOn
      (fun t : ℝ => (B t : ℂ) * (-(Real.log t : ℂ)) ^ m * (t : ℂ) ^ (-(s₀ + 1)))
      (Set.Ioi (1 : ℝ)) := by
    refine (integrableOn_mellin_real hB_meas hB_nn hI m hs₀).mono'
      (aestronglyMeasurable_mellin_integrand hB_meas m s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hB_nn t ht),
      norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg ht.le),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re, Complex.add_re, Complex.one_re,
      show -(s₀.re + 1) = -s₀.re - 1 by ring]
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    (s := Metric.ball s₀ δ)
    (F := fun z t => (B t : ℂ) * (-(Real.log t : ℂ)) ^ m * (t : ℂ) ^ (-(z + 1)))
    (F' := fun z t => (B t : ℂ) * (-(Real.log t : ℂ)) ^ (m + 1) * (t : ℂ) ^ (-(z + 1)))
    (bound := fun t => ((m + 1).factorial : ℝ) / δ ^ (m + 1) * (B t * t ^ (-σ - 1)))
    (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun z => aestronglyMeasurable_mellin_integrand hB_meas m z)
    hF_int
    (aestronglyMeasurable_mellin_integrand hB_meas (m + 1) s₀)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have htpos : 0 < t := zero_lt_one.trans ht
      have hzre : σ + δ < z.re := by
        have hdist : ‖z - s₀‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
        have hre : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
          rw [← Complex.sub_re]
          exact Complex.abs_re_le_norm (z - s₀)
        have hle := (abs_lt.mp (hre.trans_lt hdist)).1
        dsimp only [δ] at hle ⊢
        linarith
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hB_nn t ht),
        norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg ht.le),
        Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re, Complex.add_re, Complex.one_re]
      have hle_pow : t ^ (-(z.re + 1)) ≤ t ^ (-(σ + δ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
      have hsplit : t ^ (-(σ + δ) - 1) = t ^ (-σ - 1) * t ^ (-δ) := by
        rw [← Real.rpow_add htpos]
        congr 1
        ring
      calc
        B t * Real.log t ^ (m + 1) * t ^ (-(z.re + 1))
            ≤ B t * Real.log t ^ (m + 1) * (t ^ (-σ - 1) * t ^ (-δ)) := by
              rw [← hsplit]
              exact mul_le_mul_of_nonneg_left hle_pow
                (mul_nonneg (hB_nn t ht) (pow_nonneg (Real.log_nonneg ht.le) _))
        _ = (Real.log t ^ (m + 1) * t ^ (-δ)) * (B t * t ^ (-σ - 1)) := by ring
        _ ≤ (((m + 1).factorial : ℝ) / δ ^ (m + 1)) * (B t * t ^ (-σ - 1)) :=
          mul_le_mul_of_nonneg_right (log_pow_mul_rpow_neg_le ht hδ (m + 1))
            (mul_nonneg (hB_nn t ht) (Real.rpow_nonneg htpos.le _)))
    (hI.const_mul (((m + 1).factorial : ℝ) / δ ^ (m + 1)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
      have htpos : 0 < t := zero_lt_one.trans ht
      have hd := (hasDerivAt_ofReal_cpow_neg_add_one htpos z).const_mul
        ((B t : ℂ) * (-(Real.log t : ℂ)) ^ m)
      exact hd.congr_deriv (by rw [pow_succ]; ring))
  exact hres.2

private lemma iteratedDeriv_mellinDeriv {B : ℝ → ℝ} (hB_meas : Measurable B)
    (hB_nn : ∀ t, 1 < t → 0 ≤ B t) {σ : ℝ}
    (hI : IntegrableOn (fun t : ℝ => B t * t ^ (-σ - 1)) (Set.Ioi (1 : ℝ)))
    (m : ℕ) :
    ∀ s : ℂ, σ < s.re → iteratedDeriv m (mellinDeriv B 0) s = mellinDeriv B m s := by
  induction m with
  | zero =>
    intro s _
    rw [iteratedDeriv_zero]
  | succ m ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv m (mellinDeriv B 0) =ᶠ[𝓝 s] mellinDeriv B m := by
      refine eventuallyEq_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) fun z hz => ih z hz
    rw [heq.deriv_eq]
    exact (hasDerivAt_mellinDeriv hB_meas hB_nn hI m hs).deriv

private lemma mellinDeriv_ofReal {B : ℝ → ℝ} (m : ℕ) (c : ℝ) :
    mellinDeriv B m (c : ℂ) =
      (-1 : ℂ) ^ m * ((∫ t in Set.Ioi (1 : ℝ), B t * (Real.log t) ^ m * t ^ (-c - 1) : ℝ) : ℂ) := by
  have hof : ∫ t in Set.Ioi (1 : ℝ), ((B t * (Real.log t) ^ m * t ^ (-c - 1) : ℝ) : ℂ) =
      ((∫ t in Set.Ioi (1 : ℝ), B t * (Real.log t) ^ m * t ^ (-c - 1) : ℝ) : ℂ) :=
    integral_ofReal
  rw [mellinDeriv, ← hof, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have htpos : 0 < t := zero_lt_one.trans ht
  have hcpow : (t : ℂ) ^ (-((c : ℂ) + 1)) = ((t ^ (-c - 1) : ℝ) : ℂ) := by
    rw [show -((c : ℂ) + 1) = ((-c - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow htpos.le]
  rw [hcpow, show -(Real.log t : ℂ) = (-1 : ℂ) * (Real.log t : ℂ) by ring, mul_pow]
  push_cast
  ring

private lemma landau_step {B : ℝ → ℝ} (hB_meas : Measurable B)
    (hB_nn : ∀ t, 1 < t → 0 ≤ B t) {G : ℂ → ℂ} {σ R : ℝ} (hR : 0 < R)
    (hI : IntegrableOn (fun t : ℝ => B t * t ^ (-σ - 1)) (Set.Ioi (1 : ℝ)))
    (hEq : G =ᶠ[𝓝 ((σ + R / 4 : ℝ) : ℂ)] mellinDeriv B 0)
    (hG_ball : DifferentiableOn ℂ G (Metric.ball ((σ + R / 4 : ℝ) : ℂ) (7 / 4 * R))) :
    IntegrableOn (fun t : ℝ => B t * t ^ (-(σ - R / 2) - 1)) (Set.Ioi (1 : ℝ)) ∧
      G =ᶠ[𝓝 (((σ - R / 2) + R / 4 : ℝ) : ℂ)] mellinDeriv B 0 := by
  set c : ℝ := σ + R / 4
  set σ' : ℝ := σ - R / 2
  set d : ℝ := c - σ'
  have hd_eq : d = 3 / 4 * R := by
    dsimp only [d, c, σ']
    ring
  have hd_pos : 0 < d := by linarith
  have hσc : σ < c := by
    dsimp only [c]
    linarith
  have hσ'_ball : (σ' : ℂ) ∈ Metric.ball (c : ℂ) (7 / 4 * R) := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith : σ' - c < 0)]
    linarith
  have hTaylor := Complex.hasSum_taylorSeries_on_ball hG_ball hσ'_ball
  let I_m : ℕ → ℝ := fun m => ∫ t in Set.Ioi (1 : ℝ), B t * (Real.log t) ^ m * t ^ (-c - 1)
  have hterm : ∀ m : ℕ,
      (m.factorial : ℂ)⁻¹ • ((σ' : ℂ) - (c : ℂ)) ^ m • iteratedDeriv m G (c : ℂ) =
        (((d ^ m / (m.factorial : ℝ)) * I_m m : ℝ) : ℂ) := by
    intro m
    rw [hEq.iteratedDeriv_eq m, iteratedDeriv_mellinDeriv hB_meas hB_nn hI m (c : ℂ)
      (by simpa using hσc), mellinDeriv_ofReal]
    have hsub : (σ' : ℂ) - (c : ℂ) = (-1 : ℂ) * (d : ℂ) := by
      dsimp only [d]
      push_cast
      ring
    rw [hsub, mul_pow, smul_eq_mul, smul_eq_mul]
    have hneg1 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    push_cast
    calc
      (m.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ m * (d : ℂ) ^ m * ((-1 : ℂ) ^ m * (I_m m : ℂ)))
          = ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) * ((d : ℂ) ^ m / (m.factorial : ℂ) * (I_m m : ℂ)) := by
            rw [div_eq_mul_inv]
            ring
      _ = (d : ℂ) ^ m / (m.factorial : ℂ) * (I_m m : ℂ) := by rw [hneg1, one_mul]
  have hsum_real : Summable (fun m : ℕ => (d ^ m / (m.factorial : ℝ)) * I_m m) := by
    have hsumC : Summable (fun m : ℕ => (((d ^ m / (m.factorial : ℝ)) * I_m m : ℝ) : ℂ)) := by
      refine hTaylor.summable.congr hterm
    exact (Complex.reCLM.summable hsumC).congr fun m => by
      simp only [Complex.reCLM_apply, Complex.ofReal_re]
  have hIm_nn : ∀ m : ℕ, 0 ≤ I_m m := fun m =>
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (mul_nonneg (hB_nn t ht) (pow_nonneg (Real.log_nonneg ht.le) m))
        (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
  have hsum_enn_lt :
      (∑' m : ℕ, ENNReal.ofReal ((d ^ m / (m.factorial : ℝ)) * I_m m)) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (by positivity) (hIm_nn m)) hsum_real]
    exact ENNReal.ofReal_lt_top
  have hterm_lintegral : ∀ m : ℕ,
      ENNReal.ofReal ((d ^ m / (m.factorial : ℝ)) * I_m m) =
        ∫⁻ t in Set.Ioi (1 : ℝ),
          ENNReal.ofReal (B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ))) := by
    intro m
    have hint : IntegrableOn
        (fun t : ℝ => B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ)))
        (Set.Ioi (1 : ℝ)) := by
      have h1 := (integrableOn_mellin_real hB_meas hB_nn hI m hσc).const_mul
        (d ^ m / (m.factorial : ℝ))
      refine h1.congr (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [mul_pow]
      ring
    have heq_int : (d ^ m / (m.factorial : ℝ)) * I_m m =
        ∫ t in Set.Ioi (1 : ℝ),
          B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ)) := by
      dsimp only [I_m]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [mul_pow]
      ring
    rw [heq_int]
    refine ofReal_integral_eq_lintegral_ofReal hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (hB_nn t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _))
      (div_nonneg (pow_nonneg (mul_nonneg hd_pos.le (Real.log_nonneg ht.le)) m)
        (Nat.cast_nonneg _))
  have hlint_lt :
      (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (B t * t ^ (-σ' - 1))) < ⊤ := by
    have hmeas_m : ∀ m : ℕ, AEMeasurable
        (fun t : ℝ =>
          ENNReal.ofReal (B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ))))
        (volume.restrict (Set.Ioi (1 : ℝ))) := fun m =>
      (((hB_meas.mul (measurable_id.pow_const (-c - 1))).mul
        (((Real.measurable_log.const_mul d).pow_const m).div_const _)).ennreal_ofReal).aemeasurable
    have hswapped :
        (∫⁻ t in Set.Ioi (1 : ℝ),
          ∑' m : ℕ,
            ENNReal.ofReal (B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ)))) <
          ⊤ := by
      rw [lintegral_tsum hmeas_m]
      simpa only [← hterm_lintegral] using hsum_enn_lt
    have hae : (fun t : ℝ =>
        ∑' m : ℕ, ENNReal.ofReal (B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ))))
        =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        (fun t : ℝ => ENNReal.ofReal (B t * t ^ (-σ' - 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := zero_lt_one.trans ht
      have hsum_t : Summable
          (fun m : ℕ => B t * t ^ (-c - 1) * ((d * Real.log t) ^ m / (m.factorial : ℝ))) :=
        (Real.summable_pow_div_factorial (d * Real.log t)).mul_left (B t * t ^ (-c - 1))
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m =>
          mul_nonneg (mul_nonneg (hB_nn t ht) (Real.rpow_nonneg htpos.le _))
            (div_nonneg (pow_nonneg (mul_nonneg hd_pos.le (Real.log_nonneg ht.le)) m)
              (Nat.cast_nonneg _))) hsum_t,
        tsum_mul_left, ← real_exp_eq_tsum,
        show Real.exp (d * Real.log t) = t ^ d by
          rw [Real.rpow_def_of_pos htpos, mul_comm],
        mul_assoc, ← Real.rpow_add htpos, show -c - 1 + d = -σ' - 1 by dsimp only [d]; ring]
    rwa [← lintegral_congr_ae hae]
  have hI' : IntegrableOn (fun t : ℝ => B t * t ^ (-σ' - 1)) (Set.Ioi (1 : ℝ)) := by
    refine ⟨(hB_meas.mul (measurable_id.pow_const (-σ' - 1))).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hae_enorm : (fun t : ℝ => ‖B t * t ^ (-σ' - 1)‖ₑ)
        =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        (fun t : ℝ => ENNReal.ofReal (B t * t ^ (-σ' - 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hnn : 0 ≤ B t * t ^ (-σ' - 1) :=
        mul_nonneg (hB_nn t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
      rw [Real.enorm_eq_ofReal hnn]
    rwa [lintegral_congr_ae hae_enorm]
  refine ⟨hI', ?_⟩
  let W : Set ℂ := Metric.ball (c : ℂ) (7 / 4 * R) ∩ {z : ℂ | σ' < z.re}
  have hW_open : IsOpen W :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hW_conv : Convex ℝ W := by
    refine (convex_ball (c : ℂ) (7 / 4 * R)).inter ?_
    intro x hx y hy a b ha hb hab
    have hx' : σ' < x.re := hx
    have hy' : σ' < y.re := hy
    change σ' < (a • x + b • y).re
    simp only [add_re, Complex.real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by linarith
      rw [hb']
      nlinarith
    · have h1 : a * σ' < a * x.re := mul_lt_mul_of_pos_left hx' ha'
      have h2 : b * σ' ≤ b * y.re := mul_le_mul_of_nonneg_left hy'.le hb
      have h3 : a * σ' + b * σ' = σ' := by rw [← add_mul, hab, one_mul]
      linarith
  have hF_diffW : DifferentiableOn ℂ (mellinDeriv B 0) W := fun z hz =>
    (hasDerivAt_mellinDeriv hB_meas hB_nn hI' 0 hz.2).differentiableAt.differentiableWithinAt
  have hG_diffW : DifferentiableOn ℂ G W := hG_ball.mono Set.inter_subset_left
  have hcW : (c : ℂ) ∈ W := by
    refine ⟨Metric.mem_ball_self (by linarith), ?_⟩
    change σ' < (c : ℂ).re
    simp only [Complex.ofReal_re]
    dsimp only [c, σ']
    linarith
  have hc'W : ((σ' + R / 4 : ℝ) : ℂ) ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (by dsimp only [c, σ']; linarith)]
      dsimp only [c, σ']
      linarith
    · change σ' < ((σ' + R / 4 : ℝ) : ℂ).re
      simp only [Complex.ofReal_re]
      linarith
  have hEqW := (hG_diffW.analyticOnNhd hW_open).eqOn_of_preconnected_of_eventuallyEq
    (hF_diffW.analyticOnNhd hW_open) hW_conv.isPreconnected hcW hEq
  exact eventuallyEq_of_mem (hW_open.mem_nhds hc'W) hEqW

private lemma exists_uniform_ball_of_Icc {a b : ℝ} (hab : a ≤ b) {U : Set ℂ} (hU : IsOpen U)
    (hsub : ∀ σ ∈ Set.Icc a b, (σ : ℂ) ∈ U) :
    ∃ R > 0, ∀ σ ∈ Set.Icc a b, Metric.ball (σ : ℂ) (2 * R) ⊆ U := by
  have hrad : ∀ z ∈ Complex.ofReal '' Set.Icc a b,
      ∃ r > 0, Metric.ball z (2 * r) ⊆ U := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU (σ : ℂ) (hsub σ hσ)
    exact ⟨ρ / 2, by linarith, by simpa [show 2 * (ρ / 2) = ρ by ring] using hball⟩
  choose r hr_pos hr_ball using hrad
  let K : Set ℂ := Complex.ofReal '' Set.Icc a b
  have hK_comp : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hcover : K ⊆ ⋃ (z : K), Metric.ball z.1 (r z.1 z.2) := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hr_pos z hz)⟩
  obtain ⟨s, hs⟩ := hK_comp.elim_finite_subcover (fun z : K => Metric.ball z.1 (r z.1 z.2))
    (fun _ => Metric.isOpen_ball) hcover
  have haK : (a : ℂ) ∈ K := ⟨a, Set.left_mem_Icc.mpr hab, rfl⟩
  have hs_ne : s.Nonempty := by
    have ha_mem := hs haK
    simp only [Set.mem_iUnion] at ha_mem
    obtain ⟨z, hz, _⟩ := ha_mem
    exact ⟨z, hz⟩
  let R : ℝ := (s.inf' hs_ne fun z => r z.1 z.2) / 2
  have hR_pos : 0 < R := by
    dsimp only [R]
    have hinf : 0 < s.inf' hs_ne fun z => r z.1 z.2 :=
      (Finset.lt_inf'_iff hs_ne).mpr fun z _ => hr_pos z.1 z.2
    linarith
  refine ⟨R, hR_pos, fun σ hσ w hw => ?_⟩
  have hσK : (σ : ℂ) ∈ K := ⟨σ, hσ, rfl⟩
  have hmem := hs hσK
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨z, hzs, hσz⟩ := hmem
  have hR_le : 2 * R ≤ r z.1 z.2 := by
    dsimp only [R]
    have hle := Finset.inf'_le (f := fun u : K => r u.1 u.2) hzs
    linarith
  have hwz : w ∈ Metric.ball z.1 (2 * r z.1 z.2) := by
    rw [Metric.mem_ball] at hw hσz ⊢
    calc
      dist w z.1 ≤ dist w (σ : ℂ) + dist (σ : ℂ) z.1 := dist_triangle _ _ _
      _ < 2 * R + r z.1 z.2 := add_lt_add hw hσz
      _ ≤ 2 * r z.1 z.2 := by linarith
  exact hr_ball z.1 z.2 hwz

private lemma landau_theorem {B : ℝ → ℝ} (hB_meas : Measurable B)
    (hB_nn : ∀ t, 1 < t → 0 ≤ B t) {G : ℂ → ℂ} {U : Set ℂ} {a b : ℝ} (hab : a ≤ b)
    (hU_open : IsOpen U) (hU_sub : ∀ σ ∈ Set.Icc a b, (σ : ℂ) ∈ U)
    (hG_diff : DifferentiableOn ℂ G U)
    (hIb : IntegrableOn (fun t : ℝ => B t * t ^ (-b - 1)) (Set.Ioi (1 : ℝ)))
    (hEq : ∀ s : ℂ, b < s.re → G s = mellinDeriv B 0 s) :
    IntegrableOn (fun t : ℝ => B t * t ^ (-a - 1)) (Set.Ioi (1 : ℝ)) := by
  obtain ⟨R, hR_pos, hR_ball⟩ := exists_uniform_ball_of_Icc hab hU_open hU_sub
  have hstep_ind : ∀ k : ℕ, (∀ j < k, a ≤ b - (j : ℝ) * (R / 2)) →
      IntegrableOn (fun t : ℝ => B t * t ^ (-(b - (k : ℝ) * (R / 2)) - 1)) (Set.Ioi (1 : ℝ)) ∧
        G =ᶠ[𝓝 (((b - (k : ℝ) * (R / 2)) + R / 4 : ℝ) : ℂ)] mellinDeriv B 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      refine ⟨hIb, ?_⟩
      refine eventuallyEq_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by change b < ((b + R / 4 : ℝ) : ℂ).re; simp only [Complex.ofReal_re]; linarith)) hEq
    | succ k ih =>
      intro hk
      obtain ⟨hIk, hEqk⟩ := ih fun j hj => hk j (Nat.lt_succ_of_lt hj)
      set σk : ℝ := b - (k : ℝ) * (R / 2)
      have hσk_mem : σk ∈ Set.Icc a b := by
        refine ⟨hk k (Nat.lt_succ_self k), ?_⟩
        dsimp only [σk]
        have : 0 ≤ (k : ℝ) * (R / 2) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
        linarith
      have hball_sub : Metric.ball ((σk + R / 4 : ℝ) : ℂ) (7 / 4 * R) ⊆ U := by
        intro z hz
        refine hR_ball σk hσk_mem ?_
        rw [Metric.mem_ball] at hz ⊢
        have hdist : dist ((σk + R / 4 : ℝ) : ℂ) (σk : ℂ) = R / 4 := by
          rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            show σk + R / 4 - σk = R / 4 by ring, abs_of_pos (by linarith)]
        calc
          dist z (σk : ℂ) ≤ dist z ((σk + R / 4 : ℝ) : ℂ) + dist ((σk + R / 4 : ℝ) : ℂ) (σk : ℂ) :=
            dist_triangle _ _ _
          _ < 7 / 4 * R + R / 4 := by rw [hdist]; linarith
          _ = 2 * R := by ring
      have hnext := landau_step hB_meas hB_nn hR_pos hIk hEqk (hG_diff.mono hball_sub)
      have heq_next : b - ((k + 1 : ℕ) : ℝ) * (R / 2) = σk - R / 2 := by
        dsimp only [σk]
        push_cast
        ring
      rw [heq_next]
      exact hnext
  set K : ℕ := ⌊(b - a) / (R / 2)⌋₊ + 1
  have hK_pre : ∀ j < K, a ≤ b - (j : ℝ) * (R / 2) := by
    intro j hj
    have hj_le : j ≤ ⌊(b - a) / (R / 2)⌋₊ := Nat.lt_succ_iff.mp hj
    have hj_real : (j : ℝ) ≤ (b - a) / (R / 2) :=
      (Nat.cast_le.mpr hj_le).trans (Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) (by linarith)))
    have hmul : (j : ℝ) * (R / 2) ≤ b - a := (le_div_iff₀ (by linarith)).mp hj_real
    linarith
  have hIK := (hstep_ind K hK_pre).1
  have hK_lt : b - (K : ℝ) * (R / 2) < a := by
    have hlt : (b - a) / (R / 2) < (K : ℝ) := by
      dsimp only [K]
      exact_mod_cast Nat.lt_floor_add_one ((b - a) / (R / 2))
    have hmul : b - a < (K : ℝ) * (R / 2) := (div_lt_iff₀ (by linarith)).mp hlt
    linarith
  refine hIK.mono' ((hB_meas.mul (measurable_id.pow_const (-a - 1))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  have hnn : 0 ≤ B t * t ^ (-a - 1) := mul_nonneg (hB_nn t ht) (Real.rpow_nonneg htpos.le _)
  rw [Real.norm_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (hB_nn t ht)

/-! Part 3: Application to `aPow r n = ∑ k ∈ Icc 1 n, μ(k) * k^r` for all `r ≥ 1` -/

private def aPow (r n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k * (k : ℤ) ^ r

private lemma abs_aPow_le (r n : ℕ) : |(aPow r n : ℝ)| ≤ (n : ℝ) ^ (r + 1) := by
  have h1 : |(aPow r n : ℝ)| ≤
      ∑ k ∈ Finset.Icc 1 n, |(ArithmeticFunction.moebius k : ℝ) * (k : ℝ) ^ r| := by
    rw [aPow, Int.cast_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rfl
  have h2 : ∑ k ∈ Finset.Icc 1 n, |(ArithmeticFunction.moebius k : ℝ) * (k : ℝ) ^ r| ≤
      ∑ _k ∈ Finset.Icc 1 n, (n : ℝ) ^ r := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (a := (k : ℝ) ^ r) (pow_nonneg (Nat.cast_nonneg k) r)]
    have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    have hkn : (k : ℝ) ^ r ≤ (n : ℝ) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg k) (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2) r
    calc
      |(ArithmeticFunction.moebius k : ℝ)| * (k : ℝ) ^ r ≤ 1 * (n : ℝ) ^ r :=
        mul_le_mul hmu hkn (pow_nonneg (Nat.cast_nonneg k) r) zero_le_one
      _ = (n : ℝ) ^ r := one_mul _
  calc
    |(aPow r n : ℝ)| ≤ ∑ _k ∈ Finset.Icc 1 n, (n : ℝ) ^ r := h1.trans h2
    _ = ((Finset.Icc 1 n).card : ℝ) * (n : ℝ) ^ r := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) ^ (r + 1) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel, pow_succ, mul_comm]

private lemma aPow_succ (r n : ℕ) :
    aPow r (n + 1) - aPow r n = ArithmeticFunction.moebius (n + 1) * ((n + 1 : ℕ) : ℤ) ^ r := by
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : n + 1 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    omega
  rw [aPow, aPow, hIcc, Finset.sum_insert hnotmem]
  ring

private lemma LSeries_moebius_mul_pow (r : ℕ) {s : ℂ} (hs : (r + 1 : ℝ) < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ r) s ∧
      LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ r) s =
        invZeta (s - (r : ℂ)) := by
  have hsr : 1 < (s - (r : ℂ)).re := by
    rw [Complex.sub_re, Complex.natCast_re]
    linarith
  have hterm : ∀ n : ℕ,
      LSeries.term (fun k : ℕ => (ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ r) s n =
        LSeries.term (fun k : ℕ => (ArithmeticFunction.moebius k : ℂ)) (s - (r : ℂ)) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_natCast, div_div_eq_mul_div]
  have hsum : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ r) s := by
    have hmu := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsr
    rw [LSeriesSummable, funext hterm]
    exact hmu
  refine ⟨hsum, ?_⟩
  have hL : LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ r) s =
      LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s - (r : ℂ)) :=
    tsum_congr hterm
  rw [hL]
  have hmul := LSeries_one_mul_Lseries_moebius hsr
  rw [LSeries_one_eq_riemannZeta hsr] at hmul
  have hne1 : s - (r : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h
    rw [Complex.one_re] at this
    linarith
  rw [invZeta, Function.update_of_ne hne1]
  have hzeta_ne : riemannZeta (s - (r : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hsr
  exact eq_inv_of_mul_eq_one_right hmul

private lemma aestronglyMeasurable_ofReal_cpow (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := fun t ht =>
    (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  exact hcont.aestronglyMeasurable measurableSet_Ioi

private lemma integrableOn_indicator_Ioc (N : ℕ) (C : ℝ) :
    IntegrableOn (Set.indicator (Set.Ioc (1 : ℝ) ((N + 1 : ℕ) : ℝ)) (fun _ => C))
      (Set.Ioi (1 : ℝ)) := by
  have h1 : IntegrableOn (fun _ : ℝ => C) (Set.Ioc (1 : ℝ) ((N + 1 : ℕ) : ℝ)) :=
    integrableOn_const (by simp)
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr h1).integrableOn

private lemma differentiable_finite_part (r N : ℕ) (ε : ℤ) :
    Differentiable ℂ (fun s : ℂ =>
      ∫ t in Set.Ioi (1 : ℝ),
        (if ⌊t⌋₊ ≤ N then ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) else 0) * (t : ℂ) ^ (-(s + 1))) := by
  let cN : ℝ → ℂ := fun t => if ⌊t⌋₊ ≤ N then ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) else 0
  have hcN_meas : Measurable cN :=
    (measurable_of_countable (fun k : ℕ =>
      if k ≤ N then ((ε * aPow r k : ℤ) : ℂ) else 0)).comp Nat.measurable_floor
  have hcN_zero : ∀ t : ℝ, ((N + 1 : ℕ) : ℝ) < t → cN t = 0 := by
    intro t ht
    have hfl : N + 1 ≤ ⌊t⌋₊ := Nat.le_floor ht.le
    dsimp only [cN]
    split_ifs with h
    · omega
    · rfl
  have hcN_bound : ∀ t : ℝ, ‖cN t‖ ≤ |(ε : ℝ)| * (N : ℝ) ^ (r + 1) := by
    intro t
    dsimp only [cN]
    split_ifs with h
    · rw [Int.cast_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
      have h1 := abs_aPow_le r ⌊t⌋₊
      have h2 : (⌊t⌋₊ : ℝ) ^ (r + 1) ≤ (N : ℝ) ^ (r + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr h) (r + 1)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
    · rw [norm_zero]
      positivity
  intro s₀
  set C : ℝ := |(ε : ℝ)| * (N : ℝ) ^ (r + 1) * Real.log ((N + 1 : ℕ) : ℝ) *
    ((N + 1 : ℕ) : ℝ) ^ (‖s₀‖ + 1)
  let bound : ℝ → ℝ := Set.indicator (Set.Ioc (1 : ℝ) ((N + 1 : ℕ) : ℝ)) (fun _ => C)
  have hbound_int : IntegrableOn bound (Set.Ioi (1 : ℝ)) := integrableOn_indicator_Ioc N C
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => cN t * (t : ℂ) ^ (-(z + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := fun z =>
    hcN_meas.aestronglyMeasurable.mul (aestronglyMeasurable_ofReal_cpow z)
  have hmeas_F' : AEStronglyMeasurable
      (fun t : ℝ => cN t * (-(Real.log t : ℂ)) * (t : ℂ) ^ (-(s₀ + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (hcN_meas.mul (Complex.measurable_ofReal.comp Real.measurable_log).neg).aestronglyMeasurable.mul
      (aestronglyMeasurable_ofReal_cpow s₀)
  have hF_int : IntegrableOn (fun t : ℝ => cN t * (t : ℂ) ^ (-(s₀ + 1))) (Set.Ioi (1 : ℝ)) := by
    let C₀ : ℝ := |(ε : ℝ)| * (N : ℝ) ^ (r + 1) * ((N + 1 : ℕ) : ℝ) ^ (‖s₀‖ + 1)
    refine (integrableOn_indicator_Ioc N C₀).mono' (hmeas_F s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hle : t ≤ ((N + 1 : ℕ) : ℝ)
    · have hmem : t ∈ Set.Ioc (1 : ℝ) ((N + 1 : ℕ) : ℝ) := ⟨ht, hle⟩
      rw [Set.indicator_of_mem hmem]
      have htpos : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re,
        Complex.add_re, Complex.one_re]
      have hre : -(s₀.re + 1) ≤ ‖s₀‖ + 1 := by
        have := Complex.abs_re_le_norm s₀
        linarith [neg_le_abs s₀.re]
      have hpow1 : t ^ (-(s₀.re + 1)) ≤ t ^ (‖s₀‖ + 1) :=
        Real.rpow_le_rpow_of_exponent_le ht.le hre
      have hpow2 : t ^ (‖s₀‖ + 1) ≤ ((N + 1 : ℕ) : ℝ) ^ (‖s₀‖ + 1) :=
        Real.rpow_le_rpow htpos.le hle (by positivity)
      exact mul_le_mul (hcN_bound t) (hpow1.trans hpow2) (Real.rpow_nonneg htpos.le _)
        (by positivity)
    · have hgt : ((N + 1 : ℕ) : ℝ) < t := lt_of_not_ge hle
      rw [Set.indicator_of_notMem (fun h => hgt.not_ge h.2), hcN_zero t hgt, zero_mul, norm_zero]
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    (s := Metric.ball s₀ 1)
    (F := fun z t => cN t * (t : ℂ) ^ (-(z + 1)))
    (F' := fun z t => cN t * (-(Real.log t : ℂ)) * (t : ℂ) ^ (-(z + 1)))
    (bound := bound)
    (Metric.ball_mem_nhds s₀ zero_lt_one)
    (Eventually.of_forall hmeas_F)
    hF_int
    hmeas_F'
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      by_cases hle : t ≤ ((N + 1 : ℕ) : ℝ)
      · have hmem : t ∈ Set.Ioc (1 : ℝ) ((N + 1 : ℕ) : ℝ) := ⟨ht, hle⟩
        rw [show bound t = C from Set.indicator_of_mem hmem _]
        have htpos : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
          Real.norm_of_nonneg (Real.log_nonneg ht.le),
          Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re,
          Complex.add_re, Complex.one_re]
        have hzre : -(z.re + 1) ≤ ‖s₀‖ + 1 := by
          have hdist : ‖z - s₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
          have h1 : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
            rw [← Complex.sub_re]
            exact Complex.abs_re_le_norm (z - s₀)
          have h2 : |s₀.re| ≤ ‖s₀‖ := Complex.abs_re_le_norm s₀
          linarith [(abs_lt.mp (h1.trans_lt hdist)).1, (abs_le.mp h2).1]
        have hlog : Real.log t ≤ Real.log ((N + 1 : ℕ) : ℝ) := Real.log_le_log htpos hle
        have hpow1 : t ^ (-(z.re + 1)) ≤ t ^ (‖s₀‖ + 1) :=
          Real.rpow_le_rpow_of_exponent_le ht.le hzre
        have hpow2 : t ^ (‖s₀‖ + 1) ≤ ((N + 1 : ℕ) : ℝ) ^ (‖s₀‖ + 1) :=
          Real.rpow_le_rpow htpos.le hle (by positivity)
        have hm1 : ‖cN t‖ * Real.log t ≤
            |(ε : ℝ)| * (N : ℝ) ^ (r + 1) * Real.log ((N + 1 : ℕ) : ℝ) :=
          mul_le_mul (hcN_bound t) hlog (Real.log_nonneg ht.le) (by positivity)
        exact mul_le_mul hm1 (hpow1.trans hpow2) (Real.rpow_nonneg htpos.le _)
          (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))))
      · have hgt : ((N + 1 : ℕ) : ℝ) < t := lt_of_not_ge hle
        rw [show bound t = 0 from Set.indicator_of_notMem (fun h => hgt.not_ge h.2) _,
          hcN_zero t hgt, zero_mul, zero_mul, norm_zero])
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
      have hd := (hasDerivAt_ofReal_cpow_neg_add_one (zero_lt_one.trans ht) z).const_mul (cN t)
      exact hd.congr_deriv (by ring))
  exact hres.2.differentiableAt

private lemma not_integrableOn_of_prime_intervals {f : ℝ → ℝ}
    (hf_nn : ∀ t, 1 < t → 0 ≤ f t) (hf_int : IntegrableOn f (Set.Ioi (1 : ℝ)))
    {k : Nat.Primes → ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c)
    (hk_inj : ∀ p q : Nat.Primes, M < (p : ℕ) → M < (q : ℕ) → k p = k q → p = q)
    (hk_pos : ∀ p : Nat.Primes, M < (p : ℕ) → 1 ≤ k p)
    (hf_ge : ∀ p : Nat.Primes, M < (p : ℕ) →
      ∀ t ∈ Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ), c * (1 / ((p : ℕ) : ℝ)) ≤ f t) :
    False := by
  let g : Nat.Primes → ℝ := fun p => if M < (p : ℕ) then c * (1 / ((p : ℕ) : ℝ)) else 0
  have hg_sum : Summable g := by
    refine summable_of_sum_le (c := ∫ t in Set.Ioi (1 : ℝ), f t) (fun p => by
      dsimp only [g]
      split_ifs
      · positivity
      · exact le_rfl) fun S => ?_
    let S' : Finset Nat.Primes := S.filter fun p => M < (p : ℕ)
    have hsum_eq : ∑ p ∈ S, g p = ∑ p ∈ S', c * (1 / ((p : ℕ) : ℝ)) := by
      dsimp only [S', g]
      rw [Finset.sum_filter]
    rw [hsum_eq]
    have hdisj : Set.PairwiseDisjoint (↑S' : Set Nat.Primes)
        (fun p => Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ)) := by
      intro p hp q hq hpq
      have hpM : M < (p : ℕ) := (Finset.mem_filter.mp hp).2
      have hqM : M < (q : ℕ) := (Finset.mem_filter.mp hq).2
      have hne : k p ≠ k q := fun h => hpq (hk_inj p q hpM hqM h)
      rw [Function.onFun, Set.disjoint_left]
      intro t htp htq
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : ((k p : ℕ) : ℝ) + 1 ≤ ((k q : ℕ) : ℝ) := by exact_mod_cast hlt
        linarith [htp.2, htq.1]
      · have hle : ((k q : ℕ) : ℝ) + 1 ≤ ((k p : ℕ) : ℝ) := by exact_mod_cast hgt
        linarith [htq.2, htp.1]
    have hsub : ∀ p ∈ S', Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ) ⊆ Set.Ioi (1 : ℝ) := by
      intro p hp t ht
      have h1 : (1 : ℝ) ≤ ((k p : ℕ) : ℝ) := by
        exact_mod_cast hk_pos p (Finset.mem_filter.mp hp).2
      exact lt_of_le_of_lt h1 ht.1
    have hterm_le : ∀ p ∈ S',
        c * (1 / ((p : ℕ) : ℝ)) ≤ ∫ t in Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ), f t := by
      intro p hp
      have hpM : M < (p : ℕ) := (Finset.mem_filter.mp hp).2
      have hvol : ∫ _t in Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ), c * (1 / ((p : ℕ) : ℝ)) =
          c * (1 / ((p : ℕ) : ℝ)) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioo, add_sub_cancel_left,
          ENNReal.toReal_ofReal zero_le_one, smul_eq_mul, one_mul]
      rw [← hvol]
      exact setIntegral_mono_on (integrableOn_const (by simp))
        (hf_int.mono_set (hsub p hp)) measurableSet_Ioo (hf_ge p hpM)
    calc
      ∑ p ∈ S', c * (1 / ((p : ℕ) : ℝ))
          ≤ ∑ p ∈ S', ∫ t in Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ), f t :=
        Finset.sum_le_sum hterm_le
      _ = ∫ t in ⋃ p ∈ S', Set.Ioo ((k p : ℕ) : ℝ) ((k p : ℕ) + 1 : ℝ), f t :=
        (integral_biUnion_finset S' (fun _ _ => measurableSet_Ioo) hdisj
          (fun p hp => hf_int.mono_set (hsub p hp))).symm
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), f t :=
        setIntegral_mono_set hf_int
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hf_nn t ht)
          (Eventually.of_forall (Set.iUnion₂_subset hsub))
  have hdiff_fin : (Function.support fun p : Nat.Primes =>
      (1 / ((p : ℕ) : ℝ)) - c⁻¹ * g p).Finite := by
    have hsub : Function.support (fun p : Nat.Primes => (1 / ((p : ℕ) : ℝ)) - c⁻¹ * g p) ⊆
        {p : Nat.Primes | (p : ℕ) ≤ M} := by
      intro p hp
      change (p : ℕ) ≤ M
      by_contra hle
      have hlt : M < (p : ℕ) := lt_of_not_ge hle
      have hgp : g p = c * (1 / ((p : ℕ) : ℝ)) := by
        dsimp only [g]
        simp only [hlt, ↓reduceIte]
      simp only [Function.mem_support, hgp, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul,
        sub_self, ne_eq, not_true_eq_false] at hp
    refine Set.Finite.subset ?_ hsub
    exact (Set.finite_Iic M).preimage Subtype.val_injective.injOn
  have hsum_diff : Summable (fun p : Nat.Primes => (1 / ((p : ℕ) : ℝ)) - c⁻¹ * g p) := by
    refine ⟨∑ p ∈ hdiff_fin.toFinset, ((1 / ((p : ℕ) : ℝ)) - c⁻¹ * g p),
      hasSum_sum_of_ne_finset_zero fun p hp => ?_⟩
    by_contra hne
    exact hp (hdiff_fin.mem_toFinset.mpr hne)
  have hsum_all : Summable (fun p : Nat.Primes => (1 / ((p : ℕ) : ℝ))) := by
    have h1 := (hg_sum.mul_left c⁻¹).add hsum_diff
    refine h1.congr fun p => ?_
    ring
  exact Nat.Primes.not_summable_one_div hsum_all

private lemma aPow_not_eventually_sign (r : ℕ) (hr : 1 ≤ r) (N : ℕ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hsign : ∀ n, N < n → 0 ≤ ε * aPow r n) : False := by
  let B : ℝ → ℝ := fun t => if N < ⌊t⌋₊ then ((ε * aPow r ⌊t⌋₊ : ℤ) : ℝ) else 0
  have hB_meas : Measurable B :=
    (measurable_of_countable (fun k : ℕ =>
      if N < k then ((ε * aPow r k : ℤ) : ℝ) else 0)).comp Nat.measurable_floor
  have hB_nn : ∀ t, 1 < t → 0 ≤ B t := by
    intro t _
    dsimp only [B]
    split_ifs with h
    · exact_mod_cast hsign ⌊t⌋₊ h
    · exact le_rfl
  have hB_le : ∀ t, 1 < t → B t ≤ t ^ (r + 1) := by
    intro t ht
    dsimp only [B]
    split_ifs with h
    · have hnn : 0 ≤ ((ε * aPow r ⌊t⌋₊ : ℤ) : ℝ) := by exact_mod_cast hsign ⌊t⌋₊ h
      have habs : |(ε : ℝ)| = 1 := by
        rcases hε with rfl | rfl <;> norm_num
      have h1 : ((ε * aPow r ⌊t⌋₊ : ℤ) : ℝ) ≤ (⌊t⌋₊ : ℝ) ^ (r + 1) := by
        calc
          ((ε * aPow r ⌊t⌋₊ : ℤ) : ℝ) = |((ε * aPow r ⌊t⌋₊ : ℤ) : ℝ)| := (abs_of_nonneg hnn).symm
          _ = |(ε : ℝ)| * |(aPow r ⌊t⌋₊ : ℝ)| := by rw [Int.cast_mul, abs_mul]
          _ = |(aPow r ⌊t⌋₊ : ℝ)| := by rw [habs, one_mul]
          _ ≤ (⌊t⌋₊ : ℝ) ^ (r + 1) := abs_aPow_le r ⌊t⌋₊
      have h2 : (⌊t⌋₊ : ℝ) ^ (r + 1) ≤ t ^ (r + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (zero_lt_one.trans ht).le) (r + 1)
      exact h1.trans h2
    · positivity
  let P : ℂ → ℂ := fun s =>
    ∫ t in Set.Ioi (1 : ℝ),
      (if ⌊t⌋₊ ≤ N then ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) else 0) * (t : ℂ) ^ (-(s + 1))
  let G : ℂ → ℂ := fun s => (ε : ℂ) * invZeta (s - (r : ℂ)) / s - P s
  let U : Set ℂ := {s : ℂ | s ≠ 0} ∩ {s : ℂ | s - (r : ℂ) ∈ zetaDomain}
  have hU_open : IsOpen U :=
    isOpen_ne.inter (isOpen_zetaDomain.preimage (continuous_id.sub continuous_const))
  have hU_sub : ∀ σ ∈ Set.Icc (r : ℝ) ((r : ℝ) + 2), (σ : ℂ) ∈ U := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · intro h0
      have hσ0 : σ = 0 := Complex.ofReal_injective h0
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith [hσ.1]
    · have hsub : (σ : ℂ) - (r : ℂ) = ((σ - (r : ℝ) : ℝ) : ℂ) := by push_cast; ring
      change (σ : ℂ) - (r : ℂ) ∈ zetaDomain
      rw [hsub]
      exact real_Icc_subset_zetaDomain (sub_nonneg.mpr hσ.1)
  have hG_diff : DifferentiableOn ℂ G U := by
    intro s hs
    have h1 : DifferentiableAt ℂ (fun z : ℂ => invZeta (z - (r : ℂ))) s :=
      (differentiableOn_invZeta.differentiableAt (isOpen_zetaDomain.mem_nhds hs.2)).comp s
        (differentiableAt_id.sub (differentiableAt_const _))
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (ε : ℂ) * invZeta (z - (r : ℂ)) / z) s :=
      (h1.const_mul (ε : ℂ)).div differentiableAt_id hs.1
    exact (h2.sub (differentiable_finite_part r N ε s)).differentiableWithinAt
  have hIb : IntegrableOn (fun t : ℝ => B t * t ^ (-((r : ℝ) + 2) - 1)) (Set.Ioi (1 : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine hdom.mono' ((hB_meas.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (mul_nonneg (hB_nn t ht) (Real.rpow_nonneg htpos.le _))]
    calc
      B t * t ^ (-((r : ℝ) + 2) - 1) ≤ t ^ (r + 1) * t ^ (-((r : ℝ) + 2) - 1) :=
        mul_le_mul_of_nonneg_right (hB_le t ht) (Real.rpow_nonneg htpos.le _)
      _ = t ^ ((r + 1 : ℕ) : ℝ) * t ^ (-((r : ℝ) + 2) - 1) := by rw [Real.rpow_natCast]
      _ = t ^ (-2 : ℝ) := by
        rw [← Real.rpow_add htpos]
        congr 1
        push_cast
        ring
  have hEq : ∀ s : ℂ, (r : ℝ) + 2 < s.re → G s = mellinDeriv B 0 s := by
    intro s hs
    have hs1 : (r + 1 : ℝ) < s.re := by linarith
    have hs_ne : s ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hs
      have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    obtain ⟨hLsum, hLeq⟩ := LSeries_moebius_mul_pow r hs1
    have hO : (fun n : ℕ =>
        ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ r) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ ((r + 1 : ℕ) : ℝ) := by
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
      have hcast : (∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ r) =
          ((aPow r n : ℤ) : ℂ) := by
        rw [aPow, Int.cast_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        rfl
      rw [hcast, Complex.norm_intCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
        Real.rpow_natCast, one_mul]
      exact abs_aPow_le r n
    have hMellin := LSeries_eq_mul_integral
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ r)
      (r := ((r + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _) (by push_cast; linarith) hLsum hO
    rw [hLeq] at hMellin
    have hInt_all : (ε : ℂ) * invZeta (s - (r : ℂ)) / s =
        ∫ t in Set.Ioi (1 : ℝ), ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [hMellin, mul_div_assoc, mul_div_cancel_left₀ _ hs_ne, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      have hcast : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ r) =
          ((aPow r ⌊t⌋₊ : ℤ) : ℂ) := by
        rw [aPow, Int.cast_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        rfl
      rw [hcast, Int.cast_mul, mul_assoc]
    have hInt_B : IntegrableOn (fun t : ℝ => (B t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
      have h1 := integrableOn_mellin_real hB_meas hB_nn hIb 0 hs
      refine h1.mono' (by
        simpa only [pow_zero, mul_one] using aestronglyMeasurable_mellin_integrand hB_meas 0 s) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hB_nn t ht),
        Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re, Complex.add_re, Complex.one_re,
        pow_zero, mul_one, show -(s.re + 1) = -s.re - 1 by ring]
    have hInt_P : IntegrableOn
        (fun t : ℝ =>
          (if ⌊t⌋₊ ≤ N then ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) else 0) * (t : ℂ) ^ (-(s + 1)))
        (Set.Ioi (1 : ℝ)) := by
      let cN : ℝ → ℂ := fun t => if ⌊t⌋₊ ≤ N then ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) else 0
      let C₀ : ℝ := |(ε : ℝ)| * (N : ℝ) ^ (r + 1) * ((N + 1 : ℕ) : ℝ) ^ (‖s‖ + 1)
      have hmeas : AEStronglyMeasurable (fun t : ℝ => cN t * (t : ℂ) ^ (-(s + 1)))
          (volume.restrict (Set.Ioi (1 : ℝ))) :=
        ((measurable_of_countable (fun k : ℕ =>
          if k ≤ N then ((ε * aPow r k : ℤ) : ℂ) else 0)).comp
            Nat.measurable_floor).aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow s)
      refine (integrableOn_indicator_Ioc N C₀).mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases hle : t ≤ ((N + 1 : ℕ) : ℝ)
      · have hmem : t ∈ Set.Ioc (1 : ℝ) ((N + 1 : ℕ) : ℝ) := ⟨ht, hle⟩
        rw [Set.indicator_of_mem hmem]
        have htpos : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re,
          Complex.add_re, Complex.one_re]
        have hre : -(s.re + 1) ≤ ‖s‖ + 1 := by
          have := Complex.abs_re_le_norm s
          linarith [neg_le_abs s.re]
        have hpow : t ^ (-(s.re + 1)) ≤ ((N + 1 : ℕ) : ℝ) ^ (‖s‖ + 1) :=
          (Real.rpow_le_rpow_of_exponent_le ht.le hre).trans
            (Real.rpow_le_rpow htpos.le hle (by positivity))
        have hcN_le : ‖cN t‖ ≤ |(ε : ℝ)| * (N : ℝ) ^ (r + 1) := by
          dsimp only [cN]
          split_ifs with h
          · rw [Int.cast_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
            exact mul_le_mul_of_nonneg_left
              ((abs_aPow_le r ⌊t⌋₊).trans
                (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr h) (r + 1)))
              (abs_nonneg _)
          · rw [norm_zero]
            positivity
        exact mul_le_mul hcN_le hpow (Real.rpow_nonneg htpos.le _) (by positivity)
      · have hgt : ((N + 1 : ℕ) : ℝ) < t := lt_of_not_ge hle
        have hfl : N + 1 ≤ ⌊t⌋₊ := Nat.le_floor hgt.le
        have hnot : ¬⌊t⌋₊ ≤ N := by omega
        rw [Set.indicator_of_notMem (fun h => hgt.not_ge h.2)]
        simp only [hnot, ↓reduceIte, zero_mul, norm_zero, le_rfl]
    have hsplit : (∫ t in Set.Ioi (1 : ℝ), ((ε * aPow r ⌊t⌋₊ : ℤ) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        mellinDeriv B 0 s + P s := by
      dsimp only [mellinDeriv, P]
      simp only [pow_zero, mul_one]
      rw [← integral_add hInt_B hInt_P]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      dsimp only [B]
      by_cases h : N < ⌊t⌋₊
      · have hnot : ¬⌊t⌋₊ ≤ N := by omega
        simp only [h, hnot, ↓reduceIte, Complex.ofReal_intCast, zero_mul, add_zero]
      · have hle : ⌊t⌋₊ ≤ N := by omega
        simp only [h, hle, ↓reduceIte, Complex.ofReal_zero, zero_mul, zero_add]
    dsimp only [G]
    rw [hInt_all, hsplit, add_sub_cancel_right]
  have hIr : IntegrableOn (fun t : ℝ => B t * t ^ (-(r : ℝ) - 1)) (Set.Ioi (1 : ℝ)) :=
    landau_theorem hB_meas hB_nn (by linarith : (r : ℝ) ≤ (r : ℝ) + 2) hU_open hU_sub hG_diff hIb
      hEq
  rcases hε with rfl | rfl
  · refine not_integrableOn_of_prime_intervals
      (f := fun t => B t * t ^ (-(r : ℝ) - 1))
      (fun t ht => mul_nonneg (hB_nn t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _))
      hIr (k := fun p => (p : ℕ) - 1) (M := N + 1) (c := 1) zero_lt_one
      (fun p q hp hq heq => Subtype.ext (by omega))
      (fun p hp => by omega) ?_
    intro p hp t ht
    have ht_pos : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg _) ht.1
    have hfl : ⌊t⌋₊ = (p : ℕ) - 1 := by
      rw [Nat.floor_eq_iff ht_pos.le]
      exact ⟨ht.1.le, ht.2⟩
    have hNlt : N < (p : ℕ) - 1 := by omega
    have ha_diff := aPow_succ r ((p : ℕ) - 1)
    have hp_sub : (p : ℕ) - 1 + 1 = (p : ℕ) := by omega
    rw [hp_sub, ArithmeticFunction.moebius_apply_prime p.prop] at ha_diff
    have hap_nn : 0 ≤ aPow r (p : ℕ) := by
      have := hsign (p : ℕ) (by omega)
      linarith
    have ha_ge : (((p : ℕ) : ℤ) ^ r) ≤ aPow r ((p : ℕ) - 1) := by linarith
    have hB_ge : ((p : ℕ) : ℝ) ^ r ≤ B t := by
      dsimp only [B]
      rw [hfl]
      simp only [hNlt, ↓reduceIte, one_mul]
      exact_mod_cast ha_ge
    have ht_le : t ≤ ((p : ℕ) : ℝ) := by
      have : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) := by exact_mod_cast hp_sub
      linarith [ht.2]
    have hpow_ge : ((p : ℕ) : ℝ) ^ (-(r : ℝ) - 1) ≤ t ^ (-(r : ℝ) - 1) :=
      Real.rpow_le_rpow_of_nonpos ht_pos ht_le (by linarith [Nat.cast_nonneg (α := ℝ) r])
    have hp_pos : (0 : ℝ) < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.prop.pos
    calc
      1 * (1 / ((p : ℕ) : ℝ)) = ((p : ℕ) : ℝ) ^ r * ((p : ℕ) : ℝ) ^ (-(r : ℝ) - 1) := by
        rw [one_mul, one_div, ← Real.rpow_natCast, ← Real.rpow_add hp_pos,
          show (r : ℝ) + (-(r : ℝ) - 1) = -1 by ring, Real.rpow_neg_one]
      _ ≤ B t * t ^ (-(r : ℝ) - 1) :=
        mul_le_mul hB_ge hpow_ge (Real.rpow_nonneg hp_pos.le _) (hB_nn t (by
          have : (1 : ℝ) ≤ (((p : ℕ) - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ (p : ℕ) - 1 by omega)
          linarith [ht.1]))
  · refine not_integrableOn_of_prime_intervals
      (f := fun t => B t * t ^ (-(r : ℝ) - 1))
      (fun t ht => mul_nonneg (hB_nn t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _))
      hIr (k := fun p => 2 * (p : ℕ) - 1) (M := max N 2) (c := 1 / 2) (by norm_num)
      (fun p q hp hq heq => Subtype.ext (by omega))
      (fun p hp => by omega) ?_
    intro p hp t ht
    have ht_pos : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg _) ht.1
    have hfl : ⌊t⌋₊ = 2 * (p : ℕ) - 1 := by
      rw [Nat.floor_eq_iff ht_pos.le]
      exact ⟨ht.1.le, ht.2⟩
    have hp_gt2 : 2 < (p : ℕ) := lt_of_le_of_lt (le_max_right N 2) hp
    have hcop : Nat.Coprime 2 (p : ℕ) :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr fun hdvd => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two p.prop).mp hdvd
        omega
    have hmu2p : ArithmeticFunction.moebius (2 * (p : ℕ)) = 1 := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two,
        ArithmeticFunction.moebius_apply_prime p.prop]
      norm_num
    have ha_diff := aPow_succ r (2 * (p : ℕ) - 1)
    have h2p_sub : 2 * (p : ℕ) - 1 + 1 = 2 * (p : ℕ) := by omega
    rw [h2p_sub, hmu2p, one_mul] at ha_diff
    have hpN : N < (p : ℕ) := lt_of_le_of_lt (le_max_left N 2) hp
    have ha2p_le : aPow r (2 * (p : ℕ)) ≤ 0 := by
      have := hsign (2 * (p : ℕ)) (by omega)
      linarith
    have ha_ge : ((2 * (p : ℕ) : ℕ) : ℤ) ^ r ≤ (-1 : ℤ) * aPow r (2 * (p : ℕ) - 1) := by linarith
    have hNlt : N < 2 * (p : ℕ) - 1 := by omega
    have hB_ge : ((2 * (p : ℕ) : ℕ) : ℝ) ^ r ≤ B t := by
      dsimp only [B]
      rw [hfl]
      simp only [hNlt, ↓reduceIte]
      exact_mod_cast ha_ge
    have ht_le : t ≤ ((2 * (p : ℕ) : ℕ) : ℝ) := by
      have : ((2 * (p : ℕ) - 1 : ℕ) : ℝ) + 1 = ((2 * (p : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast h2p_sub
      linarith [ht.2]
    have hpow_ge : ((2 * (p : ℕ) : ℕ) : ℝ) ^ (-(r : ℝ) - 1) ≤ t ^ (-(r : ℝ) - 1) :=
      Real.rpow_le_rpow_of_nonpos ht_pos ht_le (by linarith [Nat.cast_nonneg (α := ℝ) r])
    have h2p_pos : (0 : ℝ) < ((2 * (p : ℕ) : ℕ) : ℝ) := by positivity
    calc
      (1 / 2 : ℝ) * (1 / ((p : ℕ) : ℝ))
          = ((2 * (p : ℕ) : ℕ) : ℝ) ^ r * ((2 * (p : ℕ) : ℕ) : ℝ) ^ (-(r : ℝ) - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add h2p_pos,
          show (r : ℝ) + (-(r : ℝ) - 1) = -1 by ring, Real.rpow_neg_one, Nat.cast_mul,
          Nat.cast_ofNat]
        ring
      _ ≤ B t * t ^ (-(r : ℝ) - 1) :=
        mul_le_mul hB_ge hpow_ge (Real.rpow_nonneg h2p_pos.le _) (hB_nn t (by
          have : (1 : ℝ) ≤ ((2 * (p : ℕ) - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 1 ≤ 2 * (p : ℕ) - 1 by omega)
          linarith [ht.1]))

private theorem aPow_changes_sign (r : ℕ) (hr : 1 ≤ r) :
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ 0 < aPow r n) ∧
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ aPow r n < 0) := by
  constructor
  · intro N
    by_contra h
    exact aPow_not_eventually_sign r hr N (-1) (Or.inr rfl) fun n hn => by
      have hle : aPow r n ≤ 0 := not_lt.mp fun hpos => h ⟨n, hn, hpos⟩
      linarith
  · intro N
    by_contra h
    exact aPow_not_eventually_sign r hr N 1 (Or.inl rfl) fun n hn => by
      have hge : 0 ≤ aPow r n := not_lt.mp fun hneg => h ⟨n, hn, hneg⟩
      linarith

end OMA.S_oeis_a336277_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a336277.main :=
  OMA.S_oeis_a336277_Proof.aPow_changes_sign 3 (by omega)
