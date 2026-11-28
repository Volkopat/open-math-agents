import OMAStatements.S_oeis_a127974
import Mathlib

namespace A127974Proof

open Filter Topology MeasureTheory

private noncomputable def I (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ n

private lemma inv_one_add_cube_le (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    1 / (1 + x ^ 3) ^ n ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 : 1 + x ^ 2 ≤ 2 * (1 + x ^ 3) := by
    have h2 : 0 ≤ (x - 1 / 2) ^ 2 * (2 * x + 1) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hx3 : 1 ≤ 1 + x ^ 3 := by
    have : 0 ≤ x ^ 3 := pow_nonneg hx 3
    linarith
  have hpow : 1 + x ^ 3 ≤ (1 + x ^ 3) ^ n := le_self_pow₀ hx3 (by omega)
  have hle : 1 + x ^ 2 ≤ 2 * (1 + x ^ 3) ^ n := h1.trans (by linarith)
  rw [one_div, inv_le_iff_one_le_mul₀ (by positivity)]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  calc
    1 = (1 + x ^ 2) * (1 + x ^ 2)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
    _ ≤ (2 * (1 + x ^ 3) ^ n) * (1 + x ^ 2)⁻¹ := by gcongr
    _ = 2 * (1 + x ^ 2)⁻¹ * (1 + x ^ 3) ^ n := by ring

private lemma integrable_inv_one_add_cube_pow (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3) ^ n) (Set.Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) (Set.Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul 2).integrableOn
  refine hdom.mono' ?_ ?_
  · exact (continuousOn_const.div (by fun_prop) (fun x hx => by
      have : 0 < x := hx
      positivity)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.out.le
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_one_add_cube_le n hn hx0

private lemma I_one : I 1 = 2 * Real.pi / (3 * Real.sqrt 3) := by
  let s : ℝ := Real.sqrt 3
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let F : ℝ → ℝ := fun x =>
    (1 / 3) * Real.log (1 + x) - (1 / 6) * Real.log (x ^ 2 - x + 1) +
    (1 / s) * Real.arctan ((2 * x - 1) / s)
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt F (1 / (1 + x ^ 3)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have h1x : 0 < 1 + x := by linarith
    have hq : 0 < x ^ 2 - x + 1 := by
      have : 0 ≤ (x - 1 / 2) ^ 2 := sq_nonneg _
      linarith
    have d1 : HasDerivAt (fun t : ℝ => (1 / 3 : ℝ) * Real.log (1 + t))
        ((1 / 3 : ℝ) * (1 * (1 + x)⁻¹)) x := by
      have dl := ((hasDerivAt_id x).const_add 1).log h1x.ne'
      exact dl.const_mul (1 / 3 : ℝ)
    have d2 : HasDerivAt (fun t : ℝ => (1 / 6 : ℝ) * Real.log (t ^ 2 - t + 1))
        ((1 / 6) * ((2 * x - 1) / (x ^ 2 - x + 1))) x := by
      have dpoly : HasDerivAt (fun t : ℝ => t ^ 2 - t + 1) (2 * x - 1) x := by
        simpa using (((hasDerivAt_pow 2 x).sub (hasDerivAt_id x)).add_const 1)
      exact (dpoly.log hq.ne').const_mul (1 / 6 : ℝ)
    have d3 : HasDerivAt (fun t : ℝ => (1 / s) * Real.arctan ((2 * t - 1) / s))
        ((1 / s) * (1 / (1 + ((2 * x - 1) / s) ^ 2) * (2 / s))) x := by
      have dlin : HasDerivAt (fun t : ℝ => (2 * t - 1) / s) (2 / s) x := by
        simpa using ((((hasDerivAt_id x).const_mul 2).sub_const 1).div_const s)
      exact dlin.arctan.const_mul (1 / s)
    have hsum_eq : (1 / 3 : ℝ) * (1 * (1 + x)⁻¹) - (1 / 6) * ((2 * x - 1) / (x ^ 2 - x + 1)) +
        (1 / s) * (1 / (1 + ((2 * x - 1) / s) ^ 2) * (2 / s)) = 1 / (1 + x ^ 3) := by
      have h1x_ne : 1 + x ≠ 0 := h1x.ne'
      have hq_ne : x ^ 2 - x + 1 ≠ 0 := hq.ne'
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have h1x3 : 1 + x ^ 3 ≠ 0 := by positivity
      have hs_eq : 1 + ((2 * x - 1) / s) ^ 2 = 4 * (x ^ 2 - x + 1) / 3 := by
        field_simp
        rw [hs2]
        ring
      rw [hs_eq]
      have hsub1 : (1 / s) * (1 / (4 * (x ^ 2 - x + 1) / 3) * (2 / s)) =
          1 / (2 * (x ^ 2 - x + 1)) := by
        field_simp
        rw [hs2]
        ring
      rw [hsub1]
      have hsub2 : (1 / 3 : ℝ) * (1 * (1 + x)⁻¹) - (1 / 6) * ((2 * x - 1) / (x ^ 2 - x + 1)) +
          1 / (2 * (x ^ 2 - x + 1)) = 1 / (1 + x ^ 3) := by
        have hq_ne' : x * (x - 1) + 1 ≠ 0 := by linarith [hq]
        field_simp
        ring
      exact hsub2
    exact hsum_eq ▸ (d1.sub d2).add d3
  have hF0 : F 0 = -(Real.pi / (6 * s)) := by
    simp only [F]
    norm_num
    rw [neg_div, Real.arctan_neg, show (1 : ℝ) / s = s⁻¹ by simp [one_div],
      show s = Real.sqrt 3 from rfl, Real.arctan_inv_sqrt_three]
    ring
  have hlog_lim : Tendsto (fun x : ℝ => (1 / 3 : ℝ) * Real.log (1 + x) -
      (1 / 6) * Real.log (x ^ 2 - x + 1)) atTop (𝓝 0) := by
    have heq : ∀ᶠ x : ℝ in atTop,
        (1 / 3 : ℝ) * Real.log (1 + x) - (1 / 6) * Real.log (x ^ 2 - x + 1) =
        (1 / 6) * Real.log ((1 + x) ^ 2 / (x ^ 2 - x + 1)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have h1x : 0 < 1 + x := by linarith
      have hq : 0 < x ^ 2 - x + 1 := by nlinarith [sq_nonneg (x - 1 / 2)]
      rw [Real.log_div (by positivity) hq.ne', Real.log_pow]
      ring
    have hrat : Tendsto (fun x : ℝ => (1 + x) ^ 2 / (x ^ 2 - x + 1)) atTop (𝓝 1) := by
      have heq2 : ∀ᶠ x : ℝ in atTop,
          (1 + x) ^ 2 / (x ^ 2 - x + 1) = (1 + 2 / x + 1 / x ^ 2) / (1 - 1 / x + 1 / x ^ 2) := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        have hx0 : x ≠ 0 := hx.ne'
        field_simp
        ring
      rw [tendsto_congr' heq2]
      have h1 : Tendsto (fun x : ℝ => 1 + 2 / x + 1 / x ^ 2) atTop (𝓝 1) := by
        have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have h12 : Tendsto (fun x : ℝ => 1 + 2 * x⁻¹ + (x⁻¹) ^ 2) atTop (𝓝 1) := by
          simpa using (tendsto_const_nhds.add (hinv.const_mul 2)).add (hinv.pow 2)
        refine h12.congr fun x => ?_
        ring
      have h2 : Tendsto (fun x : ℝ => 1 - 1 / x + 1 / x ^ 2) atTop (𝓝 1) := by
        have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have h12 : Tendsto (fun x : ℝ => 1 - x⁻¹ + (x⁻¹) ^ 2) atTop (𝓝 1) := by
          simpa using (tendsto_const_nhds.sub hinv).add (hinv.pow 2)
        refine h12.congr fun x => ?_
        ring
      have hdiv : Tendsto (fun x : ℝ => (1 + 2 / x + 1 / x ^ 2) / (1 - 1 / x + 1 / x ^ 2))
          atTop (𝓝 (1 / 1)) := h1.div h2 (by norm_num)
      simpa using hdiv
    have hlog1 : Tendsto (fun x : ℝ => (1 / 6 : ℝ) * Real.log ((1 + x) ^ 2 / (x ^ 2 - x + 1)))
        atTop (𝓝 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hrat
      simpa [Real.log_one] using this.const_mul (1 / 6 : ℝ)
    exact hlog1.congr' (EventuallyEq.symm heq)
  have harc_lim : Tendsto (fun x : ℝ => (1 / s) * Real.arctan ((2 * x - 1) / s))
      atTop (𝓝 (Real.pi / (2 * s))) := by
    have hlin : Tendsto (fun x : ℝ => (2 * x - 1) / s) atTop atTop := by
      refine Tendsto.atTop_div_const hs_pos ?_
      have h2x : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
        tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      simpa [sub_eq_add_neg] using h2x.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    have ha := (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hlin
    rw [show Real.pi / (2 * s) = 1 / s * (Real.pi / 2) by ring]
    exact ha.const_mul (1 / s)
  have hF_lim : Tendsto F atTop (𝓝 (Real.pi / (2 * s))) := by
    simpa [F] using hlog_lim.add harc_lim
  have hint0 : IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3)) (Set.Ioi 0) := by
    simpa using integrable_inv_one_add_cube_pow 1 le_rfl
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint0 hF_lim
  rw [I, show (fun x : ℝ => 1 / (1 + x ^ 3) ^ 1) = (fun x => 1 / (1 + x ^ 3)) by ext; simp,
    hint, hF0]
  ring

private lemma I_succ (n : ℕ) (hn : 1 ≤ n) :
    I (n + 1) = ((3 * (n : ℝ) - 1) / (3 * (n : ℝ))) * I n := by
  let G : ℝ → ℝ := fun x => x / (1 + x ^ 3) ^ n
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt G ((1 - 3 * (n : ℝ)) / (1 + x ^ 3) ^ n +
        (3 * (n : ℝ)) / (1 + x ^ 3) ^ (n + 1)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have h1x : 0 < 1 + x ^ 3 := by positivity
    have dden : HasDerivAt (fun t : ℝ => (1 + t ^ 3) ^ n)
        ((n : ℝ) * (1 + x ^ 3) ^ (n - 1) * (3 * x ^ 2)) x := by
      have dbase : HasDerivAt (fun t : ℝ => 1 + t ^ 3) (3 * x ^ 2) x := by
        simpa using ((hasDerivAt_pow 3 x).const_add 1)
      exact dbase.pow n
    have dq : HasDerivAt G
        ((1 * (1 + x ^ 3) ^ n - x * ((n : ℝ) * (1 + x ^ 3) ^ (n - 1) * (3 * x ^ 2))) /
          ((1 + x ^ 3) ^ n) ^ 2) x := (hasDerivAt_id x).div dden (by positivity)
    convert dq using 1
    have hpow : (1 + x ^ 3) ^ n = (1 + x ^ 3) ^ (n - 1) * (1 + x ^ 3) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    have hpow1 : (1 + x ^ 3) ^ (n + 1) = (1 + x ^ 3) ^ n * (1 + x ^ 3) := pow_succ _ n
    rw [hpow1]
    have h1x_ne : 1 + x ^ 3 ≠ 0 := h1x.ne'
    have hpn : (1 + x ^ 3) ^ n ≠ 0 := by positivity
    have hpn1 : (1 + x ^ 3) ^ (n - 1) ≠ 0 := by positivity
    field_simp
    rw [hpow]
    ring
  have hG_lim : Tendsto G atTop (𝓝 0) := by
    have hle : ∀ᶠ x : ℝ in atTop, ‖G x‖ ≤ x / (1 + x ^ 3) := by
      filter_upwards [eventually_ge_atTop 0] with x hx
      have h1x : 1 ≤ 1 + x ^ 3 := by have : 0 ≤ x ^ 3 := pow_nonneg hx 3; linarith
      have hpow : 1 + x ^ 3 ≤ (1 + x ^ 3) ^ n := le_self_pow₀ h1x (by omega)
      simp only [G]
      rw [Real.norm_of_nonneg (div_nonneg hx (by positivity))]
      exact div_le_div_of_nonneg_left hx (by positivity) hpow
    have h0 : Tendsto (fun x : ℝ => x / (1 + x ^ 3)) atTop (𝓝 0) := by
      have heq : ∀ᶠ x : ℝ in atTop, x / (1 + x ^ 3) = (1 / x ^ 2) / (1 / x ^ 3 + 1) := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        have hx0 : x ≠ 0 := hx.ne'
        field_simp
      rw [tendsto_congr' heq]
      have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h2 : Tendsto (fun x : ℝ => (1 : ℝ) / x ^ 2) atTop (𝓝 0) := by
        simpa [one_div, inv_pow] using hinv.pow 2
      have h3 : Tendsto (fun x : ℝ => (1 : ℝ) / x ^ 3 + 1) atTop (𝓝 1) := by
        simpa [one_div, inv_pow] using (hinv.pow 3).add_const 1
      have hdiv : Tendsto (fun x : ℝ => ((1 : ℝ) / x ^ 2) / ((1 : ℝ) / x ^ 3 + 1))
          atTop (𝓝 (0 / 1)) := h2.div h3 (by norm_num)
      simpa using hdiv
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle h0)
  have hint1 := integrable_inv_one_add_cube_pow n hn
  have hint2 := integrable_inv_one_add_cube_pow (n + 1) (by omega)
  have hfun1 : (fun x : ℝ => (1 - 3 * (n : ℝ)) / (1 + x ^ 3) ^ n) =
      fun x => (1 - 3 * (n : ℝ)) * (1 / (1 + x ^ 3) ^ n) := by ext x; ring
  have hfun2 : (fun x : ℝ => (3 * (n : ℝ)) / (1 + x ^ 3) ^ (n + 1)) =
      fun x => (3 * (n : ℝ)) * (1 / (1 + x ^ 3) ^ (n + 1)) := by ext x; ring
  have hint1' : IntegrableOn (fun x : ℝ => (1 - 3 * (n : ℝ)) / (1 + x ^ 3) ^ n) (Set.Ioi 0) := by
    rw [hfun1]
    exact hint1.const_mul _
  have hint2' : IntegrableOn (fun x : ℝ => (3 * (n : ℝ)) / (1 + x ^ 3) ^ (n + 1)) (Set.Ioi 0) := by
    rw [hfun2]
    exact hint2.const_mul _
  have hint_sum := hint1'.add hint2'
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_sum hG_lim
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0, sub_zero] at hval
  have hsplit : ∫ x in Set.Ioi (0 : ℝ), ((1 - 3 * (n : ℝ)) / (1 + x ^ 3) ^ n +
      (3 * (n : ℝ)) / (1 + x ^ 3) ^ (n + 1)) =
      (1 - 3 * (n : ℝ)) * I n + (3 * (n : ℝ)) * I (n + 1) := by
    rw [integral_add hint1' hint2', hfun1, hfun2, integral_const_mul, integral_const_mul]
    rfl
  rw [hsplit] at hval
  have hn_pos : (0 : ℝ) < 3 * (n : ℝ) := by positivity
  field_simp
  linarith

private noncomputable def c (m : ℕ) : ℚ :=
  PowerSeries.coeff m OMA.S_oeis_a127974.series

private lemma c_zero : c 0 = 1 := by
  simp [c, OMA.S_oeis_a127974.series, PowerSeries.coeff_rescale]

private lemma c_succ (m : ℕ) :
    c (m + 1) = ((3 * (m : ℚ) + 2) / (3 * ((m : ℚ) + 1))) * c m := by
  have h1 : c (m + 1) = (-1 : ℚ) ^ (m + 1) * Ring.choose (-2 / 3 : ℚ) (m + 1) := by
    simp [c, OMA.S_oeis_a127974.series, PowerSeries.coeff_rescale]
  have h0 : c m = (-1 : ℚ) ^ m * Ring.choose (-2 / 3 : ℚ) m := by
    simp [c, OMA.S_oeis_a127974.series, PowerSeries.coeff_rescale]
  have hch : (((m + 1).factorial : ℕ) : ℚ) * Ring.choose (-2 / 3 : ℚ) (m + 1) =
      ((m.factorial : ℕ) : ℚ) * Ring.choose (-2 / 3 : ℚ) m * (-2 / 3 - m) := by
    have hsm1 := Ring.descPochhammer_eq_factorial_smul_choose (-2 / 3 : ℚ) (m + 1)
    have hsm0 := Ring.descPochhammer_eq_factorial_smul_choose (-2 / 3 : ℚ) m
    rw [nsmul_eq_mul] at hsm1 hsm0
    rw [← hsm1, descPochhammer_succ_right]
    simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
      ← Polynomial.C_eq_natCast, Polynomial.smeval_C, pow_one, pow_zero, zsmul_eq_mul,
      Int.cast_natCast, mul_one]
    rw [hsm0]
  have hfac : (((m + 1).factorial : ℕ) : ℚ) = ((m : ℚ) + 1) * ((m.factorial : ℕ) : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac] at hch
  have hf0 : ((m.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hch2 : ((m : ℚ) + 1) * Ring.choose (-2 / 3 : ℚ) (m + 1) =
      Ring.choose (-2 / 3 : ℚ) m * (-2 / 3 - m) := by
    apply mul_left_cancel₀ hf0
    linear_combination hch
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hch' : Ring.choose (-2 / 3 : ℚ) (m + 1) =
      ((-2 / 3 - m) / ((m : ℚ) + 1)) * Ring.choose (-2 / 3 : ℚ) m := by
    field_simp
    linarith [hch2]
  rw [h1, hch', h0, pow_succ]
  field_simp
  ring

private lemma I_eq_c (m : ℕ) :
    (1 / (2 * Real.sqrt 3 * Real.pi)) * I (m + 1) = ((c m / 9 : ℚ) : ℝ) := by
  induction m with
  | zero =>
    rw [zero_add, I_one, c_zero]
    have hs : Real.sqrt 3 ≠ 0 := by positivity
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  | succ m ih =>
    have hrec := I_succ (m + 1) (by omega)
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl, hrec, c_succ m]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    calc
      (1 / (2 * Real.sqrt 3 * Real.pi)) *
          (((3 * ((m + 1 : ℕ) : ℝ) - 1) / (3 * ((m + 1 : ℕ) : ℝ))) * I (m + 1))
          = ((3 * ((m + 1 : ℕ) : ℝ) - 1) / (3 * ((m + 1 : ℕ) : ℝ))) *
              ((1 / (2 * Real.sqrt 3 * Real.pi)) * I (m + 1)) := by ring
      _ = ((3 * ((m + 1 : ℕ) : ℝ) - 1) / (3 * ((m + 1 : ℕ) : ℝ))) *
            ((c m / 9 : ℚ) : ℝ) := by rw [ih]
      _ = ((((3 * (m : ℚ) + 2) / (3 * ((m : ℚ) + 1))) * c m / 9 : ℚ) : ℝ) := by
            push_cast
            ring

private lemma c_not_dvd_three (m : ℕ) : ¬ (3 : ℤ) ∣ (c m).num := by
  induction m with
  | zero =>
    rw [c_zero]
    norm_num
  | succ m ih =>
    have h := c_succ m
    have heq : (c (m + 1)).num * ((c m).den * (3 * ((m : ℤ) + 1))) =
        (c (m + 1)).den * (c m).num * (3 * (m : ℤ) + 2) := by
      have hq3 : ((c (m + 1)).num : ℚ) / (c (m + 1)).den =
          ((3 * (m : ℚ) + 2) / (3 * ((m : ℚ) + 1))) * (((c m).num : ℚ) / (c m).den) := by
        rw [Rat.num_div_den, Rat.num_div_den, h]
      have hd1 : ((c (m + 1)).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (c (m + 1)).den_nz
      have hd0 : ((c m).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (c m).den_nz
      have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
      field_simp at hq3
      have hq4 : (((c (m + 1)).num * ((c m).den * (3 * ((m : ℤ) + 1))) : ℤ) : ℚ) =
          (((c (m + 1)).den * (c m).num * (3 * (m : ℤ) + 2) : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast hq4
    intro hdvd
    have hdvd_rhs : (3 : ℤ) ∣ (c (m + 1)).den * (c m).num * (3 * (m : ℤ) + 2) := by
      rw [← heq]
      exact dvd_mul_of_dvd_left hdvd _
    have hp3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
    rcases hp3.dvd_or_dvd hdvd_rhs with h12 | h3
    · rcases hp3.dvd_or_dvd h12 with hden | hnum
      · have hcop : Nat.Coprime (c (m + 1)).num.natAbs (c (m + 1)).den := (c (m + 1)).reduced
        have hdvd1 : 3 ∣ (c (m + 1)).num.natAbs := Int.natCast_dvd.mp hdvd
        have hdvd2 : 3 ∣ (c (m + 1)).den := Int.natCast_dvd.mp hden
        have := Nat.dvd_gcd hdvd1 hdvd2
        rw [hcop] at this
        omega
      · exact ih hnum
    · omega

private lemma div_nine_num_eq (q : ℚ) (hq : ¬ (3 : ℤ) ∣ q.num) : (q / 9).num = q.num := by
  have hcop9 : Nat.Coprime q.num.natAbs 9 := by
    have hp3 : Nat.Prime 3 := by decide
    have hnd : ¬ 3 ∣ q.num.natAbs := fun h => hq (Int.natCast_dvd.mpr h)
    have hcop3 : Nat.Coprime q.num.natAbs 3 := ((hp3.coprime_iff_not_dvd).mpr hnd).symm
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact hcop3.pow_right 2
  have hcop : Nat.Coprime q.num.natAbs ((9 * (q.den : ℤ)).natAbs) := by
    have h9d : (9 * (q.den : ℤ)).natAbs = 9 * q.den := by omega
    rw [h9d]
    exact hcop9.mul_right q.reduced
  have hdiv : q / 9 = (q.num : ℚ) / ((9 * (q.den : ℤ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast
    ring
  rw [hdiv]
  exact Rat.num_div_eq_of_coprime (by positivity) hcop

end A127974Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a127974.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨A127974Proof.c m / 9, (A127974Proof.I_eq_c m).symm, ?_⟩
  simp only [Nat.add_sub_cancel]
  exact A127974Proof.div_nine_num_eq (A127974Proof.c m) (A127974Proof.c_not_dvd_three m)
