import OMAStatements.S_oeis_a060294

-- Problem: A060294: Cesaro means of |sin(k*m)| and |cos(k*m)| equal 2/pi
-- Upstream: statements/oeis-a060294.lean (declaration OMA.S_oeis_a060294.main)
-- Credit: @cgaray

open Filter Topology Real Complex MeasureTheory

namespace OMA_oeis_a060294

private instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private noncomputable def avg (m : ℤ) (f : C(AddCircle Real.pi, ℂ)) (n : ℕ) : ℂ :=
  (1 / (n : ℂ)) * ∑ k ∈ Finset.Icc 1 n, f (((k : ℝ) * (m : ℝ) : ℝ) : AddCircle Real.pi)

private lemma exp_two_I_mul_ne_one {j m : ℤ} (hj : j ≠ 0) (hm : m ≠ 0) :
    Complex.exp (2 * Complex.I * (j : ℂ) * (m : ℂ)) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  rcases h with ⟨r, hr⟩
  have h2I : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  have hmul : (j : ℂ) * (m : ℂ) = (r : ℂ) * (Real.pi : ℂ) := by
    apply mul_left_cancel₀ h2I
    calc (2 : ℂ) * Complex.I * ((j : ℂ) * (m : ℂ))
        = 2 * Complex.I * (j : ℂ) * (m : ℂ) := by ring
      _ = (r : ℂ) * (2 * Real.pi * Complex.I) := hr
      _ = (2 : ℂ) * Complex.I * ((r : ℂ) * (Real.pi : ℂ)) := by ring
  have hreal : ((j : ℝ) * (m : ℝ)) = (r : ℝ) * Real.pi := by
    have := congr_arg Complex.re hmul
    simpa using this
  rcases eq_or_ne r 0 with rfl | hr0
  · simp only [Int.cast_zero, zero_mul] at hreal
    have : (j : ℝ) = 0 ∨ (m : ℝ) = 0 := mul_eq_zero.mp hreal
    rcases this with h1 | h2
    · exact hj (Int.cast_eq_zero.mp h1)
    · exact hm (Int.cast_eq_zero.mp h2)
  · have hr_ne : (r : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hr0
    have hpi : Real.pi = ((j * m : ℚ) / (r : ℚ) : ℚ) := by
      push_cast
      field_simp [hr_ne]
      linarith
    exact irrational_pi ⟨(j * m : ℚ) / (r : ℚ), hpi.symm⟩

private lemma tendsto_avg_fourier {m : ℤ} (hm : m ≠ 0) (j : ℤ) :
    Tendsto (avg m (fourier (T := Real.pi) j)) atTop
      (𝓝 (fourierCoeff (T := Real.pi) (fourier (T := Real.pi) j) 0)) := by
  rw [fourierCoeff_fourier]
  rcases eq_or_ne j 0 with rfl | hj
  · simp only [Pi.single_eq_same]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [avg, fourier_zero, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
      nsmul_eq_mul, mul_one]
    field_simp [hn_ne]
  · simp only [Pi.single_eq_of_ne (Ne.symm hj)]
    set z : ℂ := Complex.exp (2 * Complex.I * (j : ℂ) * (m : ℂ))
    have hz1 : z ≠ 1 := exp_two_I_mul_ne_one hj hm
    have hz_norm : ‖z‖ = 1 := by
      have harg : (2 * Complex.I * (j : ℂ) * (m : ℂ)) = (((2 * (j : ℝ) * (m : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [show z = Complex.exp (2 * Complex.I * (j : ℂ) * (m : ℂ)) from rfl, harg]
      exact Complex.norm_exp_ofReal_mul_I _
    have hsum : ∀ n : ℕ, 1 ≤ n →
        ∑ k ∈ Finset.Icc 1 n, fourier (T := Real.pi) j (((k : ℝ) * (m : ℝ) : ℝ) : AddCircle Real.pi) =
        z * ((z ^ n - 1) / (z - 1)) := by
      intro n _
      have hterm : ∀ k : ℕ,
          fourier (T := Real.pi) j (((k : ℝ) * (m : ℝ) : ℝ) : AddCircle Real.pi) = z ^ k := by
        intro k
        rw [fourier_coe_apply, ← Complex.exp_nat_mul]
        congr 1
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        push_cast
        field_simp [hpi]
      simp_rw [hterm]
      have hshift : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, z ^ k = ∑ k ∈ Finset.range m, z ^ (k + 1) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      rw [hshift n]
      simp_rw [pow_succ']
      rw [← Finset.mul_sum, geom_sum_eq hz1]
    have hbound : Tendsto (fun n : ℕ => (2 / ‖z - 1‖) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [avg, hsum n hn, norm_mul, norm_mul, one_div, norm_inv, Complex.norm_natCast,
      hz_norm, one_mul, norm_div]
    have hnum : ‖z ^ n - 1‖ ≤ 2 := by
      calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖z‖ ^ n + 1 := by rw [norm_pow, norm_one]
        _ = 2 := by rw [hz_norm, one_pow]; norm_num
    have hden_pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [div_eq_mul_inv, inv_mul_eq_div, div_le_div_iff_of_pos_right hn_pos]
    exact div_le_div_of_nonneg_right hnum hden_pos.le

private lemma tendsto_avg_span {m : ℤ} (hm : m ≠ 0)
    {f : C(AddCircle Real.pi, ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := Real.pi)))) :
    Tendsto (avg m f) atTop (𝓝 (fourierCoeff (T := Real.pi) f 0)) := by
  refine Submodule.span_induction (p := fun g _ => Tendsto (avg m g) atTop (𝓝 (fourierCoeff (T := Real.pi) g 0)))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨j, rfl⟩
    exact tendsto_avg_fourier hm j
  · have havg : avg m 0 = fun _ => 0 := by ext n; simp [avg]
    have hfc : fourierCoeff (T := Real.pi) (0 : C(AddCircle Real.pi, ℂ)) 0 = 0 := by
      simp [fourierCoeff]
    rw [havg, hfc]
    exact tendsto_const_nhds
  · intro f₁ f₂ _ _ hf₁ hf₂
    have havg : avg m (f₁ + f₂) = fun n => avg m f₁ n + avg m f₂ n := by
      ext n
      simp only [avg, ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
    have hfc : fourierCoeff (T := Real.pi) (f₁ + f₂) 0 =
        fourierCoeff (T := Real.pi) f₁ 0 + fourierCoeff (T := Real.pi) f₂ 0 := by
      have hi1 : Integrable f₁ AddCircle.haarAddCircle :=
        f₁.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hi2 : Integrable f₂ AddCircle.haarAddCircle :=
        f₂.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      exact congr_fun (fourierCoeff.add hi1 hi2) 0
    rw [havg, hfc]
    exact hf₁.add hf₂
  · intro c f₁ _ hf₁
    have havg : avg m (c • f₁) = fun n => c * avg m f₁ n := by
      ext n
      simp only [avg, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    have hfc : fourierCoeff (T := Real.pi) (c • f₁) 0 =
        c * fourierCoeff (T := Real.pi) f₁ 0 := by
      simpa [smul_eq_mul] using fourierCoeff.const_smul (T := Real.pi) f₁ c 0
    rw [havg, hfc]
    exact hf₁.const_mul c

private lemma norm_avg_sub_le (m : ℤ) (f g : C(AddCircle Real.pi, ℂ)) {n : ℕ} (hn : 1 ≤ n) :
    ‖avg m f n - avg m g n‖ ≤ ‖f - g‖ := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsub : avg m f n - avg m g n =
      (1 / (n : ℂ)) * ∑ k ∈ Finset.Icc 1 n, (f - g) (((k : ℝ) * (m : ℝ) : ℝ) : AddCircle Real.pi) := by
    simp only [avg, ContinuousMap.sub_apply, Finset.sum_sub_distrib, mul_sub]
  rw [hsub, norm_mul, one_div, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.Icc 1 n, (f - g) (((k : ℝ) * (m : ℝ) : ℝ) : AddCircle Real.pi)‖
      ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, ‖(f - g) (((k : ℝ) * (m : ℝ) : ℝ) : AddCircle Real.pi)‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _k ∈ Finset.Icc 1 n, ‖f - g‖ := by
        gcongr with k _; exact ContinuousMap.norm_coe_le_norm (f - g) _
    _ = ‖f - g‖ := by
        simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
        field_simp [ne_of_gt hn_pos]

private lemma norm_fourierCoeff_zero_sub_le (f g : C(AddCircle Real.pi, ℂ)) :
    ‖fourierCoeff (T := Real.pi) f 0 - fourierCoeff (T := Real.pi) g 0‖ ≤ ‖f - g‖ := by
  have hsub : fourierCoeff (T := Real.pi) f 0 - fourierCoeff (T := Real.pi) g 0 =
      ∫ t : AddCircle Real.pi, (f - g) t ∂AddCircle.haarAddCircle := by
    simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, ContinuousMap.sub_apply]
    have hi1 : Integrable f AddCircle.haarAddCircle :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable g AddCircle.haarAddCircle :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hi1 hi2]
  rw [hsub]
  calc ‖∫ t : AddCircle Real.pi, (f - g) t ∂AddCircle.haarAddCircle‖
      ≤ ∫ t : AddCircle Real.pi, ‖(f - g) t‖ ∂AddCircle.haarAddCircle :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _t : AddCircle Real.pi, ‖f - g‖ ∂AddCircle.haarAddCircle := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          (integrable_const _) (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm (f - g) t)
    _ = ‖f - g‖ := by simp

lemma tendsto_avg_continuous {m : ℤ} (hm : m ≠ 0) (f : C(AddCircle Real.pi, ℂ)) :
    Tendsto (avg m f) atTop (𝓝 (fourierCoeff (T := Real.pi) f 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdense : f ∈ closure (Submodule.span ℂ (Set.range (fourier (T := Real.pi))) :
      Set C(AddCircle Real.pi, ℂ)) := by
    change f ∈ (Submodule.span ℂ (Set.range (fourier (T := Real.pi)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨g, hg_mem, hfg⟩ := Metric.mem_closure_iff.mp hdense (ε / 3) (by linarith)
  rw [dist_eq_norm] at hfg
  have hg_lim := Metric.tendsto_atTop.mp (tendsto_avg_span hm hg_mem) (ε / 3) (by linarith)
  obtain ⟨N, hN⟩ := hg_lim
  refine ⟨max N 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have h1 : ‖avg m f n - avg m g n‖ ≤ ‖f - g‖ := norm_avg_sub_le m f g (le_trans (le_max_right _ _) hn)
  have h2 : ‖avg m g n - fourierCoeff (T := Real.pi) g 0‖ < ε / 3 := by
    simpa [dist_eq_norm] using hN n (le_trans (le_max_left _ _) hn)
  have h3 : ‖fourierCoeff (T := Real.pi) g 0 - fourierCoeff (T := Real.pi) f 0‖ ≤ ‖f - g‖ := by
    rw [norm_sub_rev]
    exact norm_fourierCoeff_zero_sub_le f g
  have htri : ‖avg m f n - fourierCoeff (T := Real.pi) f 0‖ ≤
      ‖avg m f n - avg m g n‖ + ‖avg m g n - fourierCoeff (T := Real.pi) g 0‖ +
      ‖fourierCoeff (T := Real.pi) g 0 - fourierCoeff (T := Real.pi) f 0‖ := by
    calc ‖avg m f n - fourierCoeff (T := Real.pi) f 0‖
        = ‖(avg m f n - avg m g n) + (avg m g n - fourierCoeff (T := Real.pi) g 0) +
            (fourierCoeff (T := Real.pi) g 0 - fourierCoeff (T := Real.pi) f 0)‖ := by
          congr 1; ring
      _ ≤ ‖(avg m f n - avg m g n) + (avg m g n - fourierCoeff (T := Real.pi) g 0)‖ +
            ‖fourierCoeff (T := Real.pi) g 0 - fourierCoeff (T := Real.pi) f 0‖ := norm_add_le _ _
      _ ≤ ‖avg m f n - avg m g n‖ + ‖avg m g n - fourierCoeff (T := Real.pi) g 0‖ +
            ‖fourierCoeff (T := Real.pi) g 0 - fourierCoeff (T := Real.pi) f 0‖ := by
          gcongr; exact norm_add_le _ _
  linarith

private noncomputable def liftPi (f : ℝ → ℂ) (hper : Function.Periodic f Real.pi)
    (hcont : Continuous f) : C(AddCircle Real.pi, ℂ) :=
  ⟨Quotient.lift f (fun x y h => by
    have h' : -x + y ∈ AddSubgroup.zmultiples Real.pi := QuotientAddGroup.leftRel_apply.mp h
    rw [AddSubgroup.mem_zmultiples_iff] at h'
    rcases h' with ⟨k, hk⟩
    have hyx : y = x + k * Real.pi := by
      have : (k : ℝ) * Real.pi = -x + y := by simpa [zsmul_eq_mul] using hk
      linarith
    rw [hyx]
    exact (hper.int_mul k x).symm),
   continuous_quot_lift _ hcont⟩

private lemma liftPi_coe (f : ℝ → ℂ) (hper : Function.Periodic f Real.pi)
    (hcont : Continuous f) (x : ℝ) :
    liftPi f hper hcont (x : AddCircle Real.pi) = f x := rfl

lemma tendsto_cesaro_periodic {m : ℤ} (hm : m ≠ 0) (f : ℝ → ℝ)
    (hper : Function.Periodic f Real.pi) (hcont : Continuous f) :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) * (m : ℝ)))
      atTop (𝓝 ((1 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi, f x)) := by
  let g : C(AddCircle Real.pi, ℂ) :=
    liftPi (fun x => (f x : ℂ)) (fun x => by simp [hper x]) (Complex.continuous_ofReal.comp hcont)
  have hg_coe : ∀ x : ℝ, g (x : AddCircle Real.pi) = (f x : ℂ) := fun _ => rfl
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_avg_continuous hm g)
  have hfc : (fourierCoeff (T := Real.pi) g 0).re = (1 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi, f x := by
    rw [fourierCoeff_eq_intervalIntegral g 0 0]
    simp only [neg_zero, fourier_zero, one_smul, zero_add]
    simp_rw [hg_coe]
    rw [intervalIntegral.integral_ofReal]
    simp [Complex.real_smul]
  rw [hfc] at hlim
  refine hlim.congr (fun n => ?_)
  simp only [Function.comp_apply, avg]
  simp_rw [hg_coe]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]

end OMA_oeis_a060294

theorem OMA.solution : type_of% @OMA.S_oeis_a060294.main := by
  intro m hm
  constructor
  · have hlim := OMA_oeis_a060294.tendsto_cesaro_periodic hm (fun x => |Real.sin x|)
      (fun x => by simp [Real.sin_add_pi]) (continuous_abs.comp Real.continuous_sin)
    have hint : (1 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi, |Real.sin x| = 2 / Real.pi := by
      have heq : ∫ x in (0 : ℝ)..Real.pi, |Real.sin x| = ∫ x in (0 : ℝ)..Real.pi, Real.sin x := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le Real.pi_pos.le] at hx
        exact abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hx)
      rw [heq, integral_sin, Real.cos_zero, Real.cos_pi]
      ring
    rwa [hint] at hlim
  · have hlim := OMA_oeis_a060294.tendsto_cesaro_periodic hm (fun x => |Real.cos x|)
      (fun x => by simp [Real.cos_add_pi]) (continuous_abs.comp Real.continuous_cos)
    have hint : (1 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi, |Real.cos x| = 2 / Real.pi := by
      have hcont : Continuous (fun x : ℝ => |Real.cos x|) := continuous_abs.comp Real.continuous_cos
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hcont.intervalIntegrable 0 (Real.pi / 2))
        (hcont.intervalIntegrable (Real.pi / 2) Real.pi)
      have h1 : ∫ x in (0 : ℝ)..(Real.pi / 2), |Real.cos x| =
          ∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
        exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
      have h2 : ∫ x in (Real.pi / 2)..Real.pi, |Real.cos x| =
          ∫ x in (Real.pi / 2)..Real.pi, -Real.cos x := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
        have hle : Real.cos x ≤ 0 := by
          have : Real.cos x = -Real.sin (x - Real.pi / 2) := by
            rw [Real.sin_sub_pi_div_two]; ring
          rw [this]
          have hsin : 0 ≤ Real.sin (x - Real.pi / 2) :=
            Real.sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
          linarith
        exact abs_of_nonpos hle
      rw [← hsplit, h1, h2, intervalIntegral.integral_neg, integral_cos, integral_cos,
        Real.sin_zero, Real.sin_pi_div_two, Real.sin_pi]
      ring
    rwa [hint] at hlim
