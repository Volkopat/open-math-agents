import OMAReductions.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1

-- Step DensityHypothesis.density_hypothesis_zeta_zeros.R1.H2: hypothesis H2 of reduction DensityHypothesis.density_hypothesis_zeta_zeros.R1
-- Credit: @senamakel
-- H2 := ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →     (Complex.zeroCountOn riemannZeta       {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ) ≤ C * T * Real.log T  /-- Under RH, zeta has no zero with real part above 1/2 off the real axis. -/

/-! # N(T) = O(T log T) for the zeros of zeta in the critical strip

Riemann xi, written as s (s - 1) Lambda_0(s) + 1, is entire with xi(0) = 1, and its growth is
at most exp(C |s| log |s|): the Mellin integrand of the theta kernel is bounded by a factorial.
Jensen's formula on the discs of radius r and 2r around 0 then bounds the zeros of xi in
|s| <= r by A r log r. Away from the trivial zeros, zeta and xi vanish to the same order, and
the strip 0 <= Re s <= 1, 0 < Im s <= T lies in the disc of radius T + 1. -/

namespace OMA.DH2
section

open Real

def LogGrowth (F : ℂ → ℂ) : Prop :=
  ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))

lemma one_le_log_of_three_le {u : ℝ} (hu : 3 ≤ u) : 1 ≤ log u := by
  have h3 : exp 1 < 3 := lt_of_lt_of_le exp_one_lt_d9 (by norm_num)
  rw [le_log_iff_exp_le (by linarith)]
  linarith

lemma ulogu_mono {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u * log u ≤ v * log v :=
  mul_le_mul huv (log_le_log (by linarith) huv) (log_nonneg hu) (by linarith)

lemma expo_mono {a a' b b' y y' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 3 ≤ b) (hy : 0 ≤ y)
    (hle : y + b ≤ y' + b') :
    a * ((y + b) * log (y + b)) ≤ a' * ((y' + b') * log (y' + b')) := by
  have h1 : 1 ≤ log (y + b) := one_le_log_of_three_le (by linarith)
  have h2 : (y + b) * log (y + b) ≤ (y' + b') * log (y' + b') :=
    ulogu_mono (by linarith) hle
  have h3 : 0 ≤ (y' + b') * log (y' + b') := by nlinarith
  exact mul_le_mul haa h2 (by nlinarith) (ha.trans haa)

lemma LogGrowth.nonneg_K {F : ℂ → ℂ} {K a b : ℝ}
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) : 0 ≤ K :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h 0)) (exp_pos _)

lemma LogGrowth.mono {F : ℂ → ℂ} {K a b : ℝ} (ha : 0 ≤ a) (hb : 3 ≤ b)
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) {a' b' : ℝ} (haa : a ≤ a')
    (hbb : b ≤ b') : ∀ s, ‖F s‖ ≤ K * exp (a' * ((‖s‖ + b') * log (‖s‖ + b'))) := by
  intro s
  refine (h s).trans (mul_le_mul_of_nonneg_left ?_ (LogGrowth.nonneg_K h))
  exact exp_le_exp.2 (expo_mono ha haa hb (norm_nonneg _) (by linarith))

lemma LogGrowth.congr {F G : ℂ → ℂ} (hF : LogGrowth F) (h : ∀ s, F s = G s) : LogGrowth G := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  exact ⟨K, a, b, ha, hb, fun s => h s ▸ hK s⟩

lemma LogGrowth.const (c : ℂ) : LogGrowth (fun _ => c) :=
  ⟨‖c‖, 0, 3, le_rfl, le_rfl, fun s => by simp⟩

lemma LogGrowth.add {F G : ℂ → ℂ} (hF : LogGrowth F) (hG : LogGrowth G) :
    LogGrowth (fun s => F s + G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K + K', max a a', max b b', le_max_of_le_left ha, le_max_of_le_left hb, fun s => ?_⟩
  have h1 := LogGrowth.mono ha hb hK (le_max_left a a') (le_max_left b b') s
  have h2 := LogGrowth.mono ha' hb' hK' (le_max_right a a') (le_max_right b b') s
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2

lemma LogGrowth.mul {F G : ℂ → ℂ} (hF : LogGrowth F) (hG : LogGrowth G) :
    LogGrowth (fun s => F s * G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K * K', a + a', max b b', add_nonneg ha ha', le_max_of_le_left hb, fun s => ?_⟩
  have h1 := LogGrowth.mono ha hb hK le_rfl (le_max_left b b') s
  have h2 := LogGrowth.mono ha' hb' hK' le_rfl (le_max_right b b') s
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ _ := mul_le_mul h1 h2 (norm_nonneg _)
        (mul_nonneg (LogGrowth.nonneg_K hK) (exp_pos _).le)
    _ = _ := by rw [add_mul a a', exp_add]; ring

lemma LogGrowth.comp {F : ℂ → ℂ} (hF : LogGrowth F) {g : ℂ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ s, ‖g s‖ ≤ ‖s‖ + d) : LogGrowth (fun s => F (g s)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  refine ⟨K, a, b + d, ha, by linarith, fun s => (hK (g s)).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (LogGrowth.nonneg_K hK)
  exact expo_mono ha le_rfl hb (norm_nonneg _) (by linarith [hg s])

end
section

open Real Set MeasureTheory
open scoped Nat

lemma exp_neg_le_factorial_mul {y : ℝ} (hy : 0 < y) (m : ℕ) : exp (-y) ≤ m ! * y⁻¹ ^ m := by
  have h := pow_div_factorial_le_exp (x := y) (hx := hy.le) (n := m)
  have hpos : 0 < y ^ m / m ! := by positivity
  rw [exp_neg]
  calc (exp y)⁻¹ ≤ (y ^ m / m !)⁻¹ := inv_anti₀ hpos h
    _ = m ! * y⁻¹ ^ m := by rw [inv_div, inv_pow, div_eq_mul_inv]

noncomputable def domFun : ℝ → ℝ :=
  (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))

lemma integrableOn_domFun : IntegrableOn domFun (Ioi 0) := by
  have h1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have h2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).integrable_indicator measurableSet_Ioi
  exact (h1.add h2).integrableOn

lemma integrand_bound (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * domFun t := by
  have hsre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk := P.hk
  have hA : 0 ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by positivity
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  · -- `0 < t < 1`: use the functional equation
    have hdom : domFun t = 1 := by
      simp [domFun, indicator, ht, h1.le, not_lt.2 h1.le]
    rw [hdom, mul_one]
    have hfm : P.f_modif t = (P.ε * ((1 / t) ^ P.k : ℝ)) • (P.g (1 / t) - P.g₀) := by
      have hfe := P.h_feq (1 / t) (by simpa using ht)
      rw [one_div_one_div] at hfe
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator, mem_Ioi, mem_Ioo, ht, h1,
        and_self, ite_true, not_lt.2 h1.le, ite_false, zero_add, hfe, smul_sub]
      congr 2
      rw [one_div, inv_rpow ht.le, rpow_neg ht.le]
    have h1t : 1 < 1 / t := by rw [lt_one_div one_pos ht, div_one]; exact h1
    rw [hfm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hgb := hg (1 / t) h1t
    have he := exp_neg_le_factorial_mul (show 0 < p * (1 / t) by positivity) m
    rw [neg_mul] at hgb
    have hcalc : t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m) ≤ 1 := by
      rw [one_div, inv_inv, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_natCast,
        ← rpow_add ht, ← rpow_add ht]
      apply rpow_le_one ht.le h1.le
      have := neg_abs_le s.re
      linarith
    calc t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖)
        ≤ t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * (C * (m ! * (p * (1 / t))⁻¹ ^ m))) := by
          gcongr
          exact hgb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * ‖P.ε‖ * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m)) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * ‖P.ε‖ * m ! * p⁻¹ ^ m * 1 := by gcongr
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by
          rw [mul_one]; gcongr; exact le_max_right _ _
  · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hA (by simp [domFun])
  · -- `t > 1`
    have hdom : domFun t = t ^ (-2 : ℝ) := by
      simp [domFun, indicator, h1, not_le.2 h1]
    rw [hdom]
    have hfm : P.f_modif t = P.f t - P.f₀ := by
      simp [WeakFEPair.f_modif, indicator, h1, not_lt.2 h1.le]
    rw [hfm]
    have he := exp_neg_le_factorial_mul (show 0 < p * t by positivity) m
    have hfb := hf t h1
    rw [neg_mul] at hfb
    have ht0 : 0 < t := ht
    have hcalc : t ^ (s.re - 1) * t⁻¹ ^ m ≤ t ^ (-2 : ℝ) := by
      rw [inv_pow, ← rpow_natCast, ← rpow_neg ht.le, ← rpow_add ht]
      apply rpow_le_rpow_of_exponent_le h1.le
      have := le_abs_self s.re
      linarith
    calc t ^ (s.re - 1) * ‖P.f t - P.f₀‖
        ≤ t ^ (s.re - 1) * (C * (m ! * (p * t)⁻¹ ^ m)) := by
          gcongr
          exact hfb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * 1 * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * t⁻¹ ^ m) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * t ^ (-2 : ℝ) := by
          gcongr
          exact le_max_left _ _

lemma Λ₀_bound (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) :
    ‖P.Λ₀ s‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ∫ t in Ioi 0, domFun t := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (integrableOn_domFun.const_mul _) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => integrand_bound P hp hC hf hg s m hm t ht)

theorem Λ₀_logGrowth (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) : LogGrowth P.Λ₀ := by
  set I0 := ∫ t in Ioi 0, domFun t
  set Q := max 1 p⁻¹
  have hQ : 1 ≤ Q := le_max_left _ _
  have hk := P.hk
  set b := P.k + 5
  refine ⟨C * max 1 ‖P.ε‖ * I0, 1 + log Q, b, by linarith [log_nonneg hQ], by linarith,
    fun s => ?_⟩
  set m := ⌈‖s‖ + P.k + 1⌉₊
  have hm : ‖s‖ + P.k + 1 ≤ m := Nat.le_ceil _
  have hm' : (m : ℝ) ≤ ‖s‖ + b := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖s‖ + P.k + 1 by positivity)
    linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith [norm_nonneg s]
  have hI0 : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun t _ => by
    simp only [domFun, Pi.add_apply]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _) _))
  refine (Λ₀_bound P hp hC hf hg s m hm).trans ?_
  have hfac : (m ! : ℝ) * p⁻¹ ^ m ≤ exp ((1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b))) := by
    have h1 : (m ! : ℝ) * p⁻¹ ^ m ≤ ((m : ℝ) * Q) ^ m := by
      rw [mul_pow]
      gcongr
      · exact_mod_cast Nat.factorial_le_pow m
      · exact le_max_right _ _
    have h2 : ((m : ℝ) * Q) ^ m = exp (m * log (m * Q)) := by
      rw [← log_pow, exp_log (by positivity)]
    have hL : 1 ≤ log (‖s‖ + b) := one_le_log_of_three_le (by linarith [norm_nonneg s])
    have hlogQ : 0 ≤ log Q := log_nonneg hQ
    have h3 : (m : ℝ) * log (m * Q) ≤ (1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b)) := by
      rw [log_mul (by positivity) (by positivity)]
      have e1 : (m : ℝ) * log m ≤ (‖s‖ + b) * log (‖s‖ + b) := ulogu_mono hm1 hm'
      have e2 : (m : ℝ) * log Q ≤ (‖s‖ + b) * log (‖s‖ + b) * log Q := by
        have : (m : ℝ) ≤ (‖s‖ + b) * log (‖s‖ + b) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlogQ
      nlinarith
    rw [h2] at h1
    exact h1.trans (exp_le_exp.2 h3)
  have hE : 0 ≤ C * max 1 ‖P.ε‖ := by positivity
  calc C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * I0 = C * max 1 ‖P.ε‖ * I0 * (m ! * p⁻¹ ^ m) := by ring
    _ ≤ _ := by gcongr

end

section

open Real Set Filter Asymptotics HurwitzZeta

lemma exp_bound_of_isBigO {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (h : F =O[atTop] fun x => exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 < t → |F t| ≤ C * exp (-p * t) := by
  obtain ⟨c, hc'⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc'
  set T' := max T 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T')).exists_bound_of_continuousOn
    (hc.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
  refine ⟨max (max c 0) (max M 0 * exp (p * T')), by positivity, fun t ht => ?_⟩
  rcases le_total T' t with h1 | h1
  · have := hT t ((le_max_left _ _).trans h1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have h2 := hM t ⟨ht.le, h1⟩
    rw [Real.norm_eq_abs] at h2
    calc |F t| ≤ max M 0 := h2.trans (le_max_left _ _)
      _ ≤ max M 0 * (exp (p * T') * exp (-p * t)) := by
          refine le_mul_of_one_le_right (le_max_right _ _) ?_
          rw [← exp_add, one_le_exp_iff]
          nlinarith
      _ = (max M 0 * exp (p * T')) * exp (-p * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le

lemma combine_bounds {f g : ℝ → ℝ} {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hf : ∀ t, 1 < t → f t ≤ C₁ * exp (-p₁ * t)) (hg : ∀ t, 1 < t → g t ≤ C₂ * exp (-p₂ * t)) :
    ∃ p C, 0 < p ∧ 0 ≤ C ∧ (∀ t, 1 < t → f t ≤ C * exp (-p * t)) ∧
      (∀ t, 1 < t → g t ≤ C * exp (-p * t)) := by
  refine ⟨min p₁ p₂, max C₁ C₂, lt_min hp₁ hp₂, le_max_of_le_left hC₁, fun t ht => ?_,
    fun t ht => ?_⟩
  · refine (hf t ht).trans (mul_le_mul (le_max_left _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_left p₁ p₂]
  · refine (hg t ht).trans (mul_le_mul (le_max_right _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_right p₁ p₂]

lemma even_logGrowth (a : UnitAddCircle) : LogGrowth (hurwitzEvenFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C₁, hC₁, hb₁⟩ := exp_bound_of_isBigO
    ((continuousOn_evenKernel a).sub continuousOn_const) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := exp_bound_of_isBigO
    ((continuousOn_cosKernel a).sub continuousOn_const) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := combine_bounds hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine Λ₀_logGrowth _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · have : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀ =
        ((evenKernel a t - if a = 0 then 1 else 0 : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hf t ht
  · have : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀ =
        ((cosKernel a t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hg t ht

lemma completedHurwitzZetaEven₀_logGrowth (a : UnitAddCircle) :
    LogGrowth (completedHurwitzZetaEven₀ a) := by
  refine (((even_logGrowth a).comp (g := fun s => s / 2) le_rfl (fun s => ?_)).mul
    (LogGrowth.const (1 / 2))).congr (fun s => ?_)
  · rw [norm_div, Complex.norm_two, add_zero]
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaEven₀]; ring

end
section

open Complex

noncomputable def xiZeta (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xiZeta : Differentiable ℂ xiZeta := by
  unfold xiZeta
  have := differentiable_completedZeta₀
  fun_prop

theorem xiZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiZeta s = s * (s - 1) * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [xiZeta, completedRiemannZeta_eq]
  field_simp
  ring

theorem xiZeta_zero : xiZeta 0 = 1 := by simp [xiZeta]

theorem growth_of_logGrowth {F : ℂ → ℂ} (hF : LogGrowth F) :
    ∃ C : ℝ, ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨K, a, b, ha, hb, h⟩ := hF
  have hK : 0 ≤ K := LogGrowth.nonneg_K h
  set lb := Real.log b
  have hlb : 0 ≤ lb := Real.log_nonneg (by linarith)
  set C₀ := a * (2 * lb + 1 + 2 * b)
  set D := a * (b * (lb + 1))
  refine ⟨max (K * Real.exp D) C₀, fun s => (h s).trans ?_⟩
  set u := ‖s‖
  have hu : 0 ≤ u := norm_nonneg s
  set ℓ := Real.log (u + 2)
  have hℓ2 : (1 / 2 : ℝ) ≤ ℓ := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hℓu : ℓ ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by linarith); linarith
  have hL : 0 ≤ u * ℓ := by positivity
  have h1 : Real.log (u + b) ≤ lb + ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : u ≤ 2 * (u * ℓ) := by nlinarith
  have key : a * ((u + b) * Real.log (u + b)) ≤ C₀ * (u * ℓ) + D := by
    have e : (u + b) * Real.log (u + b) ≤ (2 * lb + 1 + 2 * b) * (u * ℓ) + b * (lb + 1) := by
      calc (u + b) * Real.log (u + b) ≤ (u + b) * (lb + ℓ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = lb * u + u * ℓ + b * lb + b * ℓ := by ring
        _ ≤ lb * (2 * (u * ℓ)) + u * ℓ + b * lb + b * (2 * (u * ℓ) + 1) := by
            gcongr; linarith
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left e ha
    simp only [C₀, D]; nlinarith
  calc K * Real.exp (a * ((u + b) * Real.log (u + b)))
      ≤ K * Real.exp (C₀ * (u * ℓ) + D) := by gcongr
    _ = K * Real.exp D * Real.exp (C₀ * (u * ℓ)) := by
        rw [Real.exp_add]; ring
    _ ≤ max (K * Real.exp D) C₀ * Real.exp (max (K * Real.exp D) C₀ * (u * ℓ)) :=
        mul_le_mul (le_max_left _ _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL))
          (Real.exp_pos _).le (le_max_of_le_left (by positivity))
    _ = _ := by ring_nf

theorem xiZeta_growth :
    ∃ C : ℝ, ∀ s : ℂ, ‖xiZeta s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by

  have hid : LogGrowth (fun s : ℂ => s) := by
    refine ⟨1, 1, 3, zero_le_one, le_rfl, fun s => ?_⟩
    have h3 : 1 ≤ Real.log (‖s‖ + 3) := one_le_log_of_three_le (by linarith [norm_nonneg s])
    have := Real.add_one_le_exp ‖s‖
    have : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by nlinarith [norm_nonneg s]
    have : Real.exp ‖s‖ ≤ Real.exp (1 * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith

  have h : LogGrowth xiZeta :=
    (((hid.mul (hid.add (LogGrowth.const (-1)))).mul
      (completedHurwitzZetaEven₀_logGrowth 0)).add (LogGrowth.const 1)).congr fun s => by
        simp only [xiZeta, completedRiemannZeta₀]; ring
  exact growth_of_logGrowth h

end
section

open Complex Metric Set

lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {z : ℂ} (hz : z ∈ U) : MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, analyticOrderNatAt]
  cases analyticOrderAt f z with
  | top => simp
  | coe n => simp

theorem zeroCountOn_le_of_jensen {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) {S : Set ℂ} (hS : S ⊆ closedBall c r) :
    (zeroCountOn f S : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [abs_of_pos hR]
  have J := AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M) (by rwa [abs_of_pos hr])
    (by rwa [abs_of_pos hr, abs_of_pos hR]) hM hf' hfc (by rwa [abs_of_pos hR])
  rw [abs_of_pos hr] at J
  set D := MeromorphicOn.divisor f (closedBall c r)
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
  have hDfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall c r)
  set F := hDfin.toFinset
  set g : ℂ → ℕ := fun s => analyticOrderNatAt f s
  have hsub : S ∩ Function.support g ⊆ (F : Set ℂ) := by
    intro s ⟨hsS, hs⟩
    simp only [Set.Finite.coe_toFinset, Function.mem_support, F]
    rw [divisor_eq_analyticOrderNatAt hfr (hS hsS)]
    exact_mod_cast hs
  have hfin : (S ∩ Function.support g).Finite := F.finite_toSet.subset hsub
  have h1 : zeroCountOn f S ≤ ∑ s ∈ F, g s := by
    unfold zeroCountOn
    rw [finsum_mem_eq_sum g hfin]
    exact Finset.sum_le_sum_of_subset (fun x hx => hsub (by simpa using hx))
  have h2 : (∑ᶠ u, D u) = ∑ u ∈ F, (g u : ℤ) := by
    rw [finsum_eq_sum_of_support_subset D (s := F) (by simp [F])]
    refine Finset.sum_congr rfl fun u hu => ?_
    have huD : u ∈ Function.support D := by simpa [F] using hu
    exact divisor_eq_analyticOrderNatAt hfr (D.supportWithinDomain huD)
  have h3 : ((∑ᶠ u, D u : ℤ) : ℝ) = ((∑ s ∈ F, g s : ℕ) : ℝ) := by
    rw [h2]; push_cast; rfl
  calc (zeroCountOn f S : ℝ) ≤ ((∑ s ∈ F, g s : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((∑ᶠ u, D u : ℤ) : ℝ) := h3.symm
    _ ≤ _ := J

end

section

open Complex Filter Topology

lemma xiZeta_one : xiZeta 1 = 1 := by simp [xiZeta]

lemma not_analyticAt_riemannZeta_one : ¬ AnalyticAt ℂ riemannZeta 1 := by
  intro h
  have hc : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 ((1 - 1) * riemannZeta 1)) :=
    ((continuousAt_id.sub continuousAt_const).mul h.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have := tendsto_nhds_unique hc riemannZeta_residue_one
  simp at this

lemma analyticOrderNatAt_riemannZeta_one : analyticOrderNatAt riemannZeta 1 = 0 := by
  simp [analyticOrderNatAt, analyticOrderAt_of_not_analyticAt not_analyticAt_riemannZeta_one]

lemma analyticAt_xiZeta (z : ℂ) : AnalyticAt ℂ xiZeta z :=
  differentiable_xiZeta.analyticAt z

noncomputable def zetaXiFactor (s : ℂ) : ℂ := (Gammaℝ s)⁻¹ / (s * (s - 1))

lemma riemannZeta_eq_xiZeta_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannZeta s = xiZeta s * zetaXiFactor s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [xiZeta_eq hs0 hs1, zetaXiFactor, riemannZeta_def_of_ne_zero hs0]
  field_simp

lemma analyticAt_zetaXiFactor {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    AnalyticAt ℂ zetaXiFactor ρ := by
  have hU : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
  refine DifferentiableOn.analyticAt (s := ({0, 1}ᶜ : Set ℂ)) ?_ (hU.mem_nhds (by simp [h0, h1]))
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  have hd : z * (z - 1) ≠ 0 := mul_ne_zero hz.1 (sub_ne_zero.mpr hz.2)
  exact ((differentiable_Gammaℝ_inv z).div (by fun_prop) hd).differentiableWithinAt

theorem analyticOrderNatAt_riemannZeta_eq_xiZeta {ρ : ℂ} (hρ : -2 < ρ.re) :
    analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt xiZeta ρ := by
  by_cases h1 : ρ = 1
  · subst h1
    rw [analyticOrderNatAt_riemannZeta_one,
      Complex.analyticOrderNatAt_eq_zero_of_ne_zero (by rw [xiZeta_one]; exact one_ne_zero)]
  by_cases h0 : ρ = 0
  · subst h0
    rw [Complex.analyticOrderNatAt_eq_zero_of_ne_zero (by rw [riemannZeta_zero]; norm_num),
      Complex.analyticOrderNatAt_eq_zero_of_ne_zero (by rw [xiZeta_zero]; exact one_ne_zero)]
  have hΓ : Gammaℝ ρ ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, rfl⟩
    rcases n with _ | n
    · simp at h0
    · simp at hρ; linarith
  have hev : riemannZeta =ᶠ[𝓝 ρ] xiZeta * zetaXiFactor := by
    have hU : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
    filter_upwards [hU.mem_nhds (by simp [h0, h1])] with s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    exact riemannZeta_eq_xiZeta_mul hs.1 hs.2
  have hfac : zetaXiFactor ρ ≠ 0 := by
    have hd : ρ * (ρ - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
    simp [zetaXiFactor, hΓ, hd]
  have hord : analyticOrderAt zetaXiFactor ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hfac)
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hev,
    analyticOrderAt_mul (analyticAt_xiZeta ρ) (analyticAt_zetaXiFactor h0 h1), hord, add_zero]

theorem zeroCountOn_riemannZeta_eq_xiZeta {S : Set ℂ} (hS : ∀ s ∈ S, -2 < s.re) :
    zeroCountOn riemannZeta S = zeroCountOn xiZeta S := by
  unfold zeroCountOn
  exact finsum_mem_congr rfl fun s hs => analyticOrderNatAt_riemannZeta_eq_xiZeta (hS s hs)

end

section

open Complex Metric Set

theorem zeroCountOn_xiZeta_le :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 1 ≤ r → ∀ S : Set ℂ, S ⊆ closedBall 0 r →
      (zeroCountOn xiZeta S : ℝ) ≤ A * r * Real.log (r + 2) := by
  obtain ⟨C, hC⟩ := xiZeta_growth
  set C₀ := max C 1
  have hC₀ : 1 ≤ C₀ := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log C₀ + 4 * C₀) / Real.log 2,
    div_pos (by have := Real.log_nonneg hC₀; linarith) hlog2, fun r hr S hS => ?_⟩
  have hr0 : 0 < r := by linarith
  set L := Real.log (2 * r + 2)
  set M := C₀ * Real.exp (C₀ * (2 * r) * L)
  have hL : 1 ≤ L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hM : 1 ≤ M := by
    have : 1 ≤ Real.exp (C₀ * (2 * r) * L) := Real.one_le_exp (by positivity)
    nlinarith
  have hb : ∀ z ∈ sphere (0 : ℂ) (2 * r), ‖xiZeta z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine (hC z).trans ?_
    rw [hz]
    have hCC : C ≤ C₀ := le_max_left _ _
    have h1 : C * (2 * r) * Real.log (2 * r + 2) ≤ C₀ * (2 * r) * L := by
      have : 0 ≤ Real.log (2 * r + 2) := by linarith
      gcongr
    calc C * Real.exp (C * (2 * r) * Real.log (2 * r + 2))
        ≤ C₀ * Real.exp (C * (2 * r) * Real.log (2 * r + 2)) := by gcongr
      _ ≤ M := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (by linarith)
  have J := zeroCountOn_le_of_jensen (f := xiZeta) (c := 0) hr0 (by linarith : r < 2 * r) hM
    (fun z _ => analyticAt_xiZeta z) (by rw [xiZeta_zero]; exact one_ne_zero) hb hS
  rw [xiZeta_zero, norm_one, div_one, show 2 * r / r = 2 by field_simp] at J
  refine J.trans ?_
  rw [div_le_iff₀ hlog2]
  have hlogM : Real.log M = Real.log C₀ + C₀ * (2 * r) * L := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hLr : L ≤ Real.log (r + 2) + Real.log 2 := by
    rw [← Real.log_mul (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hr2 : 1 ≤ r * Real.log (r + 2) := by
    have : 1 ≤ Real.log (r + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    nlinarith
  have hl0 := Real.log_nonneg hC₀
  have hlog2' : Real.log 2 ≤ Real.log (r + 2) := Real.log_le_log (by norm_num) (by linarith)
  have e : (Real.log C₀ + 4 * C₀) / Real.log 2 * r * Real.log (r + 2) * Real.log 2
      = (Real.log C₀ + 4 * C₀) * (r * Real.log (r + 2)) := by
    field_simp
  rw [e, hlogM]
  have hL2 : L ≤ 2 * Real.log (r + 2) := by linarith
  have : C₀ * (2 * r) * L ≤ 4 * C₀ * (r * Real.log (r + 2)) := by
    have := mul_le_mul_of_nonneg_left hL2 (by positivity : (0 : ℝ) ≤ C₀ * (2 * r))
    linarith
  nlinarith

theorem zeroCountOn_riemannZeta_le_of_subset_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ S : Set ℂ,
      S ⊆ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} →
      (zeroCountOn riemannZeta S : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A, hA, hcount⟩ := zeroCountOn_xiZeta_le
  refine ⟨9 / 2 * A, by positivity, fun T hT S hS => ?_⟩
  have hball : S ⊆ closedBall 0 (T + 1) := by
    intro s hs
    obtain ⟨h0, h1, hT'⟩ := hS hs
    rw [mem_closedBall_zero_iff]
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + T := by rw [abs_of_nonneg h0]; linarith
      _ = T + 1 := by ring
  rw [zeroCountOn_riemannZeta_eq_xiZeta fun s hs => by linarith [(hS hs).1]]
  refine (hcount (T + 1) (by linarith) S hball).trans ?_
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog3 : Real.log (T + 1 + 2) ≤ 3 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    norm_num
    nlinarith [mul_le_mul hT hT (by norm_num) (by linarith : (0:ℝ) ≤ T)]
  calc A * (T + 1) * Real.log (T + 1 + 2) ≤ A * (3 / 2 * T) * (3 * Real.log T) := by
        gcongr
        · exact Real.log_nonneg (by linarith)
        · linarith
    _ = 9 / 2 * A * T * Real.log T := by ring

end

end OMA.DH2

theorem OMA.solution : OMA.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1.H2 := by
  obtain ⟨C, hC, h⟩ := OMA.DH2.zeroCountOn_riemannZeta_le_of_subset_strip
  exact ⟨C, hC, fun T hT => h T hT _ fun s hs =>
    ⟨hs.1, hs.2.1, by rw [abs_of_pos hs.2.2.1]; exact hs.2.2.2⟩⟩
