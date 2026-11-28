import FormalConjectures.Wikipedia.Transcendental
import Mathlib

/-!
# Rivoal's Theorem (2012): At least one of γ and δ is transcendental

Complete self-contained proof via the Euler-Mascheroni / Gompertz / Ein(1) identity
and the Siegel-Shidlovskii method for the E-function system `(e^{-a z} Ein(z)^b)`.
-/

open scoped BigOperators Topology Nat
open Filter MeasureTheory Set Real Polynomial Matrix

namespace OMA_Rivoal_2012

/- ### Section 1: The Euler-Mascheroni / Gompertz / Ein(1) identity -/

/-- Entire exponential integral function `Ein(z) = ∑_{k=0}^∞ (-1)^k z^{k+1} / ((k+1) (k+1)!)`. -/
noncomputable def einTerm (z : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * z ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))

noncomputable def Ein (z : ℝ) : ℝ :=
  ∑' k : ℕ, einTerm z k

lemma summable_einTerm (z : ℝ) : Summable (einTerm z) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => |z| ^ (k + 1) / ((k + 1).factorial : ℝ)) ?_ ?_
  · have h := (Real.summable_pow_div_factorial |z|).comp_injective Nat.succ_injective
    simpa [Function.comp_def] using h
  · intro k
    rw [einTerm, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_pow, Real.norm_eq_abs, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg z) _) hfac (by nlinarith)

lemma one_sub_exp_neg_div_eq_tsum {t : ℝ} (ht : t ≠ 0) :
    (1 - Real.exp (-t)) / t = ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ) := by
  have hexp : Real.exp (-t) = ∑' n : ℕ, (-t) ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hs : Summable (fun n : ℕ => (-t) ^ n / (n.factorial : ℝ)) := by
    simpa [div_eq_mul_inv] using Real.summable_pow_div_factorial (-t)
  have hsplit := hs.tsum_eq_zero_add
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
  have hsub : 1 - Real.exp (-t) = ∑' k : ℕ, -((-t) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    rw [hexp, hsplit, tsum_neg]
    ring
  rw [hsub, ← tsum_div_const]
  refine tsum_congr fun k => ?_
  have hpow : (-t) ^ (k + 1) = (-1 : ℝ) ^ (k + 1) * t ^ (k + 1) := by rw [← mul_pow]; ring_nf
  rw [hpow, pow_succ', pow_succ]
  field_simp [ht]

lemma ein_one_eq_integral :
    Ein 1 = ∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t := by
  have hmeas : ∀ k : ℕ, IntegrableOn (fun t : ℝ => (-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ))
      (Set.Ioc 0 1) volume := fun k => by
    have hcont : Continuous (fun t : ℝ => (-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ)) := by
      fun_prop
    exact hcont.integrableOn_Ioc
  have hnorm_sum : Summable (fun k : ℕ => ∫ t in Set.Ioc (0 : ℝ) 1,
      ‖(-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ)‖) := by
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_)
      (Real.summable_pow_div_factorial (1 : ℝ))
    have hle : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ‖(-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ)‖ ≤ (1 : ℝ) ^ k / (k.factorial : ℝ) := by
      intro t ht
      rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        norm_pow, Real.norm_of_nonneg ht.1.le, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      have ht1 : t ^ k ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have hfac : (k.factorial : ℝ) ≤ ((k + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (Nat.le_succ k)
      calc t ^ k / ((k + 1).factorial : ℝ)
          ≤ 1 / ((k + 1).factorial : ℝ) := div_le_div_of_nonneg_right ht1 (by positivity)
        _ ≤ 1 / (k.factorial : ℝ) := div_le_div_of_nonneg_left zero_le_one (by positivity) hfac
    calc ∫ t in Set.Ioc (0 : ℝ) 1, ‖(-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ)‖
        ≤ ∫ _t in Set.Ioc (0 : ℝ) 1, (1 : ℝ) ^ k / (k.factorial : ℝ) := by
          refine setIntegral_mono_on (hmeas k).norm (integrableOn_const (by simp)) measurableSet_Ioc hle
      _ = (1 : ℝ) ^ k / (k.factorial : ℝ) := by simp
  have htsum_int := integral_tsum_of_summable_integral_norm hmeas hnorm_sum
  have hcongr : ∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t =
      ∫ t in Set.Ioc (0 : ℝ) 1, ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ k / ((k + 1).factorial : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    exact one_sub_exp_neg_div_eq_tsum (ne_of_gt ht.1)
  rw [hcongr, ← htsum_int]
  unfold Ein
  refine tsum_congr fun k => ?_
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [div_eq_mul_inv, mul_comm _ (((k + 1).factorial : ℝ)⁻¹)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  simp only [einTerm, one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero, div_eq_mul_inv, mul_inv]
  push_cast
  ring

lemma integral_one_sub_pow_div_eq_harmonic (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in (0 : ℝ)..(N : ℝ), (1 - (1 - t / N) ^ N) / t = (harmonic N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : ∫ t in (0 : ℝ)..(N : ℝ), (1 - (1 - t / N) ^ N) / t =
      ∫ u in (0 : ℝ)..1, (1 - (1 - u) ^ N) / u := by
    have h1 := intervalIntegral.integral_comp_mul_left
      (f := fun t : ℝ => (1 - (1 - t / N) ^ N) / t) (a := (0 : ℝ)) (b := 1) (c := (N : ℝ)) hNpos.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at h1
    have h2 : ∀ u : ℝ, (1 - (1 - (N : ℝ) * u / N) ^ N) / ((N : ℝ) * u) =
        (N : ℝ)⁻¹ * ((1 - (1 - u) ^ N) / u) := by
      intro u
      have hNu : (N : ℝ) * u / N = u := mul_div_cancel_left₀ u hNpos.ne'
      rw [hNu]
      by_cases hu : u = 0
      · simp [hu]
      · field_simp [hNpos.ne', hu]
    simp_rw [h2] at h1
    rw [intervalIntegral.integral_const_mul] at h1
    exact mul_left_cancel₀ (inv_ne_zero hNpos.ne') h1.symm
  rw [hsub]
  have hgeom : ∀ u : ℝ, u ≠ 0 → (1 - (1 - u) ^ N) / u = ∑ k ∈ Finset.range N, (1 - u) ^ k := by
    intro u hu
    have h := geom_sum_mul (1 - u) N
    have hsub1 : (1 - u) - 1 = -u := by ring
    rw [hsub1] at h
    have h2 : (∑ k ∈ Finset.range N, (1 - u) ^ k) * u = 1 - (1 - u) ^ N := by linarith
    exact (div_eq_iff hu).mpr h2.symm
  have hae : EqOn (fun u : ℝ => (1 - (1 - u) ^ N) / u)
      (fun u : ℝ => ∑ k ∈ Finset.range N, (1 - u) ^ k) (Set.Ioc 0 1) :=
    fun u hu => hgeom u (ne_of_gt hu.1)
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_fun measurableSet_Ioc hae,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hcomp := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ k) (1 : ℝ) (a := (0 : ℝ)) (b := 1)
    simp only [sub_zero, sub_self] at hcomp
    rw [hcomp, integral_pow]
    simp [Nat.cast_add, Nat.cast_one]
  · intro k _
    exact (Continuous.intervalIntegrable (by fun_prop) 0 1)

lemma one_sub_div_pow_le_exp_neg {t : ℝ} {N : ℕ} (hN : 1 ≤ N) (htN : t ≤ N) :
    (1 - t / N) ^ N ≤ Real.exp (-t) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 ≤ 1 - t / N := by
    rw [sub_nonneg, div_le_one hNpos]; exact htN
  have h2 : 1 - t / N ≤ Real.exp (-(t / N)) := by
    have := Real.add_one_le_exp (-(t / N))
    linarith
  calc (1 - t / N) ^ N
      ≤ (Real.exp (-(t / N))) ^ N := pow_le_pow_left₀ h1 h2 N
    _ = Real.exp ((N : ℝ) * (-(t / N))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (-t) := by congr 1; field_simp [hNpos.ne']

lemma bernoulli_one_sub {t : ℝ} {N : ℕ} (hN : 1 ≤ N) (ht1 : t ≤ 1) :
    1 - t ≤ (1 - t / N) ^ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (-2 : ℝ) ≤ -(t / N) := by
    have : t / N ≤ 1 := (div_le_one hNpos).mpr (ht1.trans (by exact_mod_cast hN))
    linarith
  have hb := one_add_mul_le_pow hle N
  have hmul : (N : ℝ) * (-(t / N)) = -t := by field_simp [hNpos.ne']
  have hadd : (1 : ℝ) + -(t / N) = 1 - t / N := by ring
  rw [hadd, hmul] at hb
  linarith

lemma tendsto_one_sub_div_pow (t : ℝ) :
    Tendsto (fun N : ℕ => (1 - t / (N : ℝ)) ^ N) atTop (𝓝 (Real.exp (-t))) := by
  have hc := Complex.tendsto_one_add_div_pow_exp (-(t : ℂ))
  have hre := (Complex.continuous_re.continuousAt.tendsto).comp hc
  refine hre.congr (fun N => ?_) |>.trans ?_
  · simp only [Function.comp_def]
    have heq : (1 + -(t : ℂ) / (N : ℂ)) ^ N = (((1 - t / (N : ℝ)) ^ N : ℝ) : ℂ) := by
      push_cast; ring
    rw [heq, Complex.ofReal_re]
  · simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re]
    exact le_rfl

lemma integrableOn_exp_neg_div_Ioi :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi (1 : ℝ)) volume := by
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi (1 : ℝ)) volume := by
    have h := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) (1 : ℝ)
    simpa using h
  refine hdom.mono' ((Continuous.measurable (by fun_prop)).div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))]
  exact div_le_self (Real.exp_pos _).le ht1.le

lemma eulerMascheroni_eq_ein_one_sub_integral :
    Real.eulerMascheroniConstant = Ein 1 - ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t := by
  rw [ein_one_eq_integral]
  have hN_eq : ∀ N : ℕ, 1 ≤ N →
      (harmonic N : ℝ) - Real.log N =
        (∫ t in Set.Ioc (0 : ℝ) 1, (1 - (1 - t / N) ^ N) / t) -
        (∫ t in Set.Ioi (1 : ℝ), if t ≤ N then (1 - t / N) ^ N / t else 0) := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hH := integral_one_sub_pow_div_eq_harmonic N hN
    have hint1 : IntervalIntegrable (fun t : ℝ => (1 - (1 - t / N) ^ N) / t) volume 0 1 := by
      have hae : EqOn (fun t : ℝ => (1 - (1 - t / N) ^ N) / t)
          (fun t : ℝ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, (1 - t / N) ^ k) (Set.Ioc 0 1) := by
        intro t ht
        have hNpos : (0 : ℝ) < N := by linarith
        have htpos : t ≠ 0 := ne_of_gt ht.1
        have h := geom_sum_mul (1 - t / N) N
        have hsub1 : (1 - t / N) - 1 = -(t / N) := by ring
        rw [hsub1] at h
        have h2 : (∑ k ∈ Finset.range N, (1 - t / N) ^ k) * (t / N) = 1 - (1 - t / N) ^ N := by linarith
        rw [div_eq_iff htpos]
        calc 1 - (1 - t / N) ^ N
            = (∑ k ∈ Finset.range N, (1 - t / N) ^ k) * (t / N) := h2.symm
          _ = (N : ℝ)⁻¹ * (∑ k ∈ Finset.range N, (1 - t / N) ^ k) * t := by ring
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact (Continuous.integrableOn_Ioc (by fun_prop)).congr_fun hae.symm measurableSet_Ioc
    have hint2 : IntervalIntegrable (fun t : ℝ => (1 - (1 - t / N) ^ N) / t) volume 1 N := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hN1]
      intro t ht
      have htne : t ≠ 0 := by linarith [ht.1]
      exact ((continuousAt_const.sub ((continuousAt_const.sub (continuousAt_id.div_const _)).pow _)).div
        continuousAt_id htne).continuousWithinAt
    rw [← hH, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hlog : Real.log N = ∫ t in (1 : ℝ)..N, (1 : ℝ) / t := by
      rw [integral_one_div_of_pos (by norm_num) (by linarith), div_one]
    have hint_inv : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume 1 N := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hN1]
      intro t ht
      have htne : t ≠ 0 := by linarith [ht.1]
      exact (continuousAt_const.div continuousAt_id htne).continuousWithinAt
    have hint_pow : IntervalIntegrable (fun t : ℝ => (1 - t / N) ^ N / t) volume 1 N := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hN1]
      intro t ht
      have htne : t ≠ 0 := by linarith [ht.1]
      exact (((continuousAt_const.sub (continuousAt_id.div_const _)).pow _).div
        continuousAt_id htne).continuousWithinAt
    have hsplit2 : ∫ t in (1 : ℝ)..N, (1 - (1 - t / N) ^ N) / t =
        (∫ t in (1 : ℝ)..N, (1 : ℝ) / t) - ∫ t in (1 : ℝ)..N, (1 - t / N) ^ N / t := by
      rw [← intervalIntegral.integral_sub hint_inv hint_pow]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [hsplit2, ← hlog, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le hN1]
    have hind : ∫ t in Set.Ioc (1 : ℝ) N, (1 - t / N) ^ N / t =
        ∫ t in Set.Ioi (1 : ℝ), if t ≤ N then (1 - t / N) ^ N / t else 0 := by
      have hset : Set.Ioc (1 : ℝ) N = Set.Ioi (1 : ℝ) ∩ Set.Iic (N : ℝ) := rfl
      rw [hset, ← setIntegral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      by_cases ht : t ≤ N <;> simp [Set.indicator, ht]
    rw [hind]
    ring
  have htend1 : Tendsto (fun N : ℕ => ∫ t in Set.Ioc (0 : ℝ) 1, (1 - (1 - t / N) ^ N) / t)
      atTop (𝓝 (∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N _
      exact ((Continuous.measurable (by fun_prop : Continuous fun t : ℝ => 1 - (1 - t / N) ^ N)).div
        measurable_id).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with N hN
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hlow := bernoulli_one_sub hN ht.2
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hhi : (1 - t / N) ^ N ≤ 1 :=
        pow_le_one₀ (by rw [sub_nonneg, div_le_one hNpos]; exact ht.2.trans (by exact_mod_cast hN))
          (by linarith [div_nonneg ht0.le hNpos.le])
      rw [Real.norm_of_nonneg (div_nonneg (by linarith) ht0.le)]
      exact (div_le_one ht0).mpr (by linarith)
    · exact integrableOn_const (by simp)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
      exact ((tendsto_const_nhds.sub (tendsto_one_sub_div_pow t)).div_const t)
  have htend2 : Tendsto (fun N : ℕ => ∫ t in Set.Ioi (1 : ℝ), if t ≤ N then (1 - t / N) ^ N / t else 0)
      atTop (𝓝 (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => Real.exp (-t) / t) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N _
      have hm : Measurable (fun t : ℝ => if t ≤ (N : ℝ) then (1 - t / N) ^ N / t else 0) :=
        Measurable.ite measurableSet_Iic
          ((Continuous.measurable (by fun_prop : Continuous fun t : ℝ => (1 - t / N) ^ N)).div measurable_id)
          measurable_const
      exact hm.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with N hN
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      split_ifs with hle
      · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hnn : 0 ≤ (1 - t / N) ^ N :=
          pow_nonneg (by rw [sub_nonneg, div_le_one hNpos]; exact hle) N
        rw [Real.norm_of_nonneg (div_nonneg hnn ht0.le)]
        exact div_le_div_of_nonneg_right (one_sub_div_pow_le_exp_neg hN hle) ht0.le
      · rw [norm_zero]
        exact div_nonneg (Real.exp_pos _).le ht0.le
    · exact integrableOn_exp_neg_div_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      have hev : ∀ᶠ N : ℕ in atTop,
          (1 - t / (N : ℝ)) ^ N / t = (if t ≤ (N : ℝ) then (1 - t / N) ^ N / t else 0) := by
        obtain ⟨M, hM⟩ := exists_nat_ge t
        filter_upwards [eventually_ge_atTop M] with N hN
        rw [if_pos (hM.trans (by exact_mod_cast hN))]
      exact ((tendsto_one_sub_div_pow t).div_const t).congr' hev
  have htend_diff := htend1.sub htend2
  have htend_em : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hcongr_ev : ∀ᶠ N : ℕ in atTop,
      (∫ t in Set.Ioc (0 : ℝ) 1, (1 - (1 - t / N) ^ N) / t) -
        (∫ t in Set.Ioi (1 : ℝ), if t ≤ N then (1 - t / N) ^ N / t else 0) =
      (harmonic N : ℝ) - Real.log N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hN_eq N hN).symm
  exact tendsto_nhds_unique htend_em (htend_diff.congr' hcongr_ev)

lemma ein_one_eq_gamma_sub_exp_neg_mul_gompertz :
    Ein 1 = Real.eulerMascheroniConstant - Real.exp (-1) * gompertzConstant := by
  have h1 := eulerMascheroni_eq_ein_one_sub_integral
  unfold gompertzConstant
  rw [show Real.exp (-1) * (-Real.exp 1 * ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t) =
      -(Real.exp (-1) * Real.exp 1) * ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t by ring]
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linarith

/- ### Section 2: Finite-dimensional reduction from algebraicity of γ and δ -/

abbrev Idx (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1.1 + p.2.1 ≤ n}

lemma card_idx (n : ℕ) : Fintype.card (Idx n) = (n + 1) * (n + 2) / 2 := by
  let S : Finset (Fin (n + 1) × Fin (n + 1)) :=
    Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) => p.1.1 + p.2.1 ≤ n
  have h1 : Fintype.card (Idx n) = S.card := Fintype.card_subtype _
  rw [h1]
  have h2 : S.card = ∑ a : Fin (n + 1), (Finset.univ.filter fun b : Fin (n + 1) => a.1 + b.1 ≤ n).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
    · intro p hp
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [hp]
    · intro p1 _ p2 _ h
      cases p1; cases p2
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      exact Prod.ext h.1 h.2
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hq
      exact ⟨(q.1, q.2), by simp [S, hq], rfl⟩
  rw [h2]
  have hrow : ∀ a : Fin (n + 1),
      (Finset.univ.filter fun b : Fin (n + 1) => a.1 + b.1 ≤ n).card = n + 1 - a.1 := by
    intro a
    refine (Finset.card_bij (fun b _ => b.1) ?_ ?_ ?_).trans (Finset.card_range (n + 1 - a.1))
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [Finset.mem_range]; omega
    · intro b1 _ b2 _ h; exact Fin.ext h
    · intro k hk
      simp only [Finset.mem_range] at hk
      exact ⟨⟨k, by omega⟩, by simp; omega, rfl⟩
  simp_rw [hrow, Fin.sum_univ_eq_sum_range (fun a => n + 1 - a)]
  clear S h1 h2 hrow
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub, ih]
    have heven : 2 ∣ (k + 1) * (k + 2) := (Nat.even_mul_succ_self (k + 1)).two_dvd
    have heven2 : 2 ∣ (k + 2) * (k + 3) := (Nat.even_mul_succ_self (k + 2)).two_dvd
    have hmul : 2 * ((k + 1) * (k + 2) / 2 + (k + 2)) = 2 * ((k + 2) * (k + 3) / 2) := by
      rw [mul_add, Nat.mul_div_cancel' heven, Nat.mul_div_cancel' heven2]; ring
    rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega]
    omega

lemma pow_mem_span_of_poly_root {x : ℝ} {P : ℚ[X]} (hP : P ≠ 0) (hroot : aeval x P = 0) :
    ∀ k : ℕ, x ^ k ∈ Submodule.span ℚ (Set.range fun i : Fin P.natDegree => x ^ i.1) := by
  have hdeg : 0 < P.natDegree := by
    by_contra h0
    have h0' : P.natDegree = 0 := by omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0'] at hP hroot
    rw [Polynomial.aeval_C, eq_ratCast, Rat.cast_eq_zero] at hroot
    rw [hroot, map_zero] at hP
    exact hP rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < P.natDegree
    · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
    · have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
      have hP_eval : (P.leadingCoeff : ℝ) * x ^ P.natDegree +
          ∑ i ∈ Finset.range P.natDegree, (P.coeff i : ℝ) * x ^ i = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
          Polynomial.coeff_natDegree, add_comm] at hroot
        simpa only [eq_ratCast] using hroot
      have hlead : x ^ P.natDegree =
          ∑ i ∈ Finset.range P.natDegree, (-(P.coeff i / P.leadingCoeff) : ℚ) • x ^ i := by
        have hlcR : (P.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast hlc
        have h1 : x ^ P.natDegree =
            -((∑ i ∈ Finset.range P.natDegree, (P.coeff i : ℝ) * x ^ i) / (P.leadingCoeff : ℝ)) := by
          field_simp [hlcR]; linarith
        rw [h1, Finset.sum_div, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, eq_ratCast]
        push_cast
        ring
      have hmul : x ^ k = ∑ i ∈ Finset.range P.natDegree,
          (-(P.coeff i / P.leadingCoeff) : ℚ) • x ^ (i + (k - P.natDegree)) := by
        have hsplit : x ^ k = x ^ P.natDegree * x ^ (k - P.natDegree) := by
          rw [← pow_add, Nat.add_sub_of_le (by omega)]
        rw [hsplit, hlead, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, mul_assoc, ← pow_add]
      rw [hmul]
      refine Submodule.sum_mem _ fun i hi => ?_
      have hi' : i < P.natDegree := Finset.mem_range.mp hi
      exact Submodule.smul_mem _ _ (ih (i + (k - P.natDegree)) (by omega))

lemma exists_int_linear_relation_of_algebraic
    (hγ : IsAlgebraic ℚ Real.eulerMascheroniConstant)
    (hδ : IsAlgebraic ℚ gompertzConstant) :
    ∃ (n : ℕ) (c : Idx n → ℤ), (∃ p, c p ≠ 0) ∧
      ∑ p : Idx n, (c p : ℝ) * (Real.exp (-(p.1.1.1 : ℝ)) * (Ein 1) ^ p.1.2.1) = 0 := by
  obtain ⟨P, hP, hProot⟩ := hγ
  obtain ⟨Q, hQ, hQroot⟩ := hδ
  let d1 := P.natDegree
  let d2 := Q.natDegree
  let d := d1 * d2
  let n := 2 * d
  let gen : (Fin d1 × Fin d2) × Fin (n + 1) → ℝ := fun q =>
    Real.eulerMascheroniConstant ^ q.1.1.1 * gompertzConstant ^ q.1.2.1 * Real.exp (-(q.2.1 : ℝ))
  let W : Submodule ℚ ℝ := Submodule.span ℚ (Set.range gen)
  have hW_fin : Module.Finite ℚ W := Module.Finite.span_of_finite ℚ (Set.finite_range gen)
  have hW_dim : Module.finrank ℚ W ≤ d * (n + 1) := by
    have hle := finrank_span_le_card (R := ℚ) (Set.range gen)
    rw [Set.toFinset_card] at hle
    have hcard : Fintype.card (Set.range gen) ≤ Fintype.card ((Fin d1 × Fin d2) × Fin (n + 1)) :=
      Fintype.card_range_le gen
    calc Module.finrank ℚ W
        ≤ Fintype.card (Set.range gen) := hle
      _ ≤ Fintype.card ((Fin d1 × Fin d2) × Fin (n + 1)) := hcard
      _ = d * (n + 1) := by simp [d]
  have hpow_mem : ∀ (u v : ℕ) (k : Fin (n + 1)),
      Real.eulerMascheroniConstant ^ u * gompertzConstant ^ v * Real.exp (-(k.1 : ℝ)) ∈ W := by
    intro u v k
    have hu := pow_mem_span_of_poly_root hP hProot u
    have hv := pow_mem_span_of_poly_root hQ hQroot v
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hu hv
    obtain ⟨cu, hcu⟩ := hu
    obtain ⟨cv, hcv⟩ := hv
    rw [← hcu, ← hcv]
    simp only [Finsupp.sum]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem W fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem W fun j _ => ?_
    have hterm : (cu i • Real.eulerMascheroniConstant ^ i.1) *
        (cv j • gompertzConstant ^ j.1) * Real.exp (-(k.1 : ℝ)) =
        (cu i * cv j) • gen ((i, j), k) := by
      simp only [gen, Algebra.smul_def, eq_ratCast, Rat.cast_mul]
      ring
    rw [hterm]
    exact Submodule.smul_mem W _ (Submodule.subset_span ⟨((i, j), k), rfl⟩)
  have hmemW : ∀ p : Idx n, Real.exp (-(p.1.1.1 : ℝ)) * (Ein 1) ^ p.1.2.1 ∈ W := by
    intro ⟨⟨a, b⟩, hab⟩
    have hab' : a.1 + b.1 ≤ n := hab
    rw [ein_one_eq_gamma_sub_exp_neg_mul_gompertz, sub_eq_add_neg, add_pow, Finset.mul_sum]
    refine Submodule.sum_mem W fun j hj => ?_
    have hjb : j ≤ b.1 := Finset.mem_range_succ_iff.mp hj
    let k : Fin (n + 1) := ⟨a.1 + (b.1 - j), by omega⟩
    have hval : Real.exp (-(a.1 : ℝ)) *
        (Real.eulerMascheroniConstant ^ j * (-(Real.exp (-1) * gompertzConstant)) ^ (b.1 - j) *
          (b.1.choose j : ℝ)) =
        (((-1 : ℚ) ^ (b.1 - j) * (b.1.choose j : ℚ)) : ℚ) •
          (Real.eulerMascheroniConstant ^ j * gompertzConstant ^ (b.1 - j) * Real.exp (-(k.1 : ℝ))) := by
      have hexp_pow : (Real.exp (-1)) ^ (b.1 - j) = Real.exp (-((b.1 - j : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have hexp_mul : Real.exp (-(a.1 : ℝ)) * Real.exp (-((b.1 - j : ℕ) : ℝ)) = Real.exp (-(k.1 : ℝ)) := by
        rw [← Real.exp_add]; simp only [k, Nat.cast_add]; ring_nf
      have hneg : (-(Real.exp (-1) * gompertzConstant)) ^ (b.1 - j) =
          (-1 : ℝ) ^ (b.1 - j) * (Real.exp (-1)) ^ (b.1 - j) * gompertzConstant ^ (b.1 - j) := by
        rw [show -(Real.exp (-1) * gompertzConstant) = (-1) * Real.exp (-1) * gompertzConstant by ring,
          mul_pow, mul_pow]
      rw [hneg, hexp_pow, Algebra.smul_def, eq_ratCast]
      push_cast
      calc Real.exp (-(a.1 : ℝ)) *
            (Real.eulerMascheroniConstant ^ j *
              ((-1 : ℝ) ^ (b.1 - j) * Real.exp (-((b.1 - j : ℕ) : ℝ)) * gompertzConstant ^ (b.1 - j)) *
              (b.1.choose j : ℝ))
          = ((-1 : ℝ) ^ (b.1 - j) * (b.1.choose j : ℝ)) *
              (Real.eulerMascheroniConstant ^ j * gompertzConstant ^ (b.1 - j) *
                (Real.exp (-(a.1 : ℝ)) * Real.exp (-((b.1 - j : ℕ) : ℝ)))) := by ring
        _ = _ := by rw [hexp_mul]
    rw [hval]
    exact Submodule.smul_mem W _ (hpow_mem j (b.1 - j) k)
  let f : Idx n → W := fun p => ⟨Real.exp (-(p.1.1.1 : ℝ)) * (Ein 1) ^ p.1.2.1, hmemW p⟩
  have hgt : Module.finrank ℚ W < Fintype.card (Idx n) := by
    rw [card_idx]
    have hcalc : (n + 1) * (n + 2) / 2 = (2 * d + 1) * (d + 1) := by
      dsimp [n]
      have : (2 * d + 1) * (2 * d + 2) = 2 * ((2 * d + 1) * (d + 1)) := by ring
      omega
    rw [hcalc]
    have hmul : d * (n + 1) = d * (2 * d + 1) := rfl
    nlinarith [hW_dim]
  have hdep : ¬ LinearIndependent ℚ f := fun hli =>
    not_lt_of_ge (hli.fintype_card_le_finrank) hgt
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hgsum, p0, hp0⟩ := hdep
  let D : ℕ := ∏ p : Idx n, (g p).den
  have hDpos : (0 : ℚ) < D := by
    exact_mod_cast Finset.prod_pos fun p _ => (g p).pos
  let c : Idx n → ℤ := fun p => (D * g p).num
  have hc_eq : ∀ p : Idx n, (c p : ℚ) = (D : ℚ) * g p := by
    intro p
    have hdvd : (g p).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
    obtain ⟨m, hm⟩ := hdvd
    have hq : (D : ℚ) * g p = ((m : ℤ) * (g p).num : ℤ) := by
      rw [hm, Nat.cast_mul, mul_comm ((g p).den : ℚ), mul_assoc, mul_comm ((g p).den : ℚ),
        Rat.mul_den_eq_num]
      push_cast; ring
    simp only [c, hq, Rat.num_intCast]
  refine ⟨n, c, ⟨p0, ?_⟩, ?_⟩
  · intro hc0
    have hq0 : (D : ℚ) * g p0 = 0 := by rw [← hc_eq p0, hc0, Int.cast_zero]
    exact hp0 ((mul_eq_zero.mp hq0).resolve_left hDpos.ne')
  · have hsumW : (∑ p : Idx n, (g p : ℝ) * (f p : ℝ)) = 0 := by
      have h := congrArg (fun x : W => (x : ℝ)) hgsum
      simpa [Submodule.coe_sum, Algebra.smul_def] using h
    have hmul := congrArg (fun x : ℝ => (D : ℝ) * x) hsumW
    rw [mul_zero, Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hcR : (c p : ℝ) = (D : ℝ) * (g p : ℝ) := by exact_mod_cast hc_eq p
    rw [hcR, mul_assoc]

/- ### Section 3: Power series E-function system, ODE, bounds, and ℝ[X]-linear independence -/

noncomputable def expNegQ (a : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => (-(a : ℚ)) ^ k / (k.factorial : ℚ)

noncomputable def einQ : PowerSeries ℚ :=
  PowerSeries.mk fun k =>
    if k = 0 then 0 else (-1 : ℚ) ^ (k - 1) / ((k : ℚ) * (k.factorial : ℚ))

noncomputable def fQ {n : ℕ} (p : Idx n) : PowerSeries ℚ :=
  expNegQ p.1.1.1 * einQ ^ p.1.2.1

noncomputable def cQ {n : ℕ} (p : Idx n) (k : ℕ) : ℚ :=
  (k.factorial : ℚ) * PowerSeries.coeff k (fQ p)

noncomputable def expNegPS (a : ℕ) : PowerSeries ℝ :=
  PowerSeries.map (Rat.castHom ℝ) (expNegQ a)

noncomputable def einPS : PowerSeries ℝ :=
  PowerSeries.map (Rat.castHom ℝ) einQ

noncomputable def fPS {n : ℕ} (p : Idx n) : PowerSeries ℝ :=
  PowerSeries.map (Rat.castHom ℝ) (fQ p)

lemma fPS_eq_mul_pow {n : ℕ} (p : Idx n) :
    fPS p = expNegPS p.1.1.1 * einPS ^ p.1.2.1 := by
  simp [fPS, fQ, expNegPS, einPS, map_mul, map_pow]

lemma coeff_expNegQ (a k : ℕ) :
    PowerSeries.coeff k (expNegQ a) = (-(a : ℚ)) ^ k / (k.factorial : ℚ) := by
  simp [expNegQ]

lemma coeff_einQ (k : ℕ) :
    PowerSeries.coeff k einQ =
      if k = 0 then 0 else (-1 : ℚ) ^ (k - 1) / ((k : ℚ) * (k.factorial : ℚ)) := by
  simp [einQ]

lemma coeff_expNegPS (a k : ℕ) :
    PowerSeries.coeff k (expNegPS a) = (-(a : ℝ)) ^ k / (k.factorial : ℝ) := by
  simp [expNegPS, coeff_expNegQ]

lemma coeff_einPS (k : ℕ) :
    PowerSeries.coeff k einPS =
      if k = 0 then 0 else (-1 : ℝ) ^ (k - 1) / ((k : ℝ) * (k.factorial : ℝ)) := by
  simp only [einPS, PowerSeries.coeff_map, coeff_einQ, Rat.coe_castHom]
  split_ifs <;> simp

lemma coeff_fPS_eq_cQ {n : ℕ} (p : Idx n) (k : ℕ) :
    PowerSeries.coeff k (fPS p) = (cQ p k : ℝ) / (k.factorial : ℝ) := by
  simp only [fPS, cQ, PowerSeries.coeff_map, Rat.coe_castHom, Rat.cast_mul, Rat.cast_natCast]
  have hf : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hf]

lemma expNegQ_add (a b : ℕ) : expNegQ a * expNegQ b = expNegQ (a + b) := by
  ext k
  rw [PowerSeries.coeff_mul, coeff_expNegQ]
  simp_rw [coeff_expNegQ]
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  rw [mul_div_cancel₀ _ hf, Finset.mul_sum]
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
      (k.factorial : ℚ) * ((-(a : ℚ)) ^ x.1 / (x.1.factorial : ℚ) *
        ((-(b : ℚ)) ^ x.2 / (x.2.factorial : ℚ))) =
      (-(a : ℚ)) ^ x.1 * (-(b : ℚ)) ^ x.2 * (k.choose x.1 : ℚ) := by
    intro ⟨i, j⟩ hij
    have hsum : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hch : (k.choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) = (k.factorial : ℚ) := by
      have hnat := Nat.choose_mul_factorial_mul_factorial (show i ≤ k by omega)
      rw [show k - i = j by omega] at hnat
      exact_mod_cast hnat
    have hi : (i.factorial : ℚ) ≠ 0 := by positivity
    have hj : (j.factorial : ℚ) ≠ 0 := by positivity
    rw [← hch]
    field_simp [hi, hj]
  rw [Finset.sum_congr rfl hterm, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← add_pow (-(a : ℚ)) (-(b : ℚ)) k]
  push_cast
  ring

lemma expNegPS_add (a b : ℕ) : expNegPS a * expNegPS b = expNegPS (a + b) := by
  simp only [expNegPS, ← map_mul, expNegQ_add]

lemma expNegPS_zero : expNegPS 0 = 1 := by
  ext k
  rw [coeff_expNegPS]
  cases k with
  | zero => simp
  | succ k => simp

lemma expNegPS_pow (a : ℕ) : expNegPS a = (expNegPS 1) ^ a := by
  induction a with
  | zero => simp [expNegPS_zero]
  | succ a ih => rw [pow_succ, ← ih, expNegPS_add]

lemma fPS_zero {n : ℕ} :
    fPS (⟨(⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩), Nat.zero_le n⟩ : Idx n) = 1 := by
  simp [fPS_eq_mul_pow, expNegPS_zero]

/- Denominator and size bounds on `cQ p k`. -/

lemma lcmUpto_le_pow (N : ℕ) : Nat.lcmUpto N ≤ 256 ^ N := by
  have hlog : Real.log (Nat.lcmUpto N : ℝ) ≤ Real.log ((256 : ℝ) ^ N) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto, Real.log_pow]
    have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
    have h4 : Real.log 4 + 4 ≤ Real.log 256 := by
      have h256 : Real.log 256 = 4 * Real.log 4 := by
        rw [show (256 : ℝ) = 4 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
      have hlog4 : (4 : ℝ) / 3 ≤ Real.log 4 := by
        have h2 := Real.log_two_gt_d9
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
    have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hpos1 : (0 : ℝ) < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  have hpos2 : (0 : ℝ) < (256 : ℝ) ^ N := by positivity
  have hleR := (Real.log_le_log_iff hpos1 hpos2).mp hlog
  exact_mod_cast hleR

lemma denom_and_bound_expNeg_ein_pow (a b N : ℕ) :
    ∀ k ≤ N,
      (∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto N : ℚ) ^ b) *
        ((k.factorial : ℚ) * PowerSeries.coeff k (expNegQ a * einQ ^ b))) ∧
      |(k.factorial : ℚ) * PowerSeries.coeff k (expNegQ a * einQ ^ b)| ≤ ((a + b : ℕ) : ℚ) ^ k := by
  induction b with
  | zero =>
    intro k _
    simp only [pow_zero, mul_one, one_mul, coeff_expNegQ, Nat.add_zero]
    have hf : (k.factorial : ℚ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hf]
    refine ⟨⟨(-(a : ℤ)) ^ k, by push_cast; rfl⟩, ?_⟩
    rw [abs_pow, abs_neg, abs_of_nonneg (Nat.cast_nonneg a)]
  | succ b ih =>
    intro k hkN
    have hexp_split : expNegQ a * einQ ^ (b + 1) = (expNegQ a * einQ ^ b) * einQ := by
      rw [pow_succ, mul_assoc]
    rw [hexp_split, PowerSeries.coeff_mul, Finset.mul_sum]
    have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
        (k.factorial : ℚ) * (PowerSeries.coeff x.1 (expNegQ a * einQ ^ b) * PowerSeries.coeff x.2 einQ) =
          (k.choose x.1 : ℚ) *
            ((x.1.factorial : ℚ) * PowerSeries.coeff x.1 (expNegQ a * einQ ^ b)) *
            ((x.2.factorial : ℚ) * PowerSeries.coeff x.2 einQ) := by
      intro ⟨i, j⟩ hij
      have hsum : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hch : (k.choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) = (k.factorial : ℚ) := by
        have hnat := Nat.choose_mul_factorial_mul_factorial (show i ≤ k by omega)
        rw [show k - i = j by omega] at hnat
        exact_mod_cast hnat
      rw [← hch]; ring
    rw [Finset.sum_congr rfl hterm]
    constructor
    · rw [Finset.mul_sum]
      have hterm_int : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
          ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto N : ℚ) ^ (b + 1)) *
            ((k.choose x.1 : ℚ) *
              ((x.1.factorial : ℚ) * PowerSeries.coeff x.1 (expNegQ a * einQ ^ b)) *
              ((x.2.factorial : ℚ) * PowerSeries.coeff x.2 einQ)) := by
        intro ⟨i, j⟩ hij
        have hsum : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        obtain ⟨z1, hz1⟩ := (ih i (by omega)).1
        by_cases hj : j = 0
        · refine ⟨0, ?_⟩
          simp [hj, coeff_einQ]
        · have hjpos : 1 ≤ j := Nat.pos_of_ne_zero hj
          have hdvd : j ∣ Nat.lcmUpto N := by
            unfold Nat.lcmUpto
            exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hjpos, by omega⟩)
          obtain ⟨q, hq⟩ := hdvd
          have hjein : (Nat.lcmUpto N : ℚ) * ((j.factorial : ℚ) * PowerSeries.coeff j einQ) =
              (((-1 : ℤ) ^ (j - 1) * (q : ℤ)) : ℚ) := by
            rw [coeff_einQ, if_neg hj]
            have hfj : (j.factorial : ℚ) ≠ 0 := by positivity
            have hjQ : (j : ℚ) ≠ 0 := by positivity
            have hqQ : (Nat.lcmUpto N : ℚ) = (j : ℚ) * (q : ℚ) := by exact_mod_cast hq
            rw [hqQ]
            push_cast
            field_simp [hfj, hjQ]
          refine ⟨(k.choose i : ℤ) * z1 * ((-1 : ℤ) ^ (j - 1) * (q : ℤ)), ?_⟩
          rw [pow_succ]
          calc (((k.choose i : ℤ) * z1 * ((-1 : ℤ) ^ (j - 1) * (q : ℤ)) : ℤ) : ℚ)
              = (k.choose i : ℚ) * (z1 : ℚ) * (((-1 : ℤ) ^ (j - 1) * (q : ℤ)) : ℚ) := by push_cast; ring
            _ = (k.choose i : ℚ) *
                  ((Nat.lcmUpto N : ℚ) ^ b * ((i.factorial : ℚ) * PowerSeries.coeff i (expNegQ a * einQ ^ b))) *
                  ((Nat.lcmUpto N : ℚ) * ((j.factorial : ℚ) * PowerSeries.coeff j einQ)) := by
                rw [hz1, hjein]
            _ = _ := by ring
      choose zf hzf using hterm_int
      refine ⟨∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, zf x.1 x.2, ?_⟩
      rw [Int.cast_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k)
        (fun x => ((Nat.lcmUpto N : ℚ) ^ (b + 1)) *
          ((k.choose x.1 : ℚ) *
            ((x.1.factorial : ℚ) * PowerSeries.coeff x.1 (expNegQ a * einQ ^ b)) *
            ((x.2.factorial : ℚ) * PowerSeries.coeff x.2 einQ)))]
      exact Finset.sum_congr rfl fun x _ => hzf x.1 x.2
    · calc |∑ x ∈ Finset.HasAntidiagonal.antidiagonal k,
              (k.choose x.1 : ℚ) *
                ((x.1.factorial : ℚ) * PowerSeries.coeff x.1 (expNegQ a * einQ ^ b)) *
                ((x.2.factorial : ℚ) * PowerSeries.coeff x.2 einQ)|
          ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k,
              |(k.choose x.1 : ℚ) *
                ((x.1.factorial : ℚ) * PowerSeries.coeff x.1 (expNegQ a * einQ ^ b)) *
                ((x.2.factorial : ℚ) * PowerSeries.coeff x.2 einQ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, ((a + b : ℕ) : ℚ) ^ x.1 * (1 : ℚ) ^ x.2 * (k.choose x.1 : ℚ) := by
            refine Finset.sum_le_sum fun ⟨i, j⟩ hij => ?_
            dsimp only
            have hsum : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
            have h1 := (ih i (by omega)).2
            have h2 : |(j.factorial : ℚ) * PowerSeries.coeff j einQ| ≤ 1 := by
              rw [coeff_einQ]
              split_ifs with hj
              · simp
              · have hfj : (j.factorial : ℚ) ≠ 0 := by positivity
                have hj1 : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hj
                have heq : (j.factorial : ℚ) * ((-1 : ℚ) ^ (j - 1) / ((j : ℚ) * (j.factorial : ℚ))) =
                    (-1 : ℚ) ^ (j - 1) / (j : ℚ) := by field_simp [hfj]
                rw [heq, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (Nat.cast_nonneg j)]
                exact div_le_one_of_le₀ hj1 (Nat.cast_nonneg j)
            rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), one_pow, mul_one]
            have hnn1 : 0 ≤ ((a + b : ℕ) : ℚ) ^ i := by positivity
            have hnn2 : 0 ≤ (k.choose i : ℚ) := Nat.cast_nonneg _
            calc (k.choose i : ℚ) *
                  |(i.factorial : ℚ) * PowerSeries.coeff i (expNegQ a * einQ ^ b)| *
                  |(j.factorial : ℚ) * PowerSeries.coeff j einQ|
                ≤ (k.choose i : ℚ) * ((a + b : ℕ) : ℚ) ^ i * 1 := by
                  have h12 : (k.choose i : ℚ) *
                      |(i.factorial : ℚ) * PowerSeries.coeff i (expNegQ a * einQ ^ b)| ≤
                      (k.choose i : ℚ) * ((a + b : ℕ) : ℚ) ^ i :=
                    mul_le_mul_of_nonneg_left h1 hnn2
                  exact mul_le_mul h12 h2 (abs_nonneg _) (mul_nonneg hnn2 hnn1)
              _ = ((a + b : ℕ) : ℚ) ^ i * (k.choose i : ℚ) := by ring
        _ = ((a + (b + 1) : ℕ) : ℚ) ^ k := by
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← add_pow]
            push_cast; ring

lemma cQ_denom_int {n : ℕ} (p : Idx n) {k N : ℕ} (hk : k ≤ N) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto N : ℚ) ^ n) * cQ p k := by
  obtain ⟨z0, hz0⟩ := (denom_and_bound_expNeg_ein_pow p.1.1.1 p.1.2.1 N k hk).1
  have hbn : p.1.2.1 ≤ n := by have := p.2; omega
  refine ⟨z0 * (Nat.lcmUpto N : ℤ) ^ (n - p.1.2.1), ?_⟩
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hz0, cQ, fQ]
  rw [mul_comm _ ((Nat.lcmUpto N : ℚ) ^ (n - p.1.2.1)), ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hbn]

lemma cQ_abs_le {n : ℕ} (p : Idx n) (k : ℕ) :
    |cQ p k| ≤ ((n : ℚ) + 1) ^ k := by
  have h := (denom_and_bound_expNeg_ein_pow p.1.1.1 p.1.2.1 k k le_rfl).2
  have hle : ((p.1.1.1 + p.1.2.1 : ℕ) : ℚ) ≤ (n : ℚ) + 1 := by
    have : p.1.1.1 + p.1.2.1 ≤ n := p.2
    exact_mod_cast (by omega : p.1.1.1 + p.1.2.1 ≤ n + 1)
  exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hle k)

/- Convergence at `z = 1`: `HasSum (fun k => PowerSeries.coeff k (fPS p)) (fVal p)`. -/

noncomputable def fVal {n : ℕ} (p : Idx n) : ℝ :=
  Real.exp (-(p.1.1.1 : ℝ)) * (Ein 1) ^ p.1.2.1

lemma hasSum_coeff_expNegPS (a : ℕ) :
    HasSum (fun k : ℕ => PowerSeries.coeff k (expNegPS a)) (Real.exp (-(a : ℝ))) := by
  simp_rw [coeff_expNegPS]
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact (Real.summable_pow_div_factorial (-(a : ℝ))).hasSum

lemma hasSum_coeff_einPS :
    HasSum (fun k : ℕ => PowerSeries.coeff k einPS) (Ein 1) := by
  have hs := summable_einTerm 1
  have h1 : HasSum (einTerm 1) (Ein 1) := hs.hasSum
  have hshift : HasSum (fun k : ℕ => if k = 0 then (0 : ℝ) else einTerm 1 (k - 1)) (Ein 1) := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]
    · have ht := h1.tendsto_sum_nat
      have heq : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1),
          if k = 0 then (0 : ℝ) else einTerm 1 (k - 1)) = ∑ k ∈ Finset.range N, einTerm 1 k := by
        intro N
        rw [Finset.sum_range_succ']
        simp
      exact (tendsto_add_atTop_iff_nat 1).mp (ht.congr (fun N => (heq N).symm))
    · have hs1 : Summable (fun k : ℕ => ‖einTerm 1 k‖) := hs.norm
      rw [← summable_nat_add_iff 1]
      simpa using hs1
  refine hshift.congr_fun fun k => ?_
  rw [coeff_einPS]
  cases k with
  | zero => simp
  | succ k => simp [einTerm]

/- Formal Euler derivation `D_ps(f) = z f'(z)` and ODE `D_ps(fPS p) = ∑ q, Amat p q * fPS q`. -/

noncomputable def Dps (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => (k : ℝ) * PowerSeries.coeff k f

lemma coeff_Dps (f : PowerSeries ℝ) (k : ℕ) :
    PowerSeries.coeff k (Dps f) = (k : ℝ) * PowerSeries.coeff k f := by
  simp [Dps]

lemma Dps_add (f g : PowerSeries ℝ) : Dps (f + g) = Dps f + Dps g := by
  ext k; simp [coeff_Dps, mul_add]

lemma Dps_smul (c : ℝ) (f : PowerSeries ℝ) : Dps (c • f) = c • Dps f := by
  ext k; simp [coeff_Dps]; ring

lemma Dps_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) :
    Dps (∑ i ∈ s, f i) = ∑ i ∈ s, Dps (f i) := by
  ext k; simp [coeff_Dps, Finset.mul_sum]

lemma Dps_mul (f g : PowerSeries ℝ) : Dps (f * g) = Dps f * g + f * Dps g := by
  ext k
  rw [coeff_Dps, PowerSeries.coeff_mul, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
  have hsum : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  simp only [coeff_Dps, ← hsum, Nat.cast_add]
  ring

lemma Dps_one : Dps 1 = 0 := by
  ext k
  cases k <;> simp [coeff_Dps, PowerSeries.coeff_one]

lemma Dps_pow (f : PowerSeries ℝ) (b : ℕ) :
    Dps (f ^ b) = match b with | 0 => 0 | b' + 1 => ((b' + 1 : ℕ) : ℝ) • (f ^ b' * Dps f) := by
  induction b with
  | zero => simp [Dps_one]
  | succ b ih =>
    rw [pow_succ, Dps_mul]
    cases b with
    | zero => simp [Dps_one]
    | succ b' =>
      rw [ih]
      ext k
      simp only [map_add, PowerSeries.coeff_smul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
      have h1 : (b' + 1 : ℝ) • (f ^ b' * Dps f) * f = (b' + 1 : ℝ) • (f ^ (b' + 1) * Dps f) := by
        rw [smul_mul_assoc, pow_succ]; ring_nf
      rw [h1]
      simp only [PowerSeries.coeff_smul, smul_eq_mul]
      ring

lemma Dps_poly (P : ℝ[X]) :
    Dps (P : PowerSeries ℝ) = ((Polynomial.X * P.derivative : ℝ[X]) : PowerSeries ℝ) := by
  ext k
  rw [coeff_Dps, Polynomial.coeff_coe, Polynomial.coeff_coe]
  cases k with
  | zero => simp
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

lemma Dps_expNegPS (a : ℕ) :
    Dps (expNegPS a) = (-(a : ℝ)) • (PowerSeries.X * expNegPS a) := by
  ext k
  rw [coeff_Dps, PowerSeries.coeff_smul, smul_eq_mul, coeff_expNegPS]
  cases k with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_expNegPS]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hk, hfk]

lemma Dps_einPS : Dps einPS = 1 - expNegPS 1 := by
  ext k
  rw [coeff_Dps, map_sub, PowerSeries.coeff_one, coeff_expNegPS, coeff_einPS]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_sub]
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfk : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [pow_succ']
    field_simp [hk, hfk]
    ring

/-- The polynomial ODE matrix `Amat n : Matrix (Idx n) (Idx n) ℤ[X]` satisfying `z F' = A(z) F`. -/
noncomputable def AmatZ (n : ℕ) : Matrix (Idx n) (Idx n) ℤ[X] :=
  fun p q =>
    (if p = q then -(p.1.1.1 : ℤ[X]) * Polynomial.X else 0) +
    (if q.1.1.1 = p.1.1.1 ∧ q.1.2.1 + 1 = p.1.2.1 then (p.1.2.1 : ℤ[X]) else 0) +
    (if q.1.1.1 = p.1.1.1 + 1 ∧ q.1.2.1 + 1 = p.1.2.1 then -(p.1.2.1 : ℤ[X]) else 0)

noncomputable def AmatR (n : ℕ) : Matrix (Idx n) (Idx n) ℝ[X] :=
  (AmatZ n).map (Polynomial.map (Int.castRingHom ℝ))

lemma poly_coe_natCast (a : ℕ) : (((a : ℝ[X]) : PowerSeries ℝ)) = PowerSeries.C (a : ℝ) := by
  rw [← Polynomial.C_eq_natCast, Polynomial.coe_C]

lemma poly_coe_intCast (c : ℤ) : (((c : ℝ[X]) : PowerSeries ℝ)) = PowerSeries.C (c : ℝ) := by
  rw [← map_intCast (Polynomial.C : ℝ →+* ℝ[X]), Polynomial.coe_C]

lemma Dps_fPS {n : ℕ} (p : Idx n) :
    Dps (fPS p) = ∑ q : Idx n, ((AmatR n p q : ℝ[X]) : PowerSeries ℝ) * fPS q := by
  rcases p with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
  have hab' : a + b ≤ n := hab
  rw [fPS_eq_mul_pow, Dps_mul, Dps_expNegPS]
  have hdiag : (-(a : ℝ)) • (PowerSeries.X * expNegPS a) * einPS ^ b =
      ((-(a : ℝ[X]) * Polynomial.X : ℝ[X]) : PowerSeries ℝ) *
        fPS ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩ := by
    rw [fPS_eq_mul_pow]
    have hpoly : ((-(a : ℝ[X]) * Polynomial.X : ℝ[X]) : PowerSeries ℝ) =
        (-(a : ℝ)) • PowerSeries.X := by
      rw [Polynomial.coe_mul, Polynomial.coe_neg, poly_coe_natCast, Polynomial.coe_X,
        Algebra.smul_def, PowerSeries.C_eq_algebraMap, map_neg]
    rw [hpoly, smul_mul_assoc, smul_mul_assoc, mul_assoc]
  have hterm2 : expNegPS a * Dps (einPS ^ b) =
      ∑ q : Idx n,
        (((if q.1.1.1 = a ∧ q.1.2.1 + 1 = b then (b : ℝ[X]) else 0) +
          (if q.1.1.1 = a + 1 ∧ q.1.2.1 + 1 = b then -(b : ℝ[X]) else 0) : ℝ[X]) : PowerSeries ℝ) *
          fPS q := by
    cases b with
    | zero =>
      simp [Dps_one]
    | succ b' =>
      have hb' : a + (b' + 1) ≤ n := hab'
      rw [Dps_pow, Dps_einPS]
      let q1 : Idx n := ⟨(⟨a, ha⟩, ⟨b', by omega⟩), by dsimp; omega⟩
      let q2 : Idx n := ⟨(⟨a + 1, by omega⟩, ⟨b', by omega⟩), by dsimp; omega⟩
      have hq1_only : ∀ q : Idx n, (q.1.1.1 = a ∧ q.1.2.1 + 1 = b' + 1) ↔ q = q1 := by
        intro ⟨⟨⟨qa, _⟩, ⟨qb, _⟩⟩, _⟩
        simp only [q1, Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq]
        omega
      have hq2_only : ∀ q : Idx n, (q.1.1.1 = a + 1 ∧ q.1.2.1 + 1 = b' + 1) ↔ q = q2 := by
        intro ⟨⟨⟨qa, _⟩, ⟨qb, _⟩⟩, _⟩
        simp only [q2, Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq]
        omega
      simp_rw [hq1_only, hq2_only, Polynomial.coe_add, add_mul, Finset.sum_add_distrib]
      have hs1 : ∑ q : Idx n, ((if q = q1 then ((b' + 1 : ℕ) : ℝ[X]) else 0 : ℝ[X]) : PowerSeries ℝ) * fPS q =
          (((b' + 1 : ℕ) : ℝ[X]) : PowerSeries ℝ) * fPS q1 := by
        rw [Finset.sum_eq_single q1]
        · simp
        · intro q _ hq; simp [hq]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hs2 : ∑ q : Idx n, ((if q = q2 then -((b' + 1 : ℕ) : ℝ[X]) else 0 : ℝ[X]) : PowerSeries ℝ) * fPS q =
          ((-((b' + 1 : ℕ) : ℝ[X]) : ℝ[X]) : PowerSeries ℝ) * fPS q2 := by
        rw [Finset.sum_eq_single q2]
        · simp
        · intro q _ hq; simp [hq]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hs1, hs2, fPS_eq_mul_pow, fPS_eq_mul_pow]
      simp only [q1, q2]
      have he1 : expNegPS (a + 1) = expNegPS a * expNegPS 1 := (expNegPS_add a 1).symm
      rw [he1]
      have hcoe1 : ((((b' + 1 : ℕ) : ℝ[X]) : PowerSeries ℝ)) = PowerSeries.C ((b' + 1 : ℕ) : ℝ) :=
        poly_coe_natCast (b' + 1)
      have hcoe2 : (((-((b' + 1 : ℕ) : ℝ[X]) : ℝ[X]) : PowerSeries ℝ)) =
          -PowerSeries.C ((b' + 1 : ℕ) : ℝ) := by
        rw [Polynomial.coe_neg, poly_coe_natCast]
      rw [hcoe1, hcoe2, Algebra.smul_def]
      change expNegPS a * (PowerSeries.C ((b' + 1 : ℕ) : ℝ) * (einPS ^ b' * (1 - expNegPS 1))) =
        PowerSeries.C ((b' + 1 : ℕ) : ℝ) * (expNegPS a * einPS ^ b') +
        (-PowerSeries.C ((b' + 1 : ℕ) : ℝ)) * (expNegPS a * expNegPS 1 * einPS ^ b')
      ring
  have hsum_all : ∑ q : Idx n, ((AmatR n ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩ q : ℝ[X]) : PowerSeries ℝ) * fPS q =
      ((-(a : ℝ[X]) * Polynomial.X : ℝ[X]) : PowerSeries ℝ) * fPS ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩ +
      ∑ q : Idx n,
        (((if q.1.1.1 = a ∧ q.1.2.1 + 1 = b then (b : ℝ[X]) else 0) +
          (if q.1.1.1 = a + 1 ∧ q.1.2.1 + 1 = b then -(b : ℝ[X]) else 0) : ℝ[X]) : PowerSeries ℝ) *
          fPS q := by
    have hEntry : ∀ q : Idx n,
        AmatR n ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩ q =
          (if (⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩ : Idx n) = q then -(a : ℝ[X]) * Polynomial.X else 0) +
          ((if q.1.1.1 = a ∧ q.1.2.1 + 1 = b then (b : ℝ[X]) else 0) +
           (if q.1.1.1 = a + 1 ∧ q.1.2.1 + 1 = b then -(b : ℝ[X]) else 0)) := by
      intro q
      simp only [AmatR, Matrix.map_apply, AmatZ]
      rw [Polynomial.map_add, Polynomial.map_add, add_assoc]
      congr 1
      · split_ifs <;> simp
      · congr 1
        · split_ifs <;> simp
        · split_ifs <;> simp
    simp_rw [hEntry, Polynomial.coe_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩ : Idx n)]
    · simp
    · intro q _ hq; simp [Ne.symm hq]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum_all, ← hdiag, ← hterm2]

lemma AmatR_natDegree_le_one (n : ℕ) (p q : Idx n) :
    (AmatR n p q).natDegree ≤ 1 := by
  have h1 : (AmatZ n p q).natDegree ≤ 1 := by
    unfold AmatZ
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · split_ifs
        · exact (Polynomial.natDegree_mul_le).trans (by simp [Polynomial.natDegree_natCast])
        · simp
      · split_ifs <;> simp [Polynomial.natDegree_natCast]
    · split_ifs <;> simp [Polynomial.natDegree_natCast]
  exact Polynomial.natDegree_map_le.trans h1

lemma AmatR_eval_zero_nilpotent (n : ℕ) :
    ((AmatR n).map (Polynomial.eval 0)) ^ (n + 1) = 0 := by
  let A0 : Matrix (Idx n) (Idx n) ℝ := (AmatR n).map (Polynomial.eval 0)
  have hstep : ∀ k : ℕ, ∀ p q : Idx n, (A0 ^ k) p q ≠ 0 → q.1.2.1 + k = p.1.2.1 := by
    intro k
    induction k with
    | zero =>
      intro p q h
      simp only [pow_zero, Matrix.one_apply] at h
      split_ifs at h with hpq
      · subst hpq; omega
      · exact absurd rfl h
    | succ k ih =>
      intro p q h
      rw [pow_succ, Matrix.mul_apply] at h
      have hex : ∃ r : Idx n, (A0 ^ k) p r * A0 r q ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h (Finset.sum_eq_zero fun r _ => hall r)
      obtain ⟨r, hr⟩ := hex
      have hr1 : (A0 ^ k) p r ≠ 0 := left_ne_zero_of_mul hr
      have hr2 : A0 r q ≠ 0 := right_ne_zero_of_mul hr
      have h1 := ih p r hr1
      have h2 : q.1.2.1 + 1 = r.1.2.1 := by
        by_contra hne
        have hzero : A0 r q = 0 := by
          simp only [A0, Matrix.map_apply, AmatR, AmatZ]
          rw [Polynomial.map_add, Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add]
          have ht1 : Polynomial.eval 0 (Polynomial.map (Int.castRingHom ℝ)
              (if r = q then -(r.1.1.1 : ℤ[X]) * Polynomial.X else 0)) = 0 := by
            split_ifs <;> simp
          have ht2 : Polynomial.eval 0 (Polynomial.map (Int.castRingHom ℝ)
              (if q.1.1.1 = r.1.1.1 ∧ q.1.2.1 + 1 = r.1.2.1 then (r.1.2.1 : ℤ[X]) else 0)) = 0 := by
            rw [if_neg (fun hc => hne hc.2)]; simp
          have ht3 : Polynomial.eval 0 (Polynomial.map (Int.castRingHom ℝ)
              (if q.1.1.1 = r.1.1.1 + 1 ∧ q.1.2.1 + 1 = r.1.2.1 then -(r.1.2.1 : ℤ[X]) else 0)) = 0 := by
            rw [if_neg (fun hc => hne hc.2)]; simp
          linarith
        exact hr2 hzero
      omega
  ext p q
  simp only [Matrix.zero_apply]
  by_contra hne
  have heq := hstep (n + 1) p q hne
  have hpn : p.1.2.1 ≤ n := by have := p.2; omega
  omega

/- Cauchy product convergence at `z = 1` for `fPS p` and polynomial combinations. -/

lemma summable_norm_coeff_mul {f g : PowerSeries ℝ}
    (hf : Summable fun k => ‖PowerSeries.coeff k f‖)
    (hg : Summable fun k => ‖PowerSeries.coeff k g‖) :
    Summable fun k => ‖PowerSeries.coeff k (f * g)‖ := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  refine h.congr fun k => ?_
  rw [PowerSeries.coeff_mul]

lemma hasSum_coeff_mul {f g : PowerSeries ℝ} {a b : ℝ}
    (hf : HasSum (fun k => PowerSeries.coeff k f) a)
    (hg : HasSum (fun k => PowerSeries.coeff k g) b)
    (hfn : Summable fun k => ‖PowerSeries.coeff k f‖)
    (hgn : Summable fun k => ‖PowerSeries.coeff k g‖) :
    HasSum (fun k => PowerSeries.coeff k (f * g)) (a * b) := by
  have hts := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at hts
  have hs : Summable fun k => PowerSeries.coeff k (f * g) :=
    (summable_norm_coeff_mul hfn hgn).of_norm
  have heq : (∑' k, PowerSeries.coeff k (f * g)) = a * b := by
    rw [hts]
    congr 1
    ext k
    rw [PowerSeries.coeff_mul]
  rw [← heq]
  exact hs.hasSum

lemma summable_norm_coeff_expNegPS (a : ℕ) :
    Summable fun k => ‖PowerSeries.coeff k (expNegPS a)‖ := by
  have h := Real.summable_pow_div_factorial (a : ℝ)
  refine h.congr fun k => ?_
  rw [coeff_expNegPS, Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg a), abs_of_nonneg (Nat.cast_nonneg k.factorial)]

lemma summable_norm_coeff_einPS :
    Summable fun k => ‖PowerSeries.coeff k einPS‖ := by
  have h : Summable fun k => ‖PowerSeries.coeff k (expNegPS 1)‖ := summable_norm_coeff_expNegPS 1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) h
  rw [coeff_einPS, coeff_expNegPS]
  split_ifs with hk
  · simp
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hfk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [abs_div, abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hfk.le, Nat.cast_one, abs_neg, abs_one, one_pow]
    have hmul : (k.factorial : ℝ) ≤ (k : ℝ) * (k.factorial : ℝ) := by nlinarith
    exact div_le_div_of_nonneg_left zero_le_one hfk hmul

lemma hasSum_and_summable_norm_coeff_fPS {n : ℕ} (p : Idx n) :
    HasSum (fun k => PowerSeries.coeff k (fPS p)) (fVal p) ∧
    Summable (fun k => ‖PowerSeries.coeff k (fPS p)‖) := by
  rw [fPS_eq_mul_pow, fVal]
  suffices ∀ b : ℕ,
      HasSum (fun k => PowerSeries.coeff k (einPS ^ b)) ((Ein 1) ^ b) ∧
      Summable (fun k => ‖PowerSeries.coeff k (einPS ^ b)‖) by
    obtain ⟨hb1, hb2⟩ := this p.1.2.1
    exact ⟨hasSum_coeff_mul (hasSum_coeff_expNegPS p.1.1.1) hb1
        (summable_norm_coeff_expNegPS p.1.1.1) hb2,
      summable_norm_coeff_mul (summable_norm_coeff_expNegPS p.1.1.1) hb2⟩
  intro b
  induction b with
  | zero =>
    constructor
    · rw [pow_zero, pow_zero]
      have h1 : (fun k : ℕ => PowerSeries.coeff k (1 : PowerSeries ℝ)) =
          fun k => if k = 0 then (1 : ℝ) else 0 := by
        ext k; rw [PowerSeries.coeff_one]
      rw [h1]
      exact hasSum_ite_eq 0 1
    · rw [pow_zero]
      refine (summable_of_ne_finset_zero (s := {0}) fun k hk => ?_)
      simp only [Finset.mem_singleton] at hk
      simp [PowerSeries.coeff_one, hk]
  | succ b ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hasSum_coeff_mul ih.1 hasSum_coeff_einPS ih.2 summable_norm_coeff_einPS,
      summable_norm_coeff_mul ih.2 summable_norm_coeff_einPS⟩

lemma hasSum_coeff_poly (P : ℝ[X]) :
    HasSum (fun k => PowerSeries.coeff k (P : PowerSeries ℝ)) (P.eval 1) := by
  have hfin : HasSum (fun k => PowerSeries.coeff k (P : PowerSeries ℝ))
      (∑ k ∈ Finset.range (P.natDegree + 1), PowerSeries.coeff k (P : PowerSeries ℝ)) := by
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  convert hfin using 1
  rw [Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Polynomial.coeff_coe]

lemma summable_norm_coeff_poly (P : ℝ[X]) :
    Summable (fun k => ‖PowerSeries.coeff k (P : PowerSeries ℝ)‖) := by
  refine summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun k hk => ?_
  simp only [Finset.mem_range, not_lt] at hk
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

/- `ℝ[X]`-linear independence of `{fPS p : p : Idx n}` via formal exponential polynomials. -/

noncomputable def expIntPS (c : ℤ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => (c : ℝ) ^ k / (k.factorial : ℝ)

lemma coeff_expIntPS (c : ℤ) (k : ℕ) :
    PowerSeries.coeff k (expIntPS c) = (c : ℝ) ^ k / (k.factorial : ℝ) := by
  simp [expIntPS]

lemma expIntPS_neg_nat (a : ℕ) : expIntPS (-(a : ℤ)) = expNegPS a := by
  ext k; simp [coeff_expIntPS, coeff_expNegPS]

lemma expIntPS_zero : expIntPS 0 = 1 := by
  ext k; cases k <;> simp [coeff_expIntPS, PowerSeries.coeff_one]

lemma expIntPS_add (a b : ℤ) : expIntPS a * expIntPS b = expIntPS (a + b) := by
  ext k
  rw [PowerSeries.coeff_mul, coeff_expIntPS]
  simp_rw [coeff_expIntPS]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  rw [mul_div_cancel₀ _ hf, Finset.mul_sum]
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
      (k.factorial : ℝ) * ((a : ℝ) ^ x.1 / (x.1.factorial : ℝ) *
        ((b : ℝ) ^ x.2 / (x.2.factorial : ℝ))) =
      (a : ℝ) ^ x.1 * (b : ℝ) ^ x.2 * (k.choose x.1 : ℝ) := by
    intro ⟨i, j⟩ hij
    have hsum : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hch : (k.choose i : ℝ) * (i.factorial : ℝ) * (j.factorial : ℝ) = (k.factorial : ℝ) := by
      have hnat := Nat.choose_mul_factorial_mul_factorial (show i ≤ k by omega)
      rw [show k - i = j by omega] at hnat
      exact_mod_cast hnat
    have hi : (i.factorial : ℝ) ≠ 0 := by positivity
    have hj : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [← hch]; field_simp [hi, hj]
  rw [Finset.sum_congr rfl hterm, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← add_pow (a : ℝ) (b : ℝ) k]
  push_cast; ring

noncomputable def dPS (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => ((k + 1 : ℕ) : ℝ) * PowerSeries.coeff (k + 1) f

lemma coeff_dPS (f : PowerSeries ℝ) (k : ℕ) :
    PowerSeries.coeff k (dPS f) = ((k + 1 : ℕ) : ℝ) * PowerSeries.coeff (k + 1) f := by
  simp [dPS]

lemma dPS_add (f g : PowerSeries ℝ) : dPS (f + g) = dPS f + dPS g := by
  ext k; simp [coeff_dPS, mul_add]

lemma dPS_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) :
    dPS (∑ i ∈ s, f i) = ∑ i ∈ s, dPS (f i) := by
  ext k; simp [coeff_dPS, Finset.mul_sum]

lemma dPS_mul (f g : PowerSeries ℝ) : dPS (f * g) = dPS f * g + f * dPS g := by
  ext k
  have hX : PowerSeries.coeff (k + 1) (Dps (f * g)) =
      PowerSeries.coeff (k + 1) (Dps f * g + f * Dps g) := by
    rw [Dps_mul]
  have hD : ∀ h : PowerSeries ℝ, PowerSeries.X * dPS h = Dps h := by
    intro h; ext j
    cases j with
    | zero => simp [PowerSeries.coeff_zero_X_mul, coeff_Dps]
    | succ j => simp [PowerSeries.coeff_succ_X_mul, coeff_dPS, coeff_Dps]
  have hmulX : PowerSeries.X * dPS (f * g) = PowerSeries.X * (dPS f * g + f * dPS g) := by
    rw [hD, Dps_mul, ← hD f, ← hD g]; ring
  have hk := congrArg (PowerSeries.coeff (k + 1)) hmulX
  simpa only [PowerSeries.coeff_succ_X_mul] using hk

lemma dPS_poly (P : ℝ[X]) : dPS (P : PowerSeries ℝ) = (P.derivative : PowerSeries ℝ) := by
  ext k
  rw [coeff_dPS, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]
  push_cast
  ring

lemma dPS_expIntPS (c : ℤ) : dPS (expIntPS c) = (c : ℝ) • expIntPS c := by
  ext k
  rw [coeff_dPS, PowerSeries.coeff_smul, smul_eq_mul, coeff_expIntPS, coeff_expIntPS]
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ']
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hfk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hk, hfk]

lemma Dps_expIntPS (c : ℤ) : Dps (expIntPS c) = ((c : ℝ[X]) * Polynomial.X : ℝ[X]) * expIntPS c := by
  ext k
  rw [coeff_Dps]
  have hpoly : (((c : ℝ[X]) * Polynomial.X : ℝ[X]) : PowerSeries ℝ) = (c : ℝ) • PowerSeries.X := by
    rw [Polynomial.coe_mul, poly_coe_intCast, Polynomial.coe_X, Algebra.smul_def,
      PowerSeries.C_eq_algebraMap]
  rw [hpoly, smul_mul_assoc, PowerSeries.coeff_smul, smul_eq_mul]
  cases k with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_expIntPS, coeff_expIntPS,
      Nat.factorial_succ, Nat.cast_mul, pow_succ']
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hk, hfk]

lemma expIntPS_linearIndependent :
    ∀ (F : ℤ →₀ ℝ[X]),
      (∑ c ∈ F.support, ((F c : ℝ[X]) : PowerSeries ℝ) * expIntPS c) = 0 → F = 0 := by
  intro F
  induction hcard : F.support.card using Nat.strong_induction_on generalizing F with
  | h k ih =>
    intro hsum
    by_cases hF0 : F = 0
    · exact hF0
    · exfalso
      have hne : F.support.Nonempty := Finsupp.support_nonempty_iff.mpr hF0
      let c0 : ℤ := F.support.min' hne
      have hc0_mem : c0 ∈ F.support := Finset.min'_mem F.support hne
      have hc0_ne : F c0 ≠ 0 := Finsupp.mem_support_iff.mp hc0_mem
      have hshift_zero : (∑ c ∈ F.support, ((F c : ℝ[X]) : PowerSeries ℝ) * expIntPS (c - c0)) = 0 := by
        have hm := congrArg (fun x => x * expIntPS (-c0)) hsum
        rw [zero_mul, Finset.sum_mul] at hm
        rw [← hm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_assoc, expIntPS_add, sub_eq_add_neg]
      let step : (ℤ →₀ ℝ[X]) → (ℤ →₀ ℝ[X]) := fun H =>
        H.sum fun c P => Finsupp.single c (P.derivative + ((c - c0 : ℤ) : ℝ[X]) * P)
      have hstep_apply : ∀ (H : ℤ →₀ ℝ[X]) (c : ℤ),
          step H c = (H c).derivative + ((c - c0 : ℤ) : ℝ[X]) * (H c) := by
        intro H c
        simp only [step, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
        by_cases hc : c ∈ H.support
        · rw [Finset.sum_eq_single c]
          · simp
          · intro x _ hxc; simp [hxc]
          · intro h; exact absurd hc h
        · have hHc : H c = 0 := Finsupp.notMem_support_iff.mp hc
          rw [hHc, Polynomial.derivative_zero, mul_zero, add_zero]
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxc : x ≠ c := fun h => hc (h ▸ hx)
          simp [hxc]
      have hstep_dPS : ∀ H : ℤ →₀ ℝ[X],
          (∑ c ∈ (step H).support, (((step H c : ℝ[X]) : PowerSeries ℝ) * expIntPS (c - c0))) =
            dPS (∑ c ∈ H.support, (((H c : ℝ[X]) : PowerSeries ℝ) * expIntPS (c - c0))) := by
        intro H
        have hsub : (step H).support ⊆ H.support := by
          intro c hc
          rw [Finsupp.mem_support_iff] at hc ⊢
          intro hHc
          rw [hstep_apply, hHc] at hc
          simp at hc
        rw [Finset.sum_subset hsub (fun c _ hc => by
            simp [Finsupp.notMem_support_iff.mp hc])]
        rw [dPS_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hstep_apply, dPS_mul, dPS_poly, dPS_expIntPS, Polynomial.coe_add, Polynomial.coe_mul,
          poly_coe_intCast, Algebra.smul_def, PowerSeries.C_eq_algebraMap]
        ring
      have hstep_ne : ∀ (H : ℤ →₀ ℝ[X]) (c : ℤ), c ≠ c0 → H c ≠ 0 → step H c ≠ 0 := by
        intro H c hne hHc
        rw [hstep_apply]
        intro hzero
        have hcc : ((c - c0 : ℤ) : ℝ[X]) ≠ 0 := by
          have hneR : ((c - c0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
          intro hz; apply hneR; simpa using congrArg (Polynomial.eval 0) hz
        by_cases hd0 : (H c).natDegree = 0
        · have hCeq := Polynomial.eq_C_of_natDegree_eq_zero hd0
          rw [hCeq, Polynomial.derivative_C, zero_add] at hzero
          have hCne : Polynomial.C ((H c).coeff 0) ≠ 0 := by rwa [← hCeq]
          exact mul_ne_zero hcc hCne hzero
        · have hlt : ((H c).derivative).natDegree < (((c - c0 : ℤ) : ℝ[X]) * H c).natDegree := by
            rw [Polynomial.natDegree_mul hcc hHc, Polynomial.natDegree_intCast, zero_add]
            exact Polynomial.natDegree_derivative_lt hd0
          have hlc : ((H c).derivative + ((c - c0 : ℤ) : ℝ[X]) * H c).natDegree =
              (((c - c0 : ℤ) : ℝ[X]) * H c).natDegree := by
            rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]
          rw [hzero, Polynomial.natDegree_zero, Polynomial.natDegree_mul hcc hHc,
            Polynomial.natDegree_intCast, zero_add] at hlc
          exact hd0 hlc.symm
      have hiter_c0 : ∀ m : ℕ, (step^[m] F) c0 = (Polynomial.derivative^[m]) (F c0) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ihm =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep_apply, ihm]
          simp
      have hiter_sum : ∀ m : ℕ,
          (∑ c ∈ (step^[m] F).support, (((step^[m] F c : ℝ[X]) : PowerSeries ℝ) * expIntPS (c - c0))) = 0 := by
        intro m
        induction m with
        | zero => exact hshift_zero
        | succ m ihm =>
          rw [Function.iterate_succ_apply', hstep_dPS, ihm]
          ext j; simp [coeff_dPS]
      have hiter_supp : ∀ m : ℕ, (step^[m] F).support ⊆ F.support := by
        intro m
        induction m with
        | zero => exact Finset.Subset.refl _
        | succ m ihm =>
          intro c hc
          rw [Function.iterate_succ_apply'] at hc
          apply ihm
          rw [Finsupp.mem_support_iff] at hc ⊢
          intro h0; rw [hstep_apply, h0] at hc; simp at hc
      have hiter_other : ∀ m : ℕ, ∀ c ∈ F.support, c ≠ c0 → (step^[m] F) c ≠ 0 := by
        intro m c hc hne
        induction m with
        | zero => exact Finsupp.mem_support_iff.mp hc
        | succ m ihm =>
          rw [Function.iterate_succ_apply']
          exact hstep_ne _ c hne ihm
      let d := (F c0).natDegree + 1
      let F' := step^[d] F
      have hF'c0 : F' c0 = 0 := by
        change (step^[d] F) c0 = 0
        rw [hiter_c0]
        exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)
      have hF'_card : F'.support.card < k := by
        rw [← hcard]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hiter_supp d, ?_⟩)
        intro heq
        have : c0 ∈ F'.support := heq ▸ hc0_mem
        exact Finsupp.mem_support_iff.mp this hF'c0
      have hF'_sum : (∑ c ∈ F'.support, ((F' c : ℝ[X]) : PowerSeries ℝ) * expIntPS c) = 0 := by
        have hm := congrArg (fun x => x * expIntPS c0) (hiter_sum d)
        rw [zero_mul, Finset.sum_mul] at hm
        rw [← hm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_assoc, expIntPS_add, sub_add_cancel]
      have hF'_zero : F' = 0 := ih F'.support.card hF'_card F' rfl hF'_sum
      -- Wait: if `F' = 0`, then `F` had NO other elements in `F.support` besides `c0`!
      have honly : ∀ c ∈ F.support, c = c0 := by
        intro c hc
        by_contra hne
        have := hiter_other d c hc hne
        rw [show step^[d] F = F' from rfl, hF'_zero] at this
        exact this rfl
      have hsupp_eq : F.support = {c0} := by
        ext c
        simp only [Finset.mem_singleton]
        exact ⟨honly c, fun h => h ▸ hc0_mem⟩
      rw [hsupp_eq, Finset.sum_singleton, sub_self, expIntPS_zero, mul_one] at hshift_zero
      have hP0 : F c0 = 0 := by
        ext j
        have := congrArg (PowerSeries.coeff j) hshift_zero
        simpa [Polynomial.coeff_coe] using this
      exact hc0_ne hP0

/- Exponential polynomial ring `ExpPoly := AddMonoidAlgebra ℝ[X] ℤ` and algebraic independence of `einPS`. -/

abbrev ExpPoly := AddMonoidAlgebra ℝ[X] ℤ

noncomputable def evalExpPoly (G : ExpPoly) : PowerSeries ℝ :=
  G.coeff.sum fun c P => (P : PowerSeries ℝ) * expIntPS c

lemma evalExpPoly_add (G H : ExpPoly) : evalExpPoly (G + H) = evalExpPoly G + evalExpPoly H := by
  simp only [evalExpPoly, AddMonoidAlgebra.coeff_add]
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro _ _ _; simp [Polynomial.coe_add, add_mul]

lemma evalExpPoly_sub (G H : ExpPoly) : evalExpPoly (G - H) = evalExpPoly G - evalExpPoly H := by
  have h : evalExpPoly (G - H) + evalExpPoly H = evalExpPoly G := by
    rw [← evalExpPoly_add, sub_add_cancel]
  exact eq_sub_of_add_eq h

lemma evalExpPoly_single (c : ℤ) (P : ℝ[X]) :
    evalExpPoly (AddMonoidAlgebra.single c P) = (P : PowerSeries ℝ) * expIntPS c := by
  rw [evalExpPoly, AddMonoidAlgebra.single, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_single_index]
  simp

lemma expPoly_ext {G H : ExpPoly} (h : ∀ c : ℤ, G.coeff c = H.coeff c) : G = H := by
  rcases G with ⟨f⟩
  rcases H with ⟨g⟩
  congr 1
  exact Finsupp.ext h

lemma expPoly_induction {p : ExpPoly → Prop} (h0 : p 0)
    (hadd : ∀ f g, p f → p g → p (f + g))
    (hsingle : ∀ c P, p (AddMonoidAlgebra.single c P)) : ∀ G : ExpPoly, p G := by
  intro G
  rcases G with ⟨f⟩
  induction f using Finsupp.induction_linear with
  | zero => exact h0
  | add f1 f2 h1 h2 => exact hadd ⟨f1⟩ ⟨f2⟩ h1 h2
  | single c P => exact hsingle c P

lemma evalExpPoly_mul (G H : ExpPoly) : evalExpPoly (G * H) = evalExpPoly G * evalExpPoly H := by
  induction G using expPoly_induction with
  | h0 => simp [evalExpPoly]
  | hadd G1 G2 h1 h2 =>
    rw [add_mul, evalExpPoly_add, evalExpPoly_add, add_mul, h1, h2]
  | hsingle c1 P1 =>
    induction H using expPoly_induction with
    | h0 => simp [evalExpPoly]
    | hadd H1 H2 h1 h2 =>
      rw [mul_add, evalExpPoly_add, evalExpPoly_add, mul_add, h1, h2]
    | hsingle c2 P2 =>
      rw [AddMonoidAlgebra.single_mul_single, evalExpPoly_single, evalExpPoly_single,
        evalExpPoly_single, Polynomial.coe_mul, ← expIntPS_add]
      ring

lemma evalExpPoly_injective {G : ExpPoly} (h : evalExpPoly G = 0) : G = 0 := by
  have hc : G.coeff = 0 := expIntPS_linearIndependent G.coeff h
  exact expPoly_ext fun c => congrArg (fun f : ℤ →₀ ℝ[X] => f c) hc

noncomputable def Dexp (G : ExpPoly) : ExpPoly :=
  AddMonoidAlgebra.ofCoeff <|
    G.coeff.sum fun c P => Finsupp.single c (Polynomial.X * (P.derivative + ((c : ℝ[X]) * P)))

lemma Dexp_coeff (G : ExpPoly) (c : ℤ) :
    (Dexp G).coeff c = Polynomial.X * ((G.coeff c).derivative + ((c : ℝ[X]) * (G.coeff c))) := by
  simp only [Dexp, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.sum, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  by_cases hc : c ∈ G.coeff.support
  · rw [Finset.sum_eq_single c]
    · simp
    · intro x _ hxc; simp [hxc]
    · intro h; exact absurd hc h
  · have hGc : G.coeff c = 0 := Finsupp.notMem_support_iff.mp hc
    rw [hGc, Polynomial.derivative_zero, mul_zero, add_zero, mul_zero]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    simp [hxc]

lemma evalExpPoly_Dexp (G : ExpPoly) : evalExpPoly (Dexp G) = Dps (evalExpPoly G) := by
  induction G using expPoly_induction with
  | h0 =>
    have hD0 : Dexp 0 = 0 := expPoly_ext fun c => by simp [Dexp_coeff]
    rw [hD0]; simp [evalExpPoly]; ext k; simp [coeff_Dps]
  | hadd G1 G2 h1 h2 =>
    have hDadd : Dexp (G1 + G2) = Dexp G1 + Dexp G2 := expPoly_ext fun c => by
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Dexp_coeff,
        Polynomial.derivative_add]
      ring
    rw [hDadd, evalExpPoly_add, evalExpPoly_add, Dps_add, h1, h2]
  | hsingle c P =>
    have hDsingle : Dexp (AddMonoidAlgebra.single c P) =
        AddMonoidAlgebra.single c (Polynomial.X * (P.derivative + ((c : ℝ[X]) * P))) := by
      refine expPoly_ext fun x => ?_
      rw [Dexp_coeff, AddMonoidAlgebra.single, AddMonoidAlgebra.single,
        AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_ofCoeff,
        Finsupp.single_apply, Finsupp.single_apply]
      split_ifs with hxc
      · subst hxc; rfl
      · simp
    rw [hDsingle, evalExpPoly_single, evalExpPoly_single, Dps_mul, Dps_poly, Dps_expIntPS]
    have hX1 : ((Polynomial.X * (P.derivative + (c : ℝ[X]) * P) : ℝ[X]) : PowerSeries ℝ) =
        PowerSeries.X * ((P.derivative : PowerSeries ℝ) + PowerSeries.C (c : ℝ) * (P : PowerSeries ℝ)) := by
      rw [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X,
        poly_coe_intCast]
    have hX2 : (((c : ℝ[X]) * Polynomial.X : ℝ[X]) : PowerSeries ℝ) =
        PowerSeries.C (c : ℝ) * PowerSeries.X := by
      rw [Polynomial.coe_mul, poly_coe_intCast, Polynomial.coe_X]
    rw [hX1, hX2, Polynomial.coe_mul, Polynomial.coe_X]
    ring

noncomputable def expPolyEvalZ0 (G : ExpPoly) : AddMonoidAlgebra ℝ ℤ :=
  AddMonoidAlgebra.ofCoeff (G.coeff.mapRange (Polynomial.eval 0) Polynomial.eval_zero)

lemma expPolyEvalZ0_add (G H : ExpPoly) :
    expPolyEvalZ0 (G + H) = expPolyEvalZ0 G + expPolyEvalZ0 H := by
  ext c; simp [expPolyEvalZ0]

lemma expPolyEvalZ0_single (c : ℤ) (P : ℝ[X]) :
    expPolyEvalZ0 (AddMonoidAlgebra.single c P) = AddMonoidAlgebra.single c (Polynomial.eval 0 P) := by
  rcases eq_or_ne (Polynomial.eval 0 P) 0 with h | h <;>
  · ext x
    simp only [expPolyEvalZ0, AddMonoidAlgebra.single, AddMonoidAlgebra.coeff_ofCoeff,
      Finsupp.mapRange_apply, Finsupp.single_apply]
    split_ifs <;> simp

lemma expPolyEvalZ0_mul (G H : ExpPoly) :
    expPolyEvalZ0 (G * H) = expPolyEvalZ0 G * expPolyEvalZ0 H := by
  induction G using expPoly_induction with
  | h0 => simp [expPolyEvalZ0]
  | hadd G1 G2 h1 h2 => rw [add_mul, expPolyEvalZ0_add, expPolyEvalZ0_add, add_mul, h1, h2]
  | hsingle c1 P1 =>
    induction H using expPoly_induction with
    | h0 => simp [expPolyEvalZ0]
    | hadd H1 H2 h1 h2 => rw [mul_add, expPolyEvalZ0_add, expPolyEvalZ0_add, mul_add, h1, h2]
    | hsingle c2 P2 =>
      rw [AddMonoidAlgebra.single_mul_single, expPolyEvalZ0_single, expPolyEvalZ0_single,
        expPolyEvalZ0_single, AddMonoidAlgebra.single_mul_single, Polynomial.eval_mul]

lemma expPoly_single_zero_mul_coeff (Q : ℝ[X]) (A : ExpPoly) (c : ℤ) :
    (AddMonoidAlgebra.single (0 : ℤ) Q * A).coeff c = Q * A.coeff c := by
  induction A using expPoly_induction with
  | h0 => simp
  | hadd A1 A2 h1 h2 =>
    rw [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h1, h2,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
  | hsingle a P =>
    rw [AddMonoidAlgebra.single_mul_single, zero_add]
    simp only [AddMonoidAlgebra.single, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.single_apply]
    split_ifs <;> simp

lemma addMonoidAlgebra_real_int_mul_ne_zero {f g : AddMonoidAlgebra ℝ ℤ}
    (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := by
  have hfc : f.coeff ≠ 0 := fun h => hf (by ext c; exact congrArg (fun u : ℤ →₀ ℝ => u c) h)
  have hgc : g.coeff ≠ 0 := fun h => hg (by ext c; exact congrArg (fun u : ℤ →₀ ℝ => u c) h)
  have hfs : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hfc
  have hgs : g.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hgc
  let a := f.coeff.support.max' hfs
  let b := g.coeff.support.max' hgs
  have ha : f.coeff a ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hfs)
  have hb : g.coeff b ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hgs)
  have hmul_coeff : ∀ (u v : AddMonoidAlgebra ℝ ℤ) (m : ℤ),
      (u * v).coeff m = u.coeff.sum fun a1 x1 => v.coeff.sum fun a2 x2 =>
        if a1 + a2 = m then x1 * x2 else 0 := by
    intro u v m
    have huv : u = ∑ a1 ∈ u.coeff.support, AddMonoidAlgebra.single a1 (u.coeff a1) := by
      ext c
      simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.single,
        Finsupp.finsetSum_apply, Finsupp.single_apply]
      by_cases hc : c ∈ u.coeff.support
      · rw [Finset.sum_eq_single c]
        · simp
        · intro x _ hxc; simp [hxc]
        · intro h; exact absurd hc h
      · rw [Finsupp.notMem_support_iff.mp hc]
        refine (Finset.sum_eq_zero fun x hx => ?_).symm
        have hxc : x ≠ c := fun h => hc (h ▸ hx)
        simp [hxc]
    have hvv : v = ∑ a2 ∈ v.coeff.support, AddMonoidAlgebra.single a2 (v.coeff a2) := by
      ext c
      simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.single,
        Finsupp.finsetSum_apply, Finsupp.single_apply]
      by_cases hc : c ∈ v.coeff.support
      · rw [Finset.sum_eq_single c]
        · simp
        · intro x _ hxc; simp [hxc]
        · intro h; exact absurd hc h
      · rw [Finsupp.notMem_support_iff.mp hc]
        refine (Finset.sum_eq_zero fun x hx => ?_).symm
        have hxc : x ≠ c := fun h => hc (h ▸ hx)
        simp [hxc]
    conv_lhs => rw [huv, hvv]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, AddMonoidAlgebra.single_mul_single]
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.single,
      Finsupp.single_apply, Finsupp.sum]
  intro hzero
  have hcoeff := congrArg (fun h : AddMonoidAlgebra ℝ ℤ => h.coeff (a + b)) hzero
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, hmul_coeff] at hcoeff
  have hsum : (f.coeff.sum fun a1 x1 => g.coeff.sum fun a2 x2 =>
      if a1 + a2 = a + b then x1 * x2 else 0) = f.coeff a * g.coeff b := by
    rw [Finsupp.sum, Finset.sum_eq_single a]
    · rw [Finsupp.sum, Finset.sum_eq_single b]
      · simp
      · intro b' hb' hne; rw [if_neg (by omega)]
      · intro h; exact absurd (Finset.max'_mem _ hgs) h
    · intro a' ha' hne
      have halt : a' < a := lt_of_le_of_ne (Finset.le_max' _ a' ha') hne
      refine Finset.sum_eq_zero fun b' hb' => ?_
      have hble : b' ≤ b := Finset.le_max' _ b' hb'
      dsimp only
      rw [if_neg (by omega)]
    · intro h; exact absurd (Finset.max'_mem _ hfs) h
  rw [hsum] at hcoeff
  exact mul_ne_zero ha hb hcoeff

lemma expPoly_factor_X (G : ExpPoly) (hG : G ≠ 0) :
    ∃ (k : ℕ) (Gt : ExpPoly),
      expPolyEvalZ0 Gt ≠ 0 ∧ G = (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k)) * Gt := by
  induction hdeg : (∑ c ∈ G.coeff.support, (G.coeff c).natDegree) using Nat.strong_induction_on
      generalizing G with
  | h d ih =>
    by_cases hev : expPolyEvalZ0 G ≠ 0
    · refine ⟨0, G, hev, expPoly_ext fun c => ?_⟩
      rw [expPoly_single_zero_mul_coeff, pow_zero, one_mul]
    · push Not at hev
      have hdiv : ∀ c : ℤ, Polynomial.X ∣ G.coeff c := by
        intro c
        rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
        have := congrArg (fun h : AddMonoidAlgebra ℝ ℤ => h.coeff c) hev
        simpa [expPolyEvalZ0] using this
      let G1 : ExpPoly := AddMonoidAlgebra.ofCoeff
        (G.coeff.mapRange (fun P => P /ₘ Polynomial.X) (by simp))
      have hG1_coeff : ∀ c : ℤ, G.coeff c = Polynomial.X * G1.coeff c := by
        intro c
        simp only [G1, Finsupp.mapRange_apply]
        have hmon : (Polynomial.X : ℝ[X]).Monic := Polynomial.monic_X
        have hmod : G.coeff c %ₘ Polynomial.X = 0 :=
          (Polynomial.modByMonic_eq_zero_iff_dvd hmon).mpr (hdiv c)
        have hdiv_eq := Polynomial.modByMonic_add_div (G.coeff c) Polynomial.X
        rw [hmod, zero_add] at hdiv_eq
        exact hdiv_eq.symm
      have hmul : G = AddMonoidAlgebra.single (0 : ℤ) Polynomial.X * G1 :=
        expPoly_ext fun c => by rw [expPoly_single_zero_mul_coeff]; exact hG1_coeff c
      have hG1_ne : G1 ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hmul; exact hG hmul
      have hG1_supp : G1.coeff.support = G.coeff.support := by
        ext c
        simp only [Finsupp.mem_support_iff, ne_eq]
        constructor
        · intro h1 h0; apply h1; rw [hG1_coeff c] at h0
          exact (mul_eq_zero.mp h0).resolve_left Polynomial.X_ne_zero
        · intro h0 h1; apply h0; rw [hG1_coeff c, h1, mul_zero]
      have hGc_ne : G.coeff ≠ 0 := fun h => hG (expPoly_ext fun c => congrArg (fun u : ℤ →₀ ℝ[X] => u c) h)
      have hdeg_lt : (∑ c ∈ G1.coeff.support, (G1.coeff c).natDegree) < d := by
        rw [← hdeg, hG1_supp]
        refine Finset.sum_lt_sum (fun c hc => ?_) ?_
        · have hG1c : G1.coeff c ≠ 0 := Finsupp.mem_support_iff.mp (hG1_supp.symm ▸ hc)
          rw [hG1_coeff c, Polynomial.natDegree_mul Polynomial.X_ne_zero hG1c, Polynomial.natDegree_X]
          omega
        · obtain ⟨c, hc⟩ := Finsupp.support_nonempty_iff.mpr hGc_ne
          refine ⟨c, hc, ?_⟩
          have hG1c : G1.coeff c ≠ 0 := Finsupp.mem_support_iff.mp (hG1_supp.symm ▸ hc)
          rw [hG1_coeff c, Polynomial.natDegree_mul Polynomial.X_ne_zero hG1c, Polynomial.natDegree_X]
          omega
      obtain ⟨k, Gt, hGt_ev, hGt_eq⟩ := ih _ hdeg_lt G1 hG1_ne rfl
      refine ⟨k + 1, Gt, hGt_ev, ?_⟩
      rw [hmul, hGt_eq, ← mul_assoc, AddMonoidAlgebra.single_mul_single, zero_add, pow_succ']

lemma expPoly_mul_X_pow_cancel {k : ℕ} {G H : ExpPoly}
    (h : AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * G =
         AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * H) : G = H :=
  expPoly_ext fun c => by
    have hc := congrArg (fun A : ExpPoly => A.coeff c) h
    rw [expPoly_single_zero_mul_coeff, expPoly_single_zero_mul_coeff] at hc
    exact mul_left_cancel₀ (pow_ne_zero k Polynomial.X_ne_zero) hc

lemma Dexp_X_pow_mul (k : ℕ) (G : ExpPoly) :
    ∃ H : ExpPoly,
      Dexp (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * G) =
        AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) *
          (AddMonoidAlgebra.single (0 : ℤ) (k : ℝ[X]) * G +
            AddMonoidAlgebra.single (0 : ℤ) Polynomial.X * H) := by
  refine ⟨AddMonoidAlgebra.ofCoeff
      (G.coeff.sum fun c P => Finsupp.single c (P.derivative + (c : ℝ[X]) * P)),
    expPoly_ext fun c => ?_⟩
  rw [Dexp_coeff, expPoly_single_zero_mul_coeff, expPoly_single_zero_mul_coeff,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, expPoly_single_zero_mul_coeff,
    expPoly_single_zero_mul_coeff]
  have hH : (AddMonoidAlgebra.ofCoeff
      (G.coeff.sum fun c' P => Finsupp.single c' (P.derivative + (c' : ℝ[X]) * P))).coeff c =
      (G.coeff c).derivative + (c : ℝ[X]) * G.coeff c := by
    simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
    by_cases hc : c ∈ G.coeff.support
    · rw [Finset.sum_eq_single c]
      · simp
      · intro x _ hxc; simp [hxc]
      · intro h0; exact absurd hc h0
    · have hGc : G.coeff c = 0 := Finsupp.notMem_support_iff.mp hc
      rw [hGc, Polynomial.derivative_zero, mul_zero, add_zero]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxc : x ≠ c := fun h0 => hc (h0 ▸ hx)
      simp [hxc]
  rw [hH, Polynomial.derivative_mul, Polynomial.derivative_X_pow]
  cases k with
  | zero => simp
  | succ k =>
    simp only [pow_succ, Nat.add_sub_cancel, Polynomial.C_add, Polynomial.C_eq_natCast,
      Polynomial.C_1, Nat.cast_add, Nat.cast_one]
    ring

lemma expPoly_wronskian_ne_zero (G0 G1 : ExpPoly) (B : ℕ) (hB : 0 < B) (hG1 : G1 ≠ 0) :
    G1 * Dexp G0 - Dexp G1 * G0 +
      AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) * (G1 * G1) *
        (AddMonoidAlgebra.single (0 : ℤ) (1 : ℝ[X]) - AddMonoidAlgebra.single (-1 : ℤ) (1 : ℝ[X])) ≠ 0 := by
  let oneMinusT : ExpPoly :=
    AddMonoidAlgebra.single (0 : ℤ) (1 : ℝ[X]) - AddMonoidAlgebra.single (-1 : ℤ) (1 : ℝ[X])
  have h1mT_ev : expPolyEvalZ0 oneMinusT ≠ 0 := by
    intro h0
    have h1 := congrArg (fun f : AddMonoidAlgebra ℝ ℤ => f.coeff 0) h0
    simp only [oneMinusT, expPolyEvalZ0, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply,
      AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, AddMonoidAlgebra.single, Finsupp.single_apply,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    norm_num at h1
  intro hzero
  have hBne : (B : ℝ) ≠ 0 := by positivity
  have hB_ev : expPolyEvalZ0 (AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X])) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun f : AddMonoidAlgebra ℝ ℤ => f.coeff 0) h0
    simp only [expPolyEvalZ0, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply,
      AddMonoidAlgebra.single, Finsupp.single_apply, ↓reduceIte, Polynomial.eval_natCast,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    exact hBne h1
  have hXadd : ∀ a b : ℕ,
      AddMonoidAlgebra.single (0 : ℤ) ((Polynomial.X : ℝ[X]) ^ a) *
        AddMonoidAlgebra.single (0 : ℤ) ((Polynomial.X : ℝ[X]) ^ b) =
        AddMonoidAlgebra.single (0 : ℤ) ((Polynomial.X : ℝ[X]) ^ (a + b)) := by
    intro a b; rw [AddMonoidAlgebra.single_mul_single, zero_add, ← pow_add (Polynomial.X : ℝ[X])]
  have hXev : ∀ m : ℕ, 0 < m →
      expPolyEvalZ0 (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ m)) = 0 := by
    intro m hm
    ext c
    simp only [expPolyEvalZ0, AddMonoidAlgebra.single, AddMonoidAlgebra.coeff_ofCoeff,
      Finsupp.mapRange_apply, Finsupp.single_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    split_ifs
    · rw [Polynomial.eval_pow, Polynomial.eval_X, zero_pow (by omega)]
    · simp
  by_cases hG0 : G0 = 0
  · rw [hG0, show Dexp 0 = 0 from expPoly_ext fun c => by simp [Dexp_coeff], mul_zero, mul_zero,
      sub_self, zero_add] at hzero
    obtain ⟨k, Gt1, hGt1_ev, hGt1_eq⟩ := expPoly_factor_X G1 hG1
    rw [hGt1_eq] at hzero
    have hpull : AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) *
        ((AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * Gt1) *
          (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * Gt1)) * oneMinusT =
        AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (2 * k)) *
          (AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) * (Gt1 * Gt1) * oneMinusT) := by
      calc _ = (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) *
                  AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k)) *
                  (AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) * (Gt1 * Gt1) * oneMinusT) := by ring
        _ = _ := by rw [hXadd, two_mul]
    rw [hpull, ← mul_zero (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (2 * k)))] at hzero
    have hrem := expPoly_mul_X_pow_cancel hzero
    have hev := congrArg expPolyEvalZ0 hrem
    rw [expPolyEvalZ0_mul, expPolyEvalZ0_mul, expPolyEvalZ0_mul] at hev
    have hne3 := addMonoidAlgebra_real_int_mul_ne_zero
      (addMonoidAlgebra_real_int_mul_ne_zero hB_ev
        (addMonoidAlgebra_real_int_mul_ne_zero hGt1_ev hGt1_ev)) h1mT_ev
    exact hne3 (by simpa [expPolyEvalZ0] using hev)
  · obtain ⟨k, Gt1, hGt1_ev, hGt1_eq⟩ := expPoly_factor_X G1 hG1
    obtain ⟨l, Gt0, hGt0_ev, hGt0_eq⟩ := expPoly_factor_X G0 hG0
    obtain ⟨H1, hH1⟩ := Dexp_X_pow_mul k Gt1
    obtain ⟨H0, hH0⟩ := Dexp_X_pow_mul l Gt0
    have hX1 : AddMonoidAlgebra.single (0 : ℤ) ((Polynomial.X : ℝ[X]) ^ 1) =
        AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X : ℝ[X]) := by rw [pow_one]
    have htermB_ev : expPolyEvalZ0
        (AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) * (Gt1 * Gt1) * oneMinusT) ≠ 0 := by
      rw [expPolyEvalZ0_mul, expPolyEvalZ0_mul, expPolyEvalZ0_mul]
      exact addMonoidAlgebra_real_int_mul_ne_zero
        (addMonoidAlgebra_real_int_mul_ne_zero hB_ev
          (addMonoidAlgebra_real_int_mul_ne_zero hGt1_ev hGt1_ev)) h1mT_ev
    have hrew :
        AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (k + l)) *
          ((AddMonoidAlgebra.single (0 : ℤ) ((l : ℝ[X]) - (k : ℝ[X])) * (Gt1 * Gt0)) +
           AddMonoidAlgebra.single (0 : ℤ) Polynomial.X * (Gt1 * H0 - H1 * Gt0)) +
        AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (2 * k)) *
          (AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) * (Gt1 * Gt1) * oneMinusT) = 0 := by
      have hdiff : AddMonoidAlgebra.single (0 : ℤ) ((l : ℝ[X]) - (k : ℝ[X])) =
          AddMonoidAlgebra.single (0 : ℤ) (l : ℝ[X]) -
          AddMonoidAlgebra.single (0 : ℤ) (k : ℝ[X]) := by
        rw [AddMonoidAlgebra.single_sub]
      rw [hGt1_eq, hGt0_eq, hH1, hH0] at hzero
      rw [hdiff]
      calc _ = (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * Gt1) *
                  (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ l) *
                    (AddMonoidAlgebra.single (0 : ℤ) (l : ℝ[X]) * Gt0 +
                      AddMonoidAlgebra.single (0 : ℤ) Polynomial.X * H0)) -
                (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) *
                  (AddMonoidAlgebra.single (0 : ℤ) (k : ℝ[X]) * Gt1 +
                    AddMonoidAlgebra.single (0 : ℤ) Polynomial.X * H1)) *
                  (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ l) * Gt0) +
                AddMonoidAlgebra.single (0 : ℤ) (B : ℝ[X]) *
                  ((AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * Gt1) *
                    (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ k) * Gt1)) * oneMinusT := by
            rw [← hXadd k l, show 2 * k = k + k by omega, ← hXadd k k]
            ring
        _ = 0 := hzero
    rcases lt_trichotomy l k with hlt | heq | hgt
    · have h2k : 2 * k = (k + l) + (k - l) := by omega
      rw [h2k, ← hXadd (k + l) (k - l), mul_assoc, ← mul_add,
        ← mul_zero (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (k + l)))] at hrew
      have hrem := expPoly_mul_X_pow_cancel hrew
      have hev := congrArg expPolyEvalZ0 hrem
      rw [expPolyEvalZ0_add, expPolyEvalZ0_add, expPolyEvalZ0_mul, expPolyEvalZ0_mul,
        expPolyEvalZ0_mul, expPolyEvalZ0_mul, ← hX1, hXev 1 (by omega), hXev (k - l) (by omega),
        zero_mul, zero_mul, add_zero, add_zero] at hev
      have hlk_ev : expPolyEvalZ0
          (AddMonoidAlgebra.single (0 : ℤ) ((l : ℝ[X]) - (k : ℝ[X]))) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun f : AddMonoidAlgebra ℝ ℤ => f.coeff 0) h0
        simp only [expPolyEvalZ0, AddMonoidAlgebra.single, AddMonoidAlgebra.coeff_ofCoeff,
          Finsupp.mapRange_apply, Finsupp.single_apply, ↓reduceIte, Polynomial.eval_sub,
          Polynomial.eval_natCast, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
        have hltR : (l : ℝ) < (k : ℝ) := by exact_mod_cast hlt
        linarith
      have hne := addMonoidAlgebra_real_int_mul_ne_zero hlk_ev
        (addMonoidAlgebra_real_int_mul_ne_zero hGt1_ev hGt0_ev)
      exact hne (by simpa [expPolyEvalZ0] using hev)
    · rw [heq, sub_self, AddMonoidAlgebra.single_zero, zero_mul, zero_add,
        show k + k = 2 * k by omega, ← mul_add,
        ← mul_zero (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (2 * k)))] at hrew
      have hrem := expPoly_mul_X_pow_cancel hrew
      have hev := congrArg expPolyEvalZ0 hrem
      rw [expPolyEvalZ0_add, expPolyEvalZ0_mul, ← hX1, hXev 1 (by omega), zero_mul, zero_add] at hev
      exact htermB_ev (by simpa [expPolyEvalZ0] using hev)
    · have hkl : k + l = 2 * k + (l - k) := by omega
      rw [hkl, ← hXadd (2 * k) (l - k), mul_assoc, ← mul_add,
        ← mul_zero (AddMonoidAlgebra.single (0 : ℤ) (Polynomial.X ^ (2 * k)))] at hrew
      have hrem := expPoly_mul_X_pow_cancel hrew
      have hev := congrArg expPolyEvalZ0 hrem
      rw [expPolyEvalZ0_add, expPolyEvalZ0_mul, hXev (l - k) (by omega), zero_mul, zero_add] at hev
      exact htermB_ev (by simpa [expPolyEvalZ0] using hev)

lemma einPS_alg_indep_over_expPoly :
    ∀ (B : ℕ) (G : Fin (B + 1) → ExpPoly),
      (∑ b : Fin (B + 1), evalExpPoly (G b) * einPS ^ b.1) = 0 → ∀ b, G b = 0 := by
  intro B
  induction B with
  | zero =>
    intro G hsum b
    have hb0 : b = 0 := Fin.ext (by have := b.2; omega)
    subst hb0
    rw [Fin.sum_univ_one] at hsum
    simp only [Fin.val_zero, pow_zero, mul_one] at hsum
    exact evalExpPoly_injective hsum
  | succ B ih =>
    intro G hsum
    by_cases htop : G ⟨B + 1, Nat.lt_succ_self _⟩ = 0
    · let G' : Fin (B + 1) → ExpPoly := fun b => G ⟨b.1, by omega⟩
      have hsum' : (∑ b : Fin (B + 1), evalExpPoly (G' b) * einPS ^ b.1) = 0 := by
        rw [Fin.sum_univ_castSucc] at hsum
        have hlast : G (Fin.last (B + 1)) = 0 := htop
        simp only [hlast, evalExpPoly, AddMonoidAlgebra.coeff_zero, Finsupp.sum_zero_index,
          zero_mul, add_zero] at hsum
        exact hsum
      intro b
      by_cases hb : b.1 < B + 1
      · exact ih G' hsum' ⟨b.1, hb⟩
      · have hbe : b = ⟨B + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; have := b.2; omega)
        rw [hbe]; exact htop
    · exfalso
      let GB : ExpPoly := G ⟨B + 1, Nat.lt_succ_self _⟩
      let oneMinusT : ExpPoly :=
        AddMonoidAlgebra.single (0 : ℤ) (1 : ℝ[X]) - AddMonoidAlgebra.single (-1 : ℤ) (1 : ℝ[X])
      have h1mT_eval : evalExpPoly oneMinusT = 1 - expNegPS 1 := by
        rw [evalExpPoly_sub, evalExpPoly_single, evalExpPoly_single, Polynomial.coe_one,
          expIntPS_zero, one_mul, one_mul]
        simpa using congrArg (fun x => (1 : PowerSeries ℝ) - x) (expIntPS_neg_nat 1)
      let H : Fin (B + 1) → ExpPoly := fun b =>
        GB * Dexp (G ⟨b.1, by omega⟩) - Dexp GB * G ⟨b.1, by omega⟩ +
          AddMonoidAlgebra.single (0 : ℤ) ((b.1 + 1 : ℕ) : ℝ[X]) *
            (GB * G ⟨b.1 + 1, by omega⟩) * oneMinusT
      have hHsum : (∑ b : Fin (B + 1), evalExpPoly (H b) * einPS ^ b.1) = 0 := by
        have hDR : Dps (∑ b : Fin (B + 2), evalExpPoly (G b) * einPS ^ b.1) = 0 := by
          rw [hsum]; ext k; simp [coeff_Dps]
        have hcomb : evalExpPoly GB * Dps (∑ b : Fin (B + 2), evalExpPoly (G b) * einPS ^ b.1) -
            Dps (evalExpPoly GB) * (∑ b : Fin (B + 2), evalExpPoly (G b) * einPS ^ b.1) = 0 := by
          rw [hDR, hsum, mul_zero, mul_zero, sub_self]
        rw [← hcomb, Dps_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        have hstep1 : ∀ b : Fin (B + 2),
            evalExpPoly GB * Dps (evalExpPoly (G b) * einPS ^ b.1) -
              Dps (evalExpPoly GB) * (evalExpPoly (G b) * einPS ^ b.1) =
            (evalExpPoly GB * Dps (evalExpPoly (G b)) - Dps (evalExpPoly GB) * evalExpPoly (G b)) *
              einPS ^ b.1 +
            (match b.1 with
              | 0 => 0
              | b' + 1 => ((b' + 1 : ℕ) : ℝ) •
                  (evalExpPoly GB * evalExpPoly (G b) * (1 - expNegPS 1) * einPS ^ b')) := by
          intro b
          rw [Dps_mul, Dps_pow]
          cases hb : b.1 with
          | zero => simp
          | succ b' =>
            rw [Dps_einPS]
            simp only [Algebra.smul_def]
            ring
        simp_rw [hstep1, Finset.sum_add_distrib]
        have hS1 : (∑ b : Fin (B + 2),
            (evalExpPoly GB * Dps (evalExpPoly (G b)) - Dps (evalExpPoly GB) * evalExpPoly (G b)) *
              einPS ^ b.1) =
            ∑ b : Fin (B + 1),
              evalExpPoly (GB * Dexp (G ⟨b.1, by omega⟩) - Dexp GB * G ⟨b.1, by omega⟩) *
                einPS ^ b.1 := by
          rw [Fin.sum_univ_castSucc]
          have htop0 : evalExpPoly GB * Dps (evalExpPoly (G (Fin.last (B + 1)))) -
              Dps (evalExpPoly GB) * evalExpPoly (G (Fin.last (B + 1))) = 0 := by
            change evalExpPoly GB * Dps (evalExpPoly GB) - Dps (evalExpPoly GB) * evalExpPoly GB = 0
            ring
          rw [htop0, zero_mul, add_zero]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [evalExpPoly_sub, evalExpPoly_mul, evalExpPoly_mul, evalExpPoly_Dexp, evalExpPoly_Dexp]
          rfl
        have hS2 : (∑ b : Fin (B + 2),
            match b.1 with
              | 0 => (0 : PowerSeries ℝ)
              | b' + 1 => ((b' + 1 : ℕ) : ℝ) •
                  (evalExpPoly GB * evalExpPoly (G b) * (1 - expNegPS 1) * einPS ^ b')) =
            ∑ b : Fin (B + 1),
              evalExpPoly (AddMonoidAlgebra.single (0 : ℤ) ((b.1 + 1 : ℕ) : ℝ[X]) *
                (GB * G ⟨b.1 + 1, by omega⟩) * oneMinusT) * einPS ^ b.1 := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, zero_add, Fin.val_succ]
          refine Finset.sum_congr rfl fun b _ => ?_
          have hsucc : b.succ = ⟨b.1 + 1, by omega⟩ := Fin.ext rfl
          rw [hsucc, evalExpPoly_mul, evalExpPoly_mul, evalExpPoly_mul, evalExpPoly_single,
            expIntPS_zero, mul_one, h1mT_eval, Algebra.smul_def, poly_coe_natCast,
            PowerSeries.C_eq_algebraMap]
          ring
        rw [hS1, hS2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        dsimp [H]
        rw [evalExpPoly_add, add_mul]
      have hHlast : H ⟨B, Nat.lt_succ_self _⟩ = 0 := ih H hHsum ⟨B, Nat.lt_succ_self _⟩
      exact expPoly_wronskian_ne_zero (G ⟨B, by omega⟩) GB (B + 1) (Nat.succ_pos B) htop hHlast

lemma fPS_linearIndependent {n : ℕ} (P : Idx n → ℝ[X])
    (h : ∑ p : Idx n, ((P p : ℝ[X]) : PowerSeries ℝ) * fPS p = 0) :
    ∀ p : Idx n, P p = 0 := by
  let G : Fin (n + 1) → ExpPoly := fun b =>
    ∑ p ∈ Finset.univ.filter (fun p : Idx n => p.1.2 = b),
      AddMonoidAlgebra.single (-(p.1.1.1 : ℤ)) (P p)
  have hGsum : (∑ b : Fin (n + 1), evalExpPoly (G b) * einPS ^ b.1) = 0 := by
    rw [← h]
    have hsplit : ∀ b : Fin (n + 1),
        evalExpPoly (G b) * einPS ^ b.1 =
          ∑ p ∈ Finset.univ.filter (fun p : Idx n => p.1.2 = b),
            ((P p : ℝ[X]) : PowerSeries ℝ) * fPS p := by
      intro b
      have hev : evalExpPoly (G b) =
          ∑ p ∈ Finset.univ.filter (fun p : Idx n => p.1.2 = b),
            ((P p : ℝ[X]) : PowerSeries ℝ) * expNegPS p.1.1.1 := by
        dsimp [G]
        have hlin : ∀ (s : Finset (Idx n)) (f : Idx n → ExpPoly),
            evalExpPoly (∑ p ∈ s, f p) = ∑ p ∈ s, evalExpPoly (f p) := by
          intro s f
          induction s using Finset.cons_induction with
          | empty => simp [evalExpPoly]
          | cons a s ha ihs => rw [Finset.sum_cons, Finset.sum_cons, evalExpPoly_add, ihs]
        rw [hlin]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [evalExpPoly_single, expIntPS_neg_nat]
      rw [hev, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpb : p.1.2 = b := (Finset.mem_filter.mp hp).2
      rw [fPS_eq_mul_pow, hpb, mul_assoc]
    simp_rw [hsplit]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Idx n => p.1.2)
      (fun _ _ => Finset.mem_univ _)]
  have hG0 := einPS_alg_indep_over_expPoly n G hGsum
  intro p
  have hGp := congrArg (fun E : ExpPoly => E.coeff (-(p.1.1.1 : ℤ))) (hG0 p.1.2)
  simp only [G, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.single,
    Finsupp.finsetSum_apply, Finsupp.single_apply,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hGp
  rw [Finset.sum_eq_single p] at hGp
  · simpa using hGp
  · intro q hq hqp
    have hqb : q.1.2 = p.1.2 := (Finset.mem_filter.mp hq).2
    have hqa : q.1.1.1 ≠ p.1.1.1 := by
      intro hqa
      apply hqp
      apply Subtype.ext
      exact Prod.ext (Fin.ext hqa) hqb
    rw [if_neg (by omega)]
  · intro hp
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ p, rfl⟩ :
      p ∈ Finset.univ.filter fun q : Idx n => q.1.2 = p.1.2) hp

/- ### Section 4: Siegel's Lemma and Padé-type approximating forms -/

lemma siegel_lemma {ι : Type*} [Fintype ι] [DecidableEq ι] {M H B : ℕ}
    (A : Fin M → ι → ℤ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ))
    (hcard : (2 * Fintype.card ι * B * H + 1) ^ M < (H + 1) ^ Fintype.card ι) :
    ∃ x : ι → ℤ, (∃ j, x j ≠ 0) ∧ (∀ j, |x j| ≤ (H : ℤ)) ∧
      ∀ i : Fin M, ∑ j : ι, A i j * x j = 0 := by
  let U := Fintype.card ι
  let L : ℤ := (U : ℤ) * (B : ℤ) * (H : ℤ)
  have hbound : ∀ (y : ι → Fin (H + 1)) (i : Fin M),
      -L ≤ ∑ j : ι, A i j * (y j : ℤ) ∧ ∑ j : ι, A i j * (y j : ℤ) ≤ L := by
    intro y i
    have habs : |∑ j : ι, A i j * (y j : ℤ)| ≤ L := by
      calc |∑ j : ι, A i j * (y j : ℤ)|
          ≤ ∑ j : ι, |A i j * (y j : ℤ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : ι, (B : ℤ) * (H : ℤ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (a := ((y j).1 : ℤ)) (Nat.cast_nonneg _)]
            have hy : ((y j).1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast Nat.le_of_lt_succ (y j).2
            exact mul_le_mul (hA i j) hy (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = L := by simp [L, U, mul_assoc]
    exact abs_le.mp habs
  let f : (ι → Fin (H + 1)) → (Fin M → Fin (2 * U * B * H + 1)) := fun y i =>
    ⟨Int.toNat (∑ j : ι, A i j * (y j : ℤ) + L), by
      have hb := hbound y i
      have h1 : 0 ≤ ∑ j : ι, A i j * (y j : ℤ) + L := by linarith
      have h2 : ∑ j : ι, A i j * (y j : ℤ) + L ≤ 2 * L := by linarith
      have h3 : ((2 * L : ℤ)) = ((2 * U * B * H : ℕ) : ℤ) := by simp [L]; ring
      omega⟩
  have hlt : Fintype.card (Fin M → Fin (2 * U * B * H + 1)) < Fintype.card (ι → Fin (H + 1)) := by
    simpa [U] using hcard
  obtain ⟨y1, y2, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  refine ⟨fun j => ((y1 j).1 : ℤ) - ((y2 j).1 : ℤ), ?_, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hne
    funext j
    have hj := hall j
    exact Fin.ext (by omega)
  · intro j
    dsimp only
    have h1 : (y1 j).1 ≤ H := Nat.le_of_lt_succ (y1 j).2
    have h2 : (y2 j).1 ≤ H := Nat.le_of_lt_succ (y2 j).2
    rw [abs_le]
    omega
  · intro i
    have hi := congrArg (fun g => (g i).1) hfeq
    dsimp [f] at hi
    have hb1 := hbound y1 i
    have hb2 := hbound y2 i
    have h1 : (Int.toNat (∑ j : ι, A i j * (y1 j : ℤ) + L) : ℤ) =
        ∑ j : ι, A i j * (y1 j : ℤ) + L := Int.toNat_of_nonneg (by linarith)
    have h2 : (Int.toNat (∑ j : ι, A i j * (y2 j : ℤ) + L) : ℤ) =
        ∑ j : ι, A i j * (y2 j : ℤ) + L := Int.toNat_of_nonneg (by linarith)
    have heq : ∑ j : ι, A i j * (y1 j : ℤ) = ∑ j : ι, A i j * (y2 j : ℤ) := by
      have : (Int.toNat (∑ j : ι, A i j * (y1 j : ℤ) + L) : ℤ) =
          (Int.toNat (∑ j : ι, A i j * (y2 j : ℤ) + L) : ℤ) := by exact_mod_cast hi
      linarith
    calc ∑ j : ι, A i j * (((y1 j).1 : ℤ) - ((y2 j).1 : ℤ))
        = ∑ j : ι, (A i j * (y1 j : ℤ) - A i j * (y2 j : ℤ)) := by
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j : ι, A i j * (y1 j : ℤ)) - ∑ j : ι, A i j * (y2 j : ℤ) := Finset.sum_sub_distrib _ _
      _ = 0 := sub_eq_zero.mpr heq

/-- Construct the Padé-type approximating polynomial vector `P0 : Idx n → ℤ[X]` of degree `≤ N`
with `P0 p = ∑ j : Fin (N + 1), (N! / j!) * ptilde (p, j) * X^j`, `|ptilde| ≤ C4^N`,
and vanishing order `≥ M = m * (N + 1) - N / (4 * m)`. -/
lemma exists_pade_form (n : ℕ) :
    ∃ C4 : ℕ, 1 ≤ C4 ∧
      ∀ N : ℕ, 8 * Fintype.card (Idx n) ≤ N →
        let m := Fintype.card (Idx n)
        let M := m * (N + 1) - N / (4 * m)
        ∃ ptilde : Idx n × Fin (N + 1) → ℤ,
          (∃ x, ptilde x ≠ 0) ∧
          (∀ x, |ptilde x| ≤ (C4 ^ N : ℤ)) ∧
          (let P0 : Idx n → ℤ[X] := fun p =>
              ∑ j : Fin (N + 1),
                Polynomial.C (((N.factorial / j.1.factorial : ℕ) : ℤ) * ptilde (p, j)) *
                  Polynomial.X ^ j.1
            ∀ k < M,
              PowerSeries.coeff k
                (∑ p : Idx n, (((P0 p).map (Int.castRingHom ℝ) : ℝ[X]) : PowerSeries ℝ) * fPS p) = 0) := by
  let m := Fintype.card (Idx n)
  have hm_pos : 0 < m := by
    dsimp [m]; rw [card_idx]; exact Nat.div_pos (by nlinarith) (by norm_num)
  -- Base constant `C0` for matrix entries `B = C0 ^ M`, and `C1` for `2 * U * B + 1 ≤ C1 ^ N`
  let C0 : ℕ := 2 * 256 ^ n * (n + 1)
  have hC0_pos : 1 ≤ C0 := by
    have h256 : 1 ≤ 256 ^ n := Nat.one_le_pow n 256 (by norm_num)
    dsimp [C0]; nlinarith
  let C1 : ℕ := 4 * m * C0 ^ (2 * m) + 1
  have hC1_pos : 1 ≤ C1 := by dsimp [C1]; omega
  let C4 : ℕ := C1 ^ (16 * m ^ 2)
  have hC4_pos : 1 ≤ C4 := Nat.one_le_pow _ _ hC1_pos
  refine ⟨C4, hC4_pos, ?_⟩
  intro N hN
  dsimp only
  let δ := N / (4 * m)
  let M := m * (N + 1) - δ
  let U := Fintype.card (Idx n × Fin (N + 1))
  have hU : U = m * (N + 1) := by simp [U, m]
  have hδ_ge : 2 ≤ δ := by
    dsimp [δ]
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
  have hδ_le : δ ≤ N := Nat.div_le_self N (4 * m)
  have hM_le_U : M ≤ U := by dsimp [M]; omega
  have hM_le_2mN : M ≤ 2 * m * N := by
    have : m * (N + 1) ≤ 2 * m * N := by nlinarith
    dsimp [M]; omega
  -- Extract exact integer numerators `zInt p r` for `(Nat.lcmUpto M)^n * cQ p r` (`r ≤ M`)
  have hz_ex : ∀ (p : Idx n) (r : Fin (M + 1)),
      ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto M : ℚ) ^ n) * cQ p r.1 :=
    fun p r => cQ_denom_int p (Nat.le_of_lt_succ r.2)
  choose zInt hzInt using hz_ex
  let A : Fin M → Idx n × Fin (N + 1) → ℤ := fun k x =>
    if hjk : x.2.1 ≤ k.1 then
      (k.1.choose x.2.1 : ℤ) * zInt x.1 ⟨k.1 - x.2.1, by omega⟩
    else 0
  let B : ℕ := C0 ^ M
  have hA_bound : ∀ (k : Fin M) (x : Idx n × Fin (N + 1)), |A k x| ≤ (B : ℤ) := by
    intro k ⟨p, j⟩
    dsimp only [A]
    split_ifs with hjk
    · have hch : k.1.choose j.1 ≤ 2 ^ M :=
        (Nat.choose_le_two_pow k.1 j.1).trans (Nat.pow_le_pow_right (by norm_num) k.2.le)
      have hzQ : |(zInt p ⟨k.1 - j.1, by omega⟩ : ℚ)| ≤
          ((256 ^ n * (n + 1) : ℕ) : ℚ) ^ M := by
        rw [hzInt, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
        have hlcm : (Nat.lcmUpto M : ℚ) ≤ (256 : ℚ) ^ M := by exact_mod_cast lcmUpto_le_pow M
        have hlcm_pow : (Nat.lcmUpto M : ℚ) ^ n ≤ ((256 : ℚ) ^ M) ^ n :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hlcm n
        have hc_le : |cQ p (k.1 - j.1)| ≤ ((n + 1 : ℕ) : ℚ) ^ M := by
          have h1 := cQ_abs_le p (k.1 - j.1)
          have h2 : ((n : ℚ) + 1) ^ (k.1 - j.1) ≤ ((n : ℚ) + 1) ^ M :=
            pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℚ) n]) (by omega)
          simpa using h1.trans h2
        calc (Nat.lcmUpto M : ℚ) ^ n * |cQ p (k.1 - j.1)|
            ≤ ((256 : ℚ) ^ M) ^ n * ((n + 1 : ℕ) : ℚ) ^ M :=
              mul_le_mul hlcm_pow hc_le (abs_nonneg _) (by positivity)
          _ = ((256 ^ n * (n + 1) : ℕ) : ℚ) ^ M := by
              rw [← pow_mul, mul_comm M n, pow_mul, ← mul_pow]; push_cast; rfl
      have hprodQ : (|(k.1.choose j.1 : ℤ) * zInt p ⟨k.1 - j.1, by omega⟩| : ℚ) ≤ (B : ℚ) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.1.choose j.1))]
        calc (k.1.choose j.1 : ℚ) * |(zInt p ⟨k.1 - j.1, by omega⟩ : ℚ)|
            ≤ (2 : ℚ) ^ M * ((256 ^ n * (n + 1) : ℕ) : ℚ) ^ M :=
              mul_le_mul (by exact_mod_cast hch) hzQ (abs_nonneg _) (by positivity)
          _ = (B : ℚ) := by
              dsimp [B, C0]; rw [← mul_pow]; push_cast; ring
      exact_mod_cast hprodQ
    · simp
  let K : ℕ := 2 * U * B + 1
  let H : ℕ := K ^ (16 * m ^ 2)
  have hK_le : K ≤ C1 ^ N := by
    have hB_le : B ≤ (C0 ^ (2 * m)) ^ N := by
      dsimp [B]; rw [← pow_mul]; exact Nat.pow_le_pow_right hC0_pos hM_le_2mN
    have h2U_le : 2 * U ≤ 4 * m * N := by rw [hU]; nlinarith
    have hN_le_pow : N ≤ 2 ^ N := Nat.le_of_lt Nat.lt_two_pow_self
    have h1 : 2 * U * B + 1 ≤ (4 * m * 2 ^ N) * (C0 ^ (2 * m)) ^ N + 1 := by
      have ha : 2 * U * B ≤ (4 * m * N) * (C0 ^ (2 * m)) ^ N := Nat.mul_le_mul h2U_le hB_le
      have hb : (4 * m * N) * (C0 ^ (2 * m)) ^ N ≤ (4 * m * 2 ^ N) * (C0 ^ (2 * m)) ^ N :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hN_le_pow)
      exact Nat.add_le_add_right (ha.trans hb) 1
    have h4m_pow : 4 * m * 2 ^ N ≤ (4 * m) ^ N := by
      have h4m_ge4 : 4 ≤ 4 * m := by omega
      have h1N : 1 ≤ N := by omega
      have hsplit : (4 * m) ^ N = (4 * m) * (4 * m) ^ (N - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel h1N, pow_succ']
      rw [hsplit]
      refine Nat.mul_le_mul_left (4 * m) ?_
      have hpow2 : 2 ^ N = 2 * 2 ^ (N - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel h1N, pow_succ']
      rw [hpow2]
      have h4_le : 2 * 2 ^ (N - 1) ≤ 4 ^ (N - 1) := by
        have hN1 : 1 ≤ N - 1 := by omega
        have h21 : 2 ≤ 2 ^ (N - 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) hN1
        calc 2 * 2 ^ (N - 1) ≤ 2 ^ (N - 1) * 2 ^ (N - 1) := Nat.mul_le_mul_right _ h21
          _ = (2 * 2) ^ (N - 1) := (Nat.mul_pow 2 2 (N - 1)).symm
          _ = 4 ^ (N - 1) := by norm_num
      exact h4_le.trans (Nat.pow_le_pow_left h4m_ge4 (N - 1))
    have h2 : (4 * m * 2 ^ N) * (C0 ^ (2 * m)) ^ N ≤ (4 * m * C0 ^ (2 * m)) ^ N := by
      have hmp : (4 * m * C0 ^ (2 * m)) ^ N = (4 * m) ^ N * (C0 ^ (2 * m)) ^ N :=
        Nat.mul_pow (4 * m) (C0 ^ (2 * m)) N
      rw [hmp]
      exact Nat.mul_le_mul_right ((C0 ^ (2 * m)) ^ N) h4m_pow
    have hpow_succ_add : ∀ (a k : ℕ), 1 ≤ k → a ^ k + 1 ≤ (a + 1) ^ k := by
      intro a k hk
      induction k with
      | zero => omega
      | succ k ihk =>
        cases k with
        | zero => simp
        | succ k' =>
          have hih := ihk (Nat.succ_pos k')
          rw [pow_succ, pow_succ]
          have hle1 : a ^ (k' + 1) * a + 1 ≤ (a ^ (k' + 1) + 1) * (a + 1) := by
            calc a ^ (k' + 1) * a + 1
                ≤ a ^ (k' + 1) * a + a ^ (k' + 1) + a + 1 := by omega
              _ = (a ^ (k' + 1) + 1) * (a + 1) := by ring
          have hle2 : (a ^ (k' + 1) + 1) * (a + 1) ≤ (a + 1) ^ (k' + 1) * (a + 1) :=
            Nat.mul_le_mul_right (a + 1) hih
          exact hle1.trans hle2
    have h3 : (4 * m * C0 ^ (2 * m)) ^ N + 1 ≤ C1 ^ N :=
      hpow_succ_add (4 * m * C0 ^ (2 * m)) N (by omega)
    exact (h1.trans (Nat.add_le_add_right h2 1)).trans h3
  have hH_le : H ≤ C4 ^ N := by
    have hC4_eq : C4 ^ N = (C1 ^ N) ^ (16 * m ^ 2) := by
      show (C1 ^ (16 * m ^ 2)) ^ N = (C1 ^ N) ^ (16 * m ^ 2)
      rw [← pow_mul, mul_comm (16 * m ^ 2) N, pow_mul]
    rw [hC4_eq]
    exact Nat.pow_le_pow_left hK_le (16 * m ^ 2)
  have hM_le_16 : M ≤ 16 * m ^ 2 * δ := by
    have hN_le : N ≤ 4 * m * (δ + 1) := by
      have := Nat.lt_mul_div_succ N (show 0 < 4 * m by positivity)
      dsimp [δ]; omega
    have hδ1 : δ + 1 ≤ 2 * δ := by omega
    have hN_le2 : N ≤ 8 * m * δ := by nlinarith
    have hM_le_2mN' : M ≤ 2 * m * N := hM_le_2mN
    nlinarith
  have hcard : (2 * U * B * H + 1) ^ M < (H + 1) ^ U := by
    have hstep1 : 2 * U * B * H + 1 ≤ K * (H + 1) := by
      have hKe : K = 2 * U * B + 1 := rfl
      calc 2 * U * B * H + 1
          ≤ 2 * U * B * H + 2 * U * B + H + 1 := by omega
        _ = (2 * U * B + 1) * (H + 1) := by ring
        _ = K * (H + 1) := by rw [← hKe]
    have h1 : (2 * U * B * H + 1) ^ M ≤ K ^ M * (H + 1) ^ M := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hstep1 M
    have hK_pos : 1 ≤ K := Nat.le_add_left 1 (2 * U * B)
    have h2 : K ^ M < (H + 1) ^ δ := by
      calc K ^ M
          ≤ K ^ (16 * m ^ 2 * δ) := Nat.pow_le_pow_right hK_pos hM_le_16
        _ = H ^ δ := by show K ^ (16 * m ^ 2 * δ) = (K ^ (16 * m ^ 2)) ^ δ; rw [pow_mul]
        _ < (H + 1) ^ δ := Nat.pow_lt_pow_left (Nat.lt_succ_self H) (by omega)
    have h3 : K ^ M * (H + 1) ^ M < (H + 1) ^ δ * (H + 1) ^ M :=
      Nat.mul_lt_mul_of_pos_right h2 (Nat.pow_pos (Nat.succ_pos H))
    have h4 : (H + 1) ^ δ * (H + 1) ^ M = (H + 1) ^ U := by
      have hδM : δ + M = U := by
        rw [hU]
        have hδU : δ ≤ m * (N + 1) := hδ_le.trans (by nlinarith)
        dsimp [M]; omega
      rw [← pow_add, hδM]
    exact lt_of_le_of_lt h1 (h4 ▸ h3)
  obtain ⟨ptilde, hne, hbd, hsys⟩ := siegel_lemma A hA_bound hcard
  refine ⟨ptilde, hne, fun x => (hbd x).trans (by exact_mod_cast hH_le), ?_⟩
  intro k hkM
  have hkM' : k < M := hkM
  rw [map_sum]
  let ptildeNat : Idx n → ℕ → ℤ := fun p i => if hi : i < N + 1 then ptilde (p, ⟨i, hi⟩) else 0
  have hcoeff_term : ∀ p : Idx n,
      PowerSeries.coeff k
        ((((∑ j : Fin (N + 1),
              Polynomial.C (((N.factorial / j.1.factorial : ℕ) : ℤ) * ptilde (p, j)) *
                Polynomial.X ^ j.1).map (Int.castRingHom ℝ) : ℝ[X]) : PowerSeries ℝ) * fPS p) =
      ((N.factorial : ℝ) / ((k.factorial : ℝ) * ((Nat.lcmUpto M : ℝ) ^ n))) *
        ∑ j : Fin (N + 1), (A ⟨k, hkM'⟩ (p, j) : ℝ) * (ptilde (p, j) : ℝ) := by
    intro p
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    have hpoly_coeff : ∀ i : ℕ,
        PowerSeries.coeff i
          (((∑ j : Fin (N + 1),
              Polynomial.C (((N.factorial / j.1.factorial : ℕ) : ℤ) * ptilde (p, j)) *
                Polynomial.X ^ j.1).map (Int.castRingHom ℝ) : ℝ[X]) : PowerSeries ℝ) =
        if i < N + 1 then
          ((N.factorial / i.factorial : ℕ) : ℝ) * (ptildeNat p i : ℝ)
        else 0 := by
      intro i
      rw [Polynomial.coeff_coe, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      by_cases hi : i < N + 1
      · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin (N + 1))]
        · simp only [↓reduceIte, Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast, ptildeNat, hi,
            ↓reduceDIte]
        · intro j _ hji
          have hne' : i ≠ j.1 := fun h => hji (Fin.ext h.symm)
          simp [hne']
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hi]
        have hz : (∑ j : Fin (N + 1),
            if i = j.1 then ((N.factorial / j.1.factorial : ℕ) : ℤ) * ptilde (p, j) else 0) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          have hne' : i ≠ j.1 := by omega
          simp [hne']
        rw [hz]; simp
    simp_rw [hpoly_coeff, coeff_fPS_eq_cQ]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hlhs : (∑ i ∈ Finset.range (k + 1),
        (if i < N + 1 then
          ((N.factorial / i.factorial : ℕ) : ℝ) * (ptildeNat p i : ℝ)
        else 0) * ((cQ p (k - i) : ℝ) / ((k - i).factorial : ℝ))) =
        ∑ j : Fin (N + 1),
          if j.1 ≤ k then
            ((N.factorial / j.1.factorial : ℕ) : ℝ) * (ptilde (p, j) : ℝ) *
              ((cQ p (k - j.1) : ℝ) / ((k - j.1).factorial : ℝ))
          else 0 := by
      have h1 : ∀ i ∈ Finset.range (k + 1),
          (if i < N + 1 then
            ((N.factorial / i.factorial : ℕ) : ℝ) * (ptildeNat p i : ℝ)
          else 0) * ((cQ p (k - i) : ℝ) / ((k - i).factorial : ℝ)) =
          if i < N + 1 then
            ((N.factorial / i.factorial : ℕ) : ℝ) * (ptildeNat p i : ℝ) *
              ((cQ p (k - i) : ℝ) / ((k - i).factorial : ℝ))
          else 0 := by
        intro i _; split_ifs <;> simp
      rw [Finset.sum_congr rfl h1]
      rw [← Finset.sum_filter (p := fun i => i < N + 1)]
      symm
      rw [← Finset.sum_filter (p := fun j : Fin (N + 1) => j.1 ≤ k)]
      refine Finset.sum_bij (fun j _ => j.1) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), j.2⟩
      · intro j1 _ j2 _ h; exact Fin.ext h
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        exact ⟨⟨i, hi.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, rfl⟩
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [ptildeNat, j.2, ↓reduceDIte]
    rw [hlhs]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [A]
    split_ifs with hjk
    · have hdiv_fac : ((N.factorial / j.1.factorial : ℕ) : ℝ) =
          (N.factorial : ℝ) / (j.1.factorial : ℝ) := by
        have hdvd : j.1.factorial ∣ N.factorial :=
          Nat.factorial_dvd_factorial (Nat.le_of_lt_succ j.2)
        have hmul : (N.factorial / j.1.factorial : ℕ) * j.1.factorial = N.factorial :=
          Nat.div_mul_cancel hdvd
        have hfj : (j.1.factorial : ℝ) ≠ 0 := by positivity
        have hmulR : ((N.factorial / j.1.factorial : ℕ) : ℝ) * (j.1.factorial : ℝ) =
            (N.factorial : ℝ) := by exact_mod_cast hmul
        exact eq_div_of_mul_eq hfj hmulR
      have hch : (k.choose j.1 : ℝ) * (j.1.factorial : ℝ) * ((k - j.1).factorial : ℝ) =
          (k.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjk
      have hkj_lt : k - j.1 < M + 1 := by omega
      have hzR : (zInt p ⟨k - j.1, hkj_lt⟩ : ℝ) =
          ((Nat.lcmUpto M : ℝ) ^ n) * (cQ p (k - j.1) : ℝ) := by
        exact_mod_cast hzInt p ⟨k - j.1, hkj_lt⟩
      have hfj : (j.1.factorial : ℝ) ≠ 0 := by positivity
      have hfkj : ((k - j.1).factorial : ℝ) ≠ 0 := by positivity
      have hfk : (k.factorial : ℝ) ≠ 0 := by positivity
      have hch_ne : (k.choose j.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
      have hlcm : ((Nat.lcmUpto M : ℝ) ^ n) ≠ 0 := by
        have : (0 : ℝ) < (Nat.lcmUpto M : ℝ) := by exact_mod_cast Nat.lcmUpto_pos M
        positivity
      rw [hdiv_fac, Int.cast_mul, Int.cast_natCast, hzR, ← hch]
      field_simp [hfj, hfkj, hlcm, hch_ne]
    · simp
  simp_rw [hcoeff_term]
  rw [← Finset.mul_sum]
  have hsum0 : (∑ p : Idx n, ∑ j : Fin (N + 1), (A ⟨k, hkM'⟩ (p, j) : ℝ) * (ptilde (p, j) : ℝ)) = 0 := by
    have hZ := hsys ⟨k, hkM'⟩
    rw [Fintype.sum_prod_type] at hZ
    have hR : ((∑ p : Idx n, ∑ j : Fin (N + 1), A ⟨k, hkM⟩ (p, j) * ptilde (p, j) : ℤ) : ℝ) = 0 := by
      exact_mod_cast hZ
    simpa [Int.cast_sum, Int.cast_mul] using hR
  rw [hsum0, mul_zero]

/- ### Section 5: Shidlovskii Zero-Order Lemma and Row-Shift Lemma -/

noncomputable def Lrow {n : ℕ} (w : Idx n → ℝ[X]) : Idx n → ℝ[X] :=
  fun p => Polynomial.X * (w p).derivative + ∑ q : Idx n, w q * AmatR n q p

lemma Lrow_add {n : ℕ} (w1 w2 : Idx n → ℝ[X]) :
    Lrow (w1 + w2) = Lrow w1 + Lrow w2 := by
  funext p
  simp only [Lrow, Pi.add_apply, Polynomial.derivative_add, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma poly_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    ((∑ i ∈ s, f i : ℝ[X]) : PowerSeries ℝ) = ∑ i ∈ s, ((f i : ℝ[X]) : PowerSeries ℝ) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Polynomial.coe_add, ih]

lemma Lrow_smul {n : ℕ} (g : ℝ[X]) (w : Idx n → ℝ[X]) :
    Lrow (g • w) = (Polynomial.X * g.derivative) • w + g • Lrow w := by
  funext p
  simp only [Lrow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.derivative_mul]
  rw [mul_add, mul_add, Finset.mul_sum]
  have hsum : (∑ q : Idx n, g * w q * AmatR n q p) = ∑ q : Idx n, g * (w q * AmatR n q p) := by
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [hsum]
  ring

noncomputable def vZ {n : ℕ} (P0 : Idx n → ℤ[X]) : ℕ → (Idx n → ℤ[X])
  | 0 => P0
  | k + 1 => fun p => Polynomial.X * (vZ P0 k p).derivative +
      ∑ q : Idx n, vZ P0 k q * AmatZ n q p

noncomputable def vR {n : ℕ} (P0 : Idx n → ℤ[X]) (k : ℕ) (p : Idx n) : ℝ[X] :=
  (vZ P0 k p).map (Int.castRingHom ℝ)

lemma vR_succ {n : ℕ} (P0 : Idx n → ℤ[X]) (k : ℕ) :
    vR P0 (k + 1) = Lrow (vR P0 k) := by
  funext p
  simp only [vR, vZ, Lrow, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.derivative_map, Polynomial.map_sum, AmatR, Matrix.map_apply]

noncomputable def Rseq {n : ℕ} (P0 : Idx n → ℤ[X]) (k : ℕ) : PowerSeries ℝ :=
  ∑ p : Idx n, ((vR P0 k p : ℝ[X]) : PowerSeries ℝ) * fPS p

lemma Dps_poly_comb {n : ℕ} (w : Idx n → ℝ[X]) :
    Dps (∑ p : Idx n, ((w p : ℝ[X]) : PowerSeries ℝ) * fPS p) =
      ∑ p : Idx n, ((Lrow w p : ℝ[X]) : PowerSeries ℝ) * fPS p := by
  rw [Dps_sum]
  simp_rw [Dps_mul, Dps_poly, Dps_fPS, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Lrow, Polynomial.coe_add, poly_coe_sum, Polynomial.coe_mul, add_mul,
    Finset.sum_mul, mul_assoc]

lemma Dps_Rseq {n : ℕ} (P0 : Idx n → ℤ[X]) (k : ℕ) :
    Dps (Rseq P0 k) = Rseq P0 (k + 1) := by
  rw [Rseq, Rseq, vR_succ, Dps_poly_comb]

lemma coeff_Rseq {n : ℕ} (P0 : Idx n → ℤ[X]) (k j : ℕ) :
    PowerSeries.coeff j (Rseq P0 k) = (j : ℝ) ^ k * PowerSeries.coeff j (Rseq P0 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Dps_Rseq, coeff_Dps, ih, pow_succ']
    ring

lemma natDegree_vR_le {n N : ℕ} (P0 : Idx n → ℤ[X])
    (h0 : ∀ p : Idx n, (vR P0 0 p).natDegree ≤ N) :
    ∀ k p, (vR P0 k p).natDegree ≤ N + k := by
  intro k
  induction k with
  | zero => intro p; simpa using h0 p
  | succ k ih =>
    intro p
    rw [vR_succ]
    unfold Lrow
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · by_cases hd : (vR P0 k p).derivative = 0
      · simp [hd]
      · have h1 := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := (vR P0 k p).derivative)
        have h2 : ((vR P0 k p).derivative).natDegree ≤ (vR P0 k p).natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
        have h3 := ih p
        simp only [Polynomial.natDegree_X] at h1
        omega
    · refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun q _ => ?_⟩
      exact (Polynomial.natDegree_mul_le).trans (by
        have h1 := ih q
        have h2 := AmatR_natDegree_le_one n q p
        omega)

/-- From a spanning family of vectors in `α → K` over a field `K`, extract a square submatrix
with nonzero determinant. -/
lemma exists_submatrix_det_ne_zero_of_span_top {K : Type*} [Field K]
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (M : Matrix β α K) (hspan : Submodule.span K (Set.range M) = ⊤) :
    ∃ f : α → β, (M.submatrix f id).det ≠ 0 := by
  classical
  obtain ⟨s, hs_sub, hspan_s, hli_s⟩ := exists_linearIndependent K (Set.range M)
  rw [hspan] at hspan_s
  let b : Module.Basis s K (α → K) := Module.Basis.mk hli_s (by rw [Subtype.range_coe, hspan_s])
  let _ : Fintype (Set.range M) := Set.fintypeRange M
  let _ : Fintype s := Set.fintypeSubset (Set.range M) hs_sub
  have hcard : Fintype.card s = Fintype.card α := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi] at h1
    exact h1.symm
  let e : α ≃ s := (Fintype.equivOfCardEq hcard).symm
  have hmem : ∀ a : α, (e a).1 ∈ Set.range M := fun a => hs_sub (e a).2
  choose f hf using hmem
  refine ⟨f, ?_⟩
  have hli : LinearIndependent K (fun a : α => M (f a)) := by
    have hcomp : (fun a : α => M (f a)) = (fun x : s => (x : α → K)) ∘ e := by
      funext a; exact hf a
    rw [hcomp]
    exact hli_s.comp e e.injective
  have hsub : (M.submatrix f id) = Matrix.of (fun a : α => M (f a)) := rfl
  rw [hsub]
  intro hdet
  have hdetT : (Matrix.of (fun a : α => M (f a)))ᵀ.det = 0 := by
    rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hvsum : ∑ a : α, v a • M (f a) = 0 := by
    funext j
    have hj := congrArg (fun u : α → K => u j) hv0
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hj
  have := (Fintype.linearIndependent_iff.mp hli) v hvsum
  exact hv_ne (funext this)

/-- Any `r × m` matrix over `ℝ[X]` with `ℝ[X]`-linearly independent rows has a nonzero `r × r` minor. -/
lemma exists_cols_det_ne_zero {n r : ℕ} (U : Matrix (Fin r) (Idx n) ℝ[X])
    (hli : LinearIndependent ℝ[X] (fun i : Fin r => U i)) :
    ∃ cols : Fin r → Idx n, (U.submatrix id cols).det ≠ 0 := by
  let K := FractionRing ℝ[X]
  let emb : ℝ[X] →+* K := algebraMap ℝ[X] K
  have hemb_inj : Function.Injective emb := IsFractionRing.injective ℝ[X] K
  let UK : Matrix (Fin r) (Idx n) K := U.map emb
  have hliK : LinearIndependent K (fun i : Fin r => UK i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨⟨d, hd⟩, hc_int⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℝ[X])
      (Finset.univ : Finset (Fin r)) c
    have hd_ne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
    choose a ha using fun i : Fin r => hc_int i (Finset.mem_univ i)
    have ha' : ∀ i : Fin r, emb (a i) = emb d * c i := by
      intro i
      simpa [emb, Submonoid.smul_def, Algebra.smul_def] using ha i
    have hsumR : ∑ i : Fin r, a i • U i = 0 := by
      funext p
      apply hemb_inj
      rw [Pi.zero_apply, map_zero, Finset.sum_apply, map_sum]
      have hcp := congrArg (fun f : Idx n → K => emb d * f p) hc
      rw [Pi.zero_apply, mul_zero, Finset.sum_apply, Finset.mul_sum] at hcp
      rw [← hcp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, UK, Matrix.map_apply]
      rw [ha' i]
      ring
    have ha0 := Fintype.linearIndependent_iff.mp hli a hsumR
    intro i
    have hda : emb d * c i = 0 := by rw [← ha' i, ha0 i, map_zero]
    exact (mul_eq_zero.mp hda).resolve_left (fun h0 => hd_ne (hemb_inj (by rwa [map_zero])))
  have hspan : Submodule.span K (Set.range UKᵀ) = ⊤ := by
    by_contra hne
    let W := Submodule.span K (Set.range UKᵀ)
    obtain ⟨W', hcompl⟩ := Submodule.exists_isCompl W
    have hW'_ne : W' ≠ ⊥ := by
      intro hbot
      apply hne
      have h1 := hcompl.sup_eq_top
      rw [hbot, sup_bot_eq] at h1
      exact h1
    obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'_ne
    let bW' := Module.Basis.ofVectorSpace K W'
    have hrepr_ne : ∃ j, bW'.repr ⟨v, hv_mem⟩ j ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : (⟨v, hv_mem⟩ : W') = 0 := by
        rw [← bW'.sum_repr ⟨v, hv_mem⟩]
        simp [hall]
      exact hv_ne (congrArg Subtype.val h0)
    obtain ⟨j0, hj0⟩ := hrepr_ne
    let proj : (Fin r → K) →ₗ[K] W' := Submodule.projectionOnto W' W hcompl.symm
    let ψ : (Fin r → K) →ₗ[K] K := (bW'.coord j0).comp proj
    have hψ_W : ∀ w ∈ W, ψ w = 0 := by
      intro w hw
      have hp0 : proj w = 0 := Submodule.projectionOnto_apply_right hcompl.symm ⟨w, hw⟩
      simp [ψ, hp0]
    have hψ_v : ψ v ≠ 0 := by
      have hpv : proj v = ⟨v, hv_mem⟩ := Submodule.projectionOnto_apply_left hcompl.symm ⟨v, hv_mem⟩
      simpa [ψ, hpv] using hj0
    let x : Fin r → K := fun i => ψ (Pi.single i 1)
    have hx_ne : x ≠ 0 := by
      intro hx0
      apply hψ_v
      have hv_sum : v = ∑ i : Fin r, v i • Pi.single i (1 : K) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hv_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, show ψ (Pi.single i 1) = x i from rfl, hx0, Pi.zero_apply, smul_zero]
    have hx_rel : ∑ i : Fin r, x i • UK i = 0 := by
      funext p
      have hmem : UKᵀ p ∈ W := Submodule.subset_span ⟨p, rfl⟩
      have h0 := hψ_W (UKᵀ p) hmem
      have hdec : UKᵀ p = ∑ i : Fin r, (UK i p) • Pi.single i (1 : K) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, Matrix.transpose_apply]
      rw [hdec, map_sum] at h0
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simpa [x, map_smul, smul_eq_mul, mul_comm] using h0
    exact hx_ne (funext (Fintype.linearIndependent_iff.mp hliK x hx_rel))
  obtain ⟨cols, hdetK⟩ := exists_submatrix_det_ne_zero_of_span_top UKᵀ hspan
  refine ⟨cols, ?_⟩
  intro hdet0
  apply hdetK
  have hmap : (UKᵀ.submatrix cols id) = ((U.submatrix id cols)ᵀ).map emb := by
    apply Matrix.ext; intro i j; simp [UK]
  rw [hmap]
  exact (RingHom.map_det emb (U.submatrix id cols)ᵀ).symm.trans
    (by rw [Matrix.det_transpose, hdet0, map_zero])

/-- Degree bound for the determinant of an `r × r` matrix whose `i`-th row has degree `≤ N + i`. -/
lemma natDegree_det_le_of_row_deg {r N : ℕ} (V : Matrix (Fin r) (Fin r) ℝ[X])
    (hdeg : ∀ i j : Fin r, (V i j).natDegree ≤ N + i.1) :
    V.det.natDegree ≤ r * N + r * (r - 1) / 2 := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
  have hsmul : (Equiv.Perm.sign σ • ∏ i : Fin r, V (σ i) i).natDegree ≤
      (∏ i : Fin r, V (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine hsmul.trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i : Fin r, (V (σ i) i).natDegree
      ≤ ∑ i : Fin r, (N + (σ i).1) := Finset.sum_le_sum fun i _ => hdeg (σ i) i
    _ = ∑ i : Fin r, (N + i.1) := Equiv.sum_comp σ (fun i : Fin r => N + i.1)
    _ = r * N + ∑ i : Fin r, i.1 := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin]; simp
    _ = r * N + r * (r - 1) / 2 := by
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id]

/-- Shidlovskii Zero-Order Lemma: if `M > (m - 1) * N + m^2`, then the `m` iterated rows
`vR P0 0, ..., vR P0 (m - 1)` are `ℝ[X]`-linearly independent (so their determinant `Δ ≠ 0`)
and `rootMultiplicity 1 Δ ≤ m * N + m * (m - 1) / 2 - M`. -/
lemma shidlovskii_zero_order {n N M : ℕ} (P0 : Idx n → ℤ[X])
    (hP0_ne : ∃ p, P0 p ≠ 0)
    (hdeg0 : ∀ p, (vR P0 0 p).natDegree ≤ N)
    (hvan : ∀ k < M, PowerSeries.coeff k (Rseq P0 0) = 0)
    (hM_big : (Fintype.card (Idx n) - 1) * N + Fintype.card (Idx n) * Fintype.card (Idx n) < M) :
    let m := Fintype.card (Idx n)
    let e : Fin m ≃ Idx n := (Fintype.equivFin (Idx n)).symm
    let Δ : ℝ[X] := (Matrix.of fun i j : Fin m => vR P0 i.1 (e j)).det
    Δ ≠ 0 ∧ Polynomial.rootMultiplicity 1 Δ ≤ m * N + m * (m - 1) / 2 - M := by
  intro m e Δ
  have hm_pos : 0 < m := by
    dsimp [m]; rw [card_idx]; exact Nat.div_pos (by nlinarith) (by norm_num)
  have hv0_ne : vR P0 0 ≠ 0 := by
    obtain ⟨p, hp⟩ := hP0_ne
    intro h0
    have hp0 : (vR P0 0 p) = 0 := congrArg (fun f => f p) h0
    apply hp
    ext j
    have hj := congrArg (fun q : ℝ[X] => q.coeff j) hp0
    simpa [vR, vZ, Polynomial.coeff_map] using hj
  -- Step 1: Prove by induction that for every `1 ≤ r ≤ m`, `vR P0 0, ..., vR P0 (r - 1)` are `ℝ[X]`-linearly independent
  have hli_all : ∀ r : ℕ, 1 ≤ r → r ≤ m → LinearIndependent ℝ[X] (fun i : Fin r => vR P0 i.1) := by
    intro r hr1 hrm
    induction r with
    | zero => omega
    | succ r ih =>
      cases r with
      | zero =>
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hi0 : i = 0 := Fin.ext (by have := i.2; omega)
        subst hi0
        rw [Fin.sum_univ_one] at hg
        by_contra hg0
        apply hv0_ne
        funext p
        have hp := congrArg (fun f => f p) hg
        exact (mul_eq_zero.mp hp).resolve_left hg0
      | succ r' =>
        let r0 := r' + 1
        have hli_prev : LinearIndependent ℝ[X] (fun i : Fin r0 => vR P0 i.1) :=
          ih (by omega) (by omega)
        by_contra hdep
        -- `v 0, ..., v (r0 - 1)` are linearly independent, while `v 0, ..., v r0` are dependent!
        rw [Fintype.not_linearIndependent_iff] at hdep
        obtain ⟨q, hqsum, i0, hi0⟩ := hdep
        have hq_last_ne : q (Fin.last r0) ≠ 0 := by
          intro hlast
          rw [Fin.sum_univ_castSucc, hlast, zero_smul, add_zero] at hqsum
          have hall0 := Fintype.linearIndependent_iff.mp hli_prev (fun i => q i.castSucc) hqsum
          by_cases hi : i0.1 < r0
          · exact hi0 (hall0 ⟨i0.1, hi⟩)
          · have : i0 = Fin.last r0 := Fin.ext (by dsimp [Fin.last]; have := i0.2; omega)
            exact hi0 (this ▸ hlast)
        -- Saturated submodule `Ssat` of `S = span(v 0, ..., v (r0 - 1))`
        let S : Submodule ℝ[X] (Idx n → ℝ[X]) :=
          Submodule.span ℝ[X] (Set.range fun i : Fin r0 => vR P0 i.1)
        let Ssat : Submodule ℝ[X] (Idx n → ℝ[X]) :=
          { carrier := {w | ∃ g : ℝ[X], g ≠ 0 ∧ g • w ∈ S}
            add_mem' := fun {w1 w2} ⟨g1, hg1, hw1⟩ ⟨g2, hg2, hw2⟩ =>
              ⟨g1 * g2, mul_ne_zero hg1 hg2, by
                rw [smul_add]
                refine S.add_mem ?_ ?_
                · rw [mul_comm, mul_smul]; exact S.smul_mem g2 hw1
                · rw [mul_smul]; exact S.smul_mem g1 hw2⟩
            zero_mem' := ⟨1, one_ne_zero, by simp⟩
            smul_mem' := fun p {w} ⟨g, hg, hw⟩ =>
              ⟨g, hg, by rw [smul_comm]; exact S.smul_mem p hw⟩ }
        have hS_le : S ≤ Ssat := fun w hw => ⟨1, one_ne_zero, by simpa using hw⟩
        have hvr0_mem : vR P0 r0 ∈ Ssat := by
          refine ⟨q (Fin.last r0), hq_last_ne, ?_⟩
          rw [Fin.sum_univ_castSucc] at hqsum
          have heq : q (Fin.last r0) • vR P0 r0 =
              ∑ i : Fin r0, (-q i.castSucc) • vR P0 i.1 := by
            have h1 : q (Fin.last r0) • vR P0 r0 = -(∑ i : Fin r0, q i.castSucc • vR P0 i.1) :=
              eq_neg_of_add_eq_zero_right hqsum
            rw [h1, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => by rw [neg_smul]
          rw [heq]
          exact S.sum_mem fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
        have hL_Ssat : ∀ w ∈ Ssat, Lrow w ∈ Ssat := by
          have hL_S : ∀ w ∈ S, Lrow w ∈ Ssat := by
            intro w hw
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
            · intro w' hw'
              rcases hw' with ⟨i, hi⟩
              rw [← hi, ← vR_succ]
              by_cases hi' : i.1 + 1 < r0
              · exact hS_le (Submodule.subset_span ⟨⟨i.1 + 1, hi'⟩, rfl⟩)
              · have heq : i.1 + 1 = r0 := by omega
                rw [heq]; exact hvr0_mem
            · have : Lrow (0 : Idx n → ℝ[X]) = 0 := by funext p; simp [Lrow]
              rw [this]; exact Ssat.zero_mem
            · intro x y _ _ hx hy; rw [Lrow_add]; exact Ssat.add_mem hx hy
            · intro p x hxS hxL
              rw [Lrow_smul]
              exact Ssat.add_mem (Ssat.smul_mem _ (hS_le hxS)) (Ssat.smul_mem _ hxL)
          intro w hw
          obtain ⟨g, hg, hgw⟩ := hw
          have h1 : Lrow (g • w) ∈ Ssat := hL_S (g • w) hgw
          rw [Lrow_smul] at h1
          have h2 : (Polynomial.X * g.derivative) • w ∈ Ssat :=
            Ssat.smul_mem _ ⟨g, hg, hgw⟩
          have h3 : g • Lrow w ∈ Ssat := by
            have := Ssat.sub_mem h1 h2
            simpa using this
          obtain ⟨h, hh, hhg⟩ := h3
          exact ⟨h * g, mul_ne_zero hh hg, by rwa [mul_smul]⟩
        -- Apply `Submodule.basisOfPid` to `Ssat`
        obtain ⟨s, bS⟩ := Submodule.basisOfPid (Pi.basisFun ℝ[X] (Idx n)) Ssat
        -- Prove `s = r0` using `Module.Basis.card_le_card_of_linearIndependent`
        have hs_eq : s = r0 := by
          have hle1 : r0 ≤ s := by
            let v_in : Fin r0 → Ssat := fun i => ⟨vR P0 i.1, hS_le (Submodule.subset_span ⟨i, rfl⟩)⟩
            have hli_in : LinearIndependent ℝ[X] v_in := by
              rw [Fintype.linearIndependent_iff]
              intro c hc
              exact Fintype.linearIndependent_iff.mp hli_prev c (by
                have h := congrArg (fun x : Ssat => (x : Idx n → ℝ[X])) hc
                simpa [Submodule.coe_sum] using h)
            simpa using bS.card_le_card_of_linearIndependent hli_in
          have hle2 : s ≤ r0 := by
            have hmem_each : ∀ j : Fin s, ∃ g : ℝ[X], g ≠ 0 ∧ g • (bS j : Idx n → ℝ[X]) ∈ S :=
              fun j => (bS j).2
            choose gf hgf_ne hgf_mem using hmem_each
            let G : ℝ[X] := ∏ j : Fin s, gf j
            have hG_ne : G ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hgf_ne j
            have hGu_mem : ∀ j : Fin s, G • (bS j : Idx n → ℝ[X]) ∈ S := by
              intro j
              have hdvd : gf j ∣ G := Finset.dvd_prod_of_mem gf (Finset.mem_univ j)
              obtain ⟨q, hq⟩ := hdvd
              rw [hq, mul_comm, mul_smul]
              exact S.smul_mem q (hgf_mem j)
            let bV : Module.Basis (Fin r0) ℝ[X] S := Module.Basis.span hli_prev
            let u_in : Fin s → S := fun j => ⟨G • (bS j : Idx n → ℝ[X]), hGu_mem j⟩
            have hli_u : LinearIndependent ℝ[X] u_in := by
              rw [Fintype.linearIndependent_iff]
              intro c hc
              have h1 : G • (∑ j : Fin s, c j • bS j) = 0 := by
                apply Subtype.ext
                have hc' := congrArg (fun x : S => (x : Idx n → ℝ[X])) hc
                simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero,
                  u_in] at hc'
                rw [Submodule.coe_smul_of_tower, Submodule.coe_sum, Finset.smul_sum]
                calc ∑ j : Fin s, G • (c j • (bS j : Idx n → ℝ[X]))
                    = ∑ j : Fin s, c j • (G • (bS j : Idx n → ℝ[X])) := by
                      refine Finset.sum_congr rfl fun j _ => by rw [smul_comm]
                  _ = 0 := hc'
              have h2 : ∑ j : Fin s, c j • bS j = 0 := by
                apply Subtype.ext
                funext p
                have hp := congrArg (fun x : Ssat => (x : Idx n → ℝ[X]) p) h1
                exact (mul_eq_zero.mp hp).resolve_left hG_ne
              exact Fintype.linearIndependent_iff.mp bS.linearIndependent c h2
            simpa using bV.card_le_card_of_linearIndependent hli_u
          omega
        let bS' : Module.Basis (Fin r0) ℝ[X] Ssat := bS.reindex (Equiv.cast (congrArg Fin hs_eq))
        let u : Fin r0 → (Idx n → ℝ[X]) := fun j => (bS' j : Idx n → ℝ[X])
        -- Express `Lrow (u i) = ∑ j, B i j • u j`
        let B : Matrix (Fin r0) (Fin r0) ℝ[X] := fun i j => bS'.repr ⟨Lrow (u i), hL_Ssat (u i) (bS' i).2⟩ j
        have hLu : ∀ i : Fin r0, Lrow (u i) = ∑ j : Fin r0, B i j • u j := by
          intro i
          have h := congrArg (fun x : Ssat => (x : Idx n → ℝ[X]))
            (bS'.sum_repr ⟨Lrow (u i), hL_Ssat (u i) (bS' i).2⟩)
          rw [Submodule.coe_sum] at h
          exact h.symm
        -- Evaluate at `z = 0`: `U0 * A0 = B0 * U0` and `U0` has injective row action
        let U0 : Matrix (Fin r0) (Idx n) ℝ := fun i p => (u i p).eval 0
        let B0 : Matrix (Fin r0) (Fin r0) ℝ := B.map (Polynomial.eval 0)
        let A0 : Matrix (Idx n) (Idx n) ℝ := (AmatR n).map (Polynomial.eval 0)
        have hU0_eq : U0 * A0 = B0 * U0 := by
          apply Matrix.ext; intro i p
          have h1 := congrArg (fun f : Idx n → ℝ[X] => (f p).eval 0) (hLu i)
          simp only [Lrow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, zero_mul,
            zero_add, Polynomial.eval_finsetSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
          rw [Matrix.mul_apply, Matrix.mul_apply]
          exact h1
        have hU0_pow : ∀ k : ℕ, U0 * A0 ^ k = B0 ^ k * U0 := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
            rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ihk, Matrix.mul_assoc, hU0_eq,
              ← Matrix.mul_assoc]
        have hU0_inj : ∀ x : Fin r0 → ℝ, (∀ p : Idx n, ∑ i : Fin r0, x i * U0 i p = 0) → x = 0 := by
          intro x hx
          let w : Idx n → ℝ[X] := ∑ i : Fin r0, Polynomial.C (x i) • u i
          have hw_mem : w ∈ Ssat := Ssat.sum_mem fun i _ => Ssat.smul_mem _ (bS' i).2
          have hw0 : ∀ p : Idx n, Polynomial.X ∣ w p := by
            intro p
            rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
            simp only [w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Polynomial.eval_finsetSum,
              Polynomial.eval_mul, Polynomial.eval_C]
            exact hx p
          let wt : Idx n → ℝ[X] := fun p => w p /ₘ Polynomial.X
          have hwt_eq : (Polynomial.X : ℝ[X]) • wt = w := by
            funext p
            have hmon : (Polynomial.X : ℝ[X]).Monic := Polynomial.monic_X
            have hmod : w p %ₘ Polynomial.X = 0 :=
              (Polynomial.modByMonic_eq_zero_iff_dvd hmon).mpr (hw0 p)
            have hdiv := Polynomial.modByMonic_add_div (w p) Polynomial.X
            rw [hmod, zero_add] at hdiv
            exact hdiv
          have hwt_mem : wt ∈ Ssat := by
            obtain ⟨g, hg, hgw⟩ := hw_mem
            refine ⟨g * Polynomial.X, mul_ne_zero hg Polynomial.X_ne_zero, ?_⟩
            rw [mul_smul, hwt_eq]; exact hgw
          let r_wt := bS'.repr ⟨wt, hwt_mem⟩
          have hw_eq2 : ∑ i : Fin r0, Polynomial.C (x i) • bS' i =
              ∑ i : Fin r0, (Polynomial.X * r_wt i) • bS' i := by
            apply Subtype.ext
            have hrepr := congrArg (fun z : Ssat => (z : Idx n → ℝ[X])) (bS'.sum_repr ⟨wt, hwt_mem⟩)
            simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hrepr ⊢
            change w = ∑ i : Fin r0, (Polynomial.X * r_wt i) • u i
            rw [← hwt_eq, ← hrepr, Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ => by rw [mul_smul]
          have hcoeff := Fintype.linearIndependent_iff.mp bS'.linearIndependent
            (fun i => Polynomial.C (x i) - Polynomial.X * r_wt i) (by
              have : (∑ i : Fin r0, (Polynomial.C (x i) - Polynomial.X * r_wt i) • bS' i) =
                  (∑ i : Fin r0, Polynomial.C (x i) • bS' i) -
                  (∑ i : Fin r0, (Polynomial.X * r_wt i) • bS' i) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun i _ =>
                  sub_smul (Polynomial.C (x i)) (Polynomial.X * r_wt i) (bS' i)
              rw [this, hw_eq2, sub_self])
          funext i
          have hi := congrArg (Polynomial.eval 0) (hcoeff i)
          simpa using hi
        have hB0_nilp : B0 ^ (n + 1) = 0 := by
          have h0 : B0 ^ (n + 1) * U0 = 0 := by
            rw [← hU0_pow, AmatR_eval_zero_nilpotent, Matrix.mul_zero]
          ext i j
          have hrow := hU0_inj (fun k => (B0 ^ (n + 1)) i k) (fun p => by
            have := congrArg (fun M : Matrix (Fin r0) (Idx n) ℝ => M i p) h0
            simpa [Matrix.mul_apply] using this)
          exact congrArg (fun f : Fin r0 → ℝ => f j) hrow
        -- Define `g j := ∑ p, u j p * fPS p`; show `g j ≠ 0` and `∃ j0, coeff 0 (g j0) ≠ 0`
        let g : Fin r0 → PowerSeries ℝ := fun j =>
          ∑ p : Idx n, ((u j p : ℝ[X]) : PowerSeries ℝ) * fPS p
        have hg_ne : ∀ j : Fin r0, g j ≠ 0 := by
          intro j hgj
          have hu0 := fPS_linearIndependent (u j) hgj
          have hbj0 : bS' j = 0 := Subtype.ext (funext hu0)
          exact bS'.ne_zero j hbj0
        have hDg : ∀ j : Fin r0, Dps (g j) = ∑ k : Fin r0, ((B j k : ℝ[X]) : PowerSeries ℝ) * g k := by
          intro j
          rw [Dps_poly_comb, hLu j]
          simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, poly_coe_sum,
            Polynomial.coe_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
        have hex_coeff0 : ∃ j0 : Fin r0, PowerSeries.coeff 0 (g j0) ≠ 0 := by
          have hex_nz : ∀ j : Fin r0, ∃ k : ℕ, PowerSeries.coeff k (g j) ≠ 0 := by
            intro j
            by_contra hall
            push Not at hall
            exact hg_ne j (by ext k; rw [map_zero]; exact hall k)
          have hnonempty : (∃ k : ℕ, ∃ j : Fin r0, PowerSeries.coeff k (g j) ≠ 0) := by
            obtain ⟨k, hk⟩ := hex_nz ⟨0, by omega⟩
            exact ⟨k, ⟨0, by omega⟩, hk⟩
          let μ : ℕ := Nat.find hnonempty
          have hμ_spec : ∃ j : Fin r0, PowerSeries.coeff μ (g j) ≠ 0 := Nat.find_spec hnonempty
          have hμ_min : ∀ l < μ, ∀ j : Fin r0, PowerSeries.coeff l (g j) = 0 := by
            intro l hl j
            by_contra hne
            exact Nat.find_min hnonempty hl ⟨j, hne⟩
          let y : Fin r0 → ℝ := fun j => PowerSeries.coeff μ (g j)
          have hBy : B0.mulVec y = (μ : ℝ) • y := by
            funext j
            have h1 := congrArg (PowerSeries.coeff μ) (hDg j)
            rw [coeff_Dps] at h1
            conv_rhs at h1 => rw [map_sum]
            have h2 : ∀ k : Fin r0,
                PowerSeries.coeff μ (((B j k : ℝ[X]) : PowerSeries ℝ) * g k) =
                  (B j k).eval 0 * y k := by
              intro k
              rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_eq_single 0]
              · simp [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, y]
              · intro l hl hl0
                have hlt : μ - l < μ := by
                  have := Finset.mem_range.mp hl; omega
                rw [hμ_min (μ - l) hlt k, mul_zero]
              · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos μ)) h
            rw [Finset.sum_congr rfl fun k _ => h2 k] at h1
            exact h1.symm
          have hBy_pow : ∀ k : ℕ, (B0 ^ k).mulVec y = ((μ : ℝ) ^ k) • y := by
            intro k
            induction k with
            | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
            | succ k ihk =>
              rw [pow_succ', ← Matrix.mulVec_mulVec, ihk, Matrix.mulVec_smul, hBy, smul_smul,
                pow_succ, mul_comm ((μ : ℝ) ^ k) (μ : ℝ)]
          have h0 : ((μ : ℝ) ^ (n + 1)) • y = 0 := by
            rw [← hBy_pow (n + 1), hB0_nilp, Matrix.zero_mulVec]
          have hμ0 : μ = 0 := by
            obtain ⟨j, hj⟩ := hμ_spec
            have h1 := congrArg (fun f : Fin r0 → ℝ => f j) h0
            simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
            have hpow0 : (μ : ℝ) ^ (n + 1) = 0 := (mul_eq_zero.mp h1).resolve_right hj
            by_contra hμne
            exact pow_ne_zero (n + 1) (Nat.cast_ne_zero.mpr hμne) hpow0
          rw [← hμ0]
          exact hμ_spec
        -- Change-of-basis matrix `C : Matrix (Fin r0) (Fin r0) ℝ[X]` with `v i = ∑ j, C i j • u j`
        let C : Matrix (Fin r0) (Fin r0) ℝ[X] :=
          fun i j => bS'.repr ⟨vR P0 i.1, hS_le (Submodule.subset_span ⟨i, rfl⟩)⟩ j
        have hvi_eq : ∀ i : Fin r0, vR P0 i.1 = ∑ j : Fin r0, C i j • u j := by
          intro i
          have h := congrArg (fun x : Ssat => (x : Idx n → ℝ[X]))
            (bS'.sum_repr ⟨vR P0 i.1, hS_le (Submodule.subset_span ⟨i, rfl⟩)⟩)
          rw [Submodule.coe_sum] at h
          exact h.symm
        have hC_det_ne : C.det ≠ 0 := by
          intro hdet0
          let K := FractionRing ℝ[X]
          let emb : ℝ[X] →+* K := algebraMap ℝ[X] K
          have hemb_inj : Function.Injective emb := IsFractionRing.injective ℝ[X] K
          have hdetK : (C.map emb)ᵀ.det = 0 := by
            rw [Matrix.det_transpose]
            exact (RingHom.map_det emb C).symm.trans (by rw [hdet0, map_zero])
          obtain ⟨c, hc_ne, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetK
          obtain ⟨⟨d, hd⟩, hc_int⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℝ[X])
            (Finset.univ : Finset (Fin r0)) c
          have hd_ne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
          choose a ha using fun i : Fin r0 => hc_int i (Finset.mem_univ i)
          have ha' : ∀ i : Fin r0, emb (a i) = emb d * c i := by
            intro i; simpa [emb, Submonoid.smul_def, Algebra.smul_def] using ha i
          have ha_ne : ∃ i : Fin r0, a i ≠ 0 := by
            by_contra hall; push Not at hall
            apply hc_ne; funext i
            have : emb d * c i = 0 := by rw [← ha' i, hall i, map_zero]
            exact (mul_eq_zero.mp this).resolve_left (fun h0 => hd_ne (hemb_inj (by rwa [map_zero])))
          have ha_rel : ∑ i : Fin r0, a i • vR P0 i.1 = 0 := by
            have hCrel : ∀ j : Fin r0, ∑ i : Fin r0, a i * C i j = 0 := by
              intro j
              apply hemb_inj
              rw [map_zero, map_sum]
              have hj := congrArg (fun f : Fin r0 → K => emb d * f j) hc0
              rw [Pi.zero_apply, mul_zero, Matrix.mulVec, dotProduct, Finset.mul_sum] at hj
              rw [← hj]
              refine Finset.sum_congr rfl fun i _ => ?_
              simp only [Matrix.transpose_apply, Matrix.map_apply, map_mul]
              rw [ha' i]
              ring
            simp_rw [hvi_eq, Finset.smul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_eq_zero fun j _ => ?_
            simp_rw [smul_smul, ← Finset.sum_smul, hCrel j, zero_smul]
          obtain ⟨i, hi⟩ := ha_ne
          exact hi (Fintype.linearIndependent_iff.mp hli_prev a ha_rel i)
        -- `C.det * g j0 = ∑ i, C.adjugate j0 i * Rseq P0 i`
        obtain ⟨j0, hj0⟩ := hex_coeff0
        have hR_eq : ∀ i : Fin r0, Rseq P0 i.1 = ∑ j : Fin r0, ((C i j : ℝ[X]) : PowerSeries ℝ) * g j := by
          intro i
          rw [Rseq, hvi_eq i]
          simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, poly_coe_sum,
            Polynomial.coe_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => by ring
        have hdet_g : ((C.det : ℝ[X]) : PowerSeries ℝ) * g j0 =
            ∑ i : Fin r0, ((C.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) * Rseq P0 i.1 := by
          simp_rw [hR_eq, Finset.mul_sum]
          rw [Finset.sum_comm]
          have hterm : ∀ j : Fin r0,
              (∑ i : Fin r0, ((C.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) *
                (((C i j : ℝ[X]) : PowerSeries ℝ) * g j)) =
              (if j0 = j then ((C.det : ℝ[X]) : PowerSeries ℝ) * g j else 0) := by
            intro j
            have hmul : (∑ i : Fin r0, C.adjugate j0 i * C i j) =
                if j0 = j then C.det else 0 := by
              have h := congrArg (fun M : Matrix (Fin r0) (Fin r0) ℝ[X] => M j0 j)
                (Matrix.adjugate_mul C)
              simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using h
            calc (∑ i : Fin r0, ((C.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) *
                    (((C i j : ℝ[X]) : PowerSeries ℝ) * g j))
                = (((∑ i : Fin r0, C.adjugate j0 i * C i j : ℝ[X]) : PowerSeries ℝ)) * g j := by
                  rw [poly_coe_sum, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun i _ => by rw [Polynomial.coe_mul, mul_assoc]
              _ = _ := by rw [hmul]; split_ifs <;> simp
          simp_rw [hterm]
          rw [Finset.sum_eq_single j0]
          · simp
          · intro j _ hj; simp [Ne.symm hj]
          · intro h; exact absurd (Finset.mem_univ _) h
        -- Deduce `(C.det).coeff a = 0` for all `a < M`, hence `M ≤ C.det.natDegree`
        have hC_van : ∀ a < M, C.det.coeff a = 0 := by
          intro a
          induction a using Nat.strong_induction_on with
          | h a iha =>
            intro haM
            have hcoeff_rhs : PowerSeries.coeff a
                (∑ i : Fin r0, ((C.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) * Rseq P0 i.1) = 0 := by
              rw [map_sum]
              refine Finset.sum_eq_zero fun i _ => ?_
              rw [PowerSeries.coeff_mul]
              refine Finset.sum_eq_zero fun x hx => ?_
              have hsum : x.1 + x.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
              rw [coeff_Rseq, hvan x.2 (by omega), mul_zero, mul_zero]
            have hcoeff_lhs : PowerSeries.coeff a (((C.det : ℝ[X]) : PowerSeries ℝ) * g j0) =
                C.det.coeff a * PowerSeries.coeff 0 (g j0) := by
              rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_eq_single a]
              · simp [Polynomial.coeff_coe]
              · intro l hl hla
                have hlt : l < a := by have := Finset.mem_range.mp hl; omega
                rw [Polynomial.coeff_coe, iha l hlt (by omega), zero_mul]
              · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self a)) h
            have heq : C.det.coeff a * PowerSeries.coeff 0 (g j0) = 0 := by
              rw [← hcoeff_lhs, hdet_g, hcoeff_rhs]
            exact (mul_eq_zero.mp heq).resolve_right hj0
        have hM_le_Cdeg : M ≤ C.det.natDegree := by
          by_contra hlt
          push Not at hlt
          exact Polynomial.leadingCoeff_ne_zero.mpr hC_det_ne (hC_van C.det.natDegree hlt)
        -- Extract nonzero `r0 × r0` minor of `U` to bound `C.det.natDegree ≤ r0 * N + r0 * (r0 - 1) / 2`
        have hli_u : LinearIndependent ℝ[X] u := by
          rw [Fintype.linearIndependent_iff]
          intro c hc
          exact Fintype.linearIndependent_iff.mp bS'.linearIndependent c (Subtype.ext (by
            simpa [Submodule.coe_sum, u] using hc))
        obtain ⟨cols, hU_det_ne⟩ := exists_cols_det_ne_zero (Matrix.of u) hli_u
        let Vsub : Matrix (Fin r0) (Fin r0) ℝ[X] := fun i j => vR P0 i.1 (cols j)
        let Usub : Matrix (Fin r0) (Fin r0) ℝ[X] := (Matrix.of u).submatrix id cols
        have hVeq : Vsub = C * Usub := by
          apply Matrix.ext; intro i j
          have h := congrArg (fun f : Idx n → ℝ[X] => f (cols j)) (hvi_eq i)
          rw [Finset.sum_apply] at h
          rw [Matrix.mul_apply]
          exact h
        have hVdet : Vsub.det = C.det * Usub.det := by rw [hVeq, Matrix.det_mul]
        have hCdeg_le : C.det.natDegree ≤ r0 * N + r0 * (r0 - 1) / 2 := by
          have h1 : C.det.natDegree ≤ Vsub.det.natDegree := by
            rw [hVdet, Polynomial.natDegree_mul hC_det_ne hU_det_ne]; omega
          exact h1.trans (natDegree_det_le_of_row_deg Vsub fun i j =>
            natDegree_vR_le P0 hdeg0 i.1 (cols j))
        have hs_lt : r0 ≤ m - 1 := by omega
        have hss : r0 * (r0 - 1) / 2 ≤ m * m :=
          (Nat.div_le_self _ _).trans (Nat.mul_le_mul (by omega) (by omega))
        have hsN : r0 * N ≤ (m - 1) * N := Nat.mul_le_mul_right N hs_lt
        have hM_big' : (m - 1) * N + m * m < M := hM_big
        omega
  -- Step 2: Now `vR P0 0, ..., vR P0 (m - 1)` are `ℝ[X]`-linearly independent, so `Δ ≠ 0`
  have hli_m : LinearIndependent ℝ[X] (fun i : Fin m => vR P0 i.1) := hli_all m hm_pos le_rfl
  let V : Matrix (Fin m) (Fin m) ℝ[X] := Matrix.of fun i j : Fin m => vR P0 i.1 (e j)
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    let K := FractionRing ℝ[X]
    let emb : ℝ[X] →+* K := algebraMap ℝ[X] K
    have hemb_inj : Function.Injective emb := IsFractionRing.injective ℝ[X] K
    have hdetK : (V.map emb)ᵀ.det = 0 := by
      rw [Matrix.det_transpose]
      exact (RingHom.map_det emb V).symm.trans (by rw [show V.det = Δ from rfl, h0, map_zero])
    obtain ⟨c, hc_ne, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetK
    obtain ⟨⟨d, hd⟩, hc_int⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℝ[X])
      (Finset.univ : Finset (Fin m)) c
    have hd_ne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
    choose a ha using fun i : Fin m => hc_int i (Finset.mem_univ i)
    have ha' : ∀ i : Fin m, emb (a i) = emb d * c i := by
      intro i; simpa [emb, Submonoid.smul_def, Algebra.smul_def] using ha i
    have ha_ne : ∃ i : Fin m, a i ≠ 0 := by
      by_contra hall; push Not at hall
      apply hc_ne; funext i
      have : emb d * c i = 0 := by rw [← ha' i, hall i, map_zero]
      exact (mul_eq_zero.mp this).resolve_left (fun h0 => hd_ne (hemb_inj (by rwa [map_zero])))
    have ha_rel : ∑ i : Fin m, a i • vR P0 i.1 = 0 := by
      funext p
      let j := e.symm p
      have hp : e j = p := e.apply_symm_apply p
      rw [← hp, Finset.sum_apply]
      apply hemb_inj
      rw [Pi.zero_apply, map_zero, map_sum]
      have hj := congrArg (fun f : Fin m → K => emb d * f j) hc0
      rw [Pi.zero_apply, mul_zero, Matrix.mulVec, dotProduct, Finset.mul_sum] at hj
      rw [← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.of_apply, V]
      rw [ha' i]
      ring
    obtain ⟨i, hi⟩ := ha_ne
    exact hi (Fintype.linearIndependent_iff.mp hli_m a ha_rel i)
  -- Step 3: Prove `X ^ M ∣ Δ` using `fPS (0, 0) = 1`, hence `rootMultiplicity 1 Δ ≤ deg Δ - M`
  let p0 : Idx n := ⟨(⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_succ n⟩), Nat.zero_le n⟩
  let j0 : Fin m := e.symm p0
  have hf0 : fPS (e j0) = 1 := by rw [e.apply_symm_apply]; exact fPS_zero
  have hΔ_eq : ((Δ : ℝ[X]) : PowerSeries ℝ) =
      ∑ i : Fin m, ((V.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) * Rseq P0 i.1 := by
    have hR_eq : ∀ i : Fin m, Rseq P0 i.1 =
        ∑ j : Fin m, ((V i j : ℝ[X]) : PowerSeries ℝ) * fPS (e j) := by
      intro i
      rw [Rseq]
      exact (Equiv.sum_comp e (fun p => ((vR P0 i.1 p : ℝ[X]) : PowerSeries ℝ) * fPS p)).symm
    simp_rw [hR_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ j : Fin m,
        (∑ i : Fin m, ((V.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) *
          (((V i j : ℝ[X]) : PowerSeries ℝ) * fPS (e j))) =
        (if j0 = j then ((Δ : ℝ[X]) : PowerSeries ℝ) * fPS (e j) else 0) := by
      intro j
      have hmul : (∑ i : Fin m, V.adjugate j0 i * V i j) = if j0 = j then Δ else 0 := by
        have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ[X] => M j0 j) (Matrix.adjugate_mul V)
        simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Δ, V] using h
      calc (∑ i : Fin m, ((V.adjugate j0 i : ℝ[X]) : PowerSeries ℝ) *
              (((V i j : ℝ[X]) : PowerSeries ℝ) * fPS (e j)))
          = (((∑ i : Fin m, V.adjugate j0 i * V i j : ℝ[X]) : PowerSeries ℝ)) * fPS (e j) := by
            rw [poly_coe_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by rw [Polynomial.coe_mul, mul_assoc]
        _ = _ := by rw [hmul]; split_ifs <;> simp
    simp_rw [hterm]
    rw [Finset.sum_eq_single j0]
    · simp [hf0]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hΔ_van : ∀ a < M, Δ.coeff a = 0 := by
    intro a haM
    have h1 := congrArg (PowerSeries.coeff a) hΔ_eq
    rw [Polynomial.coeff_coe, map_sum] at h1
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum : x.1 + x.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [coeff_Rseq, hvan x.2 (by omega), mul_zero, mul_zero]
  have hX_dvd : Polynomial.X ^ M ∣ Δ := by
    rw [Polynomial.X_pow_dvd_iff]
    exact hΔ_van
  obtain ⟨Δt, hΔt⟩ := hX_dvd
  have hΔt_ne : Δt ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hΔt; exact hΔ_ne hΔt
  have hdeg_Δ : Δ.natDegree ≤ m * N + m * (m - 1) / 2 :=
    natDegree_det_le_of_row_deg V fun i j => natDegree_vR_le P0 hdeg0 i.1 (e j)
  have hdeg_Δt : M + Δt.natDegree = Δ.natDegree := by
    rw [hΔt, Polynomial.natDegree_mul (pow_ne_zero M Polynomial.X_ne_zero) hΔt_ne,
      Polynomial.natDegree_X_pow]
  have hrm_eq : Polynomial.rootMultiplicity 1 Δ = Polynomial.rootMultiplicity 1 Δt := by
    rw [hΔt, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero M Polynomial.X_ne_zero) hΔt_ne)]
    have hrmX : Polynomial.rootMultiplicity 1 ((Polynomial.X : ℝ[X]) ^ M) = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff]
      intro hroot
      simp [Polynomial.IsRoot] at hroot
    rw [hrmX, zero_add]
  have hrm_le : Polynomial.rootMultiplicity 1 Δt ≤ Δt.natDegree := by
    obtain ⟨q, hq⟩ := Polynomial.pow_rootMultiplicity_dvd Δt 1
    have hq_ne : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hΔt_ne hq
    have hpow_ne : (Polynomial.X - Polynomial.C (1 : ℝ)) ^ Polynomial.rootMultiplicity 1 Δt ≠ 0 :=
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)
    have hdeg := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hpow_ne hq_ne, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one] at hdeg
    omega
  refine ⟨hΔ_ne, ?_⟩
  omega

/-- Express any vector `y : Fin m → ℝ` as a linear combination of the rows of an invertible
`m × m` real matrix `A`. -/
lemma exists_row_comb_of_det_ne_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hdet : A.det ≠ 0) (y : Fin m → ℝ) :
    ∃ c : Fin m → ℝ, y = ∑ i : Fin m, c i • A i := by
  refine ⟨fun i => A.det⁻¹ * ∑ j : Fin m, y j * A.adjugate j i, ?_⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmul : ∀ j : Fin m,
      (∑ i : Fin m, A.adjugate j i * A i k) = if j = k then A.det else 0 := by
    intro j
    have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M j k) (Matrix.adjugate_mul A)
    simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using h
  calc y k = A.det⁻¹ * (A.det * y k) := (inv_mul_cancel_left₀ hdet (y k)).symm
    _ = A.det⁻¹ * ∑ j : Fin m, y j * (if j = k then A.det else 0) := by
        congr 1; rw [Finset.sum_eq_single k]
        · rw [if_pos rfl, mul_comm]
        · intro j _ hj; rw [if_neg hj, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = A.det⁻¹ * ∑ j : Fin m, y j * ∑ i : Fin m, A.adjugate j i * A i k := by
        congr 1; refine Finset.sum_congr rfl fun j _ => by rw [hmul j]
    _ = ∑ i : Fin m, (A.det⁻¹ * ∑ j : Fin m, y j * A.adjugate j i) * A i k := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Ascending-Chain Row-Shift Lemma: if `Δ = det(v 0, ..., v (m - 1)) ≠ 0` and
`t = rootMultiplicity 1 Δ`, then `span_ℝ { (v k)(1) : k < m + t } = ℝ^m`,
and hence there exist `m` indices `k : Fin m → ℕ` with `k i < m + t` whose evaluation
matrix at `z = 1` has nonzero determinant. -/
lemma exists_full_rank_rows_at_one {n : ℕ} (P0 : Idx n → ℤ[X])
    (hΔ_ne : (Matrix.of fun i j : Fin (Fintype.card (Idx n)) =>
        vR P0 i.1 ((Fintype.equivFin (Idx n)).symm j)).det ≠ 0) :
    let m := Fintype.card (Idx n)
    let e : Fin m ≃ Idx n := (Fintype.equivFin (Idx n)).symm
    let t := Polynomial.rootMultiplicity 1 (Matrix.of fun i j : Fin m => vR P0 i.1 (e j)).det
    ∃ k : Fin m → ℕ, (∀ i, k i < m + t) ∧
      (Matrix.of fun i j : Fin m => (vR P0 (k i) (e j)).eval 1).det ≠ 0 := by
  intro m e t
  let Msub : ℕ → Submodule ℝ[X] (Idx n → ℝ[X]) := fun s =>
    Submodule.span ℝ[X] (Set.range fun i : Fin (m + s) => vR P0 i.1)
  have hM_mono : ∀ s : ℕ, Msub s ≤ Msub (s + 1) := by
    intro s
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, by omega⟩, rfl⟩
  -- Every `Msub s` has rank `m` (contains `Msub 0` which has `det ≠ 0`, and sits in `ℝ[X]^m`)
  have hbasisM_ex : ∀ s : ℕ, Nonempty (Module.Basis (Fin m) ℝ[X] (Msub s)) := by
    intro s
    obtain ⟨k, bk⟩ := Submodule.basisOfPid (Pi.basisFun ℝ[X] (Idx n)) (Msub s)
    have hks : k = m := by
      have hle1 : k ≤ m := by
        have hli : LinearIndependent ℝ[X] (fun i : Fin k => (bk i : Idx n → ℝ[X])) := by
          rw [Fintype.linearIndependent_iff]
          intro c hc
          exact Fintype.linearIndependent_iff.mp bk.linearIndependent c
            (Subtype.ext (by simpa [Submodule.coe_sum] using hc))
        simpa [m] using (Pi.basisFun ℝ[X] (Idx n)).card_le_card_of_linearIndependent hli
      have hle2 : m ≤ k := by
        have hli0 : LinearIndependent ℝ[X] (fun i : Fin m => vR P0 i.1) := by
          rw [Fintype.linearIndependent_iff]
          intro c hc
          let V : Matrix (Fin m) (Fin m) ℝ[X] := Matrix.of fun i j => vR P0 i.1 (e j)
          have h1 : Vᵀ.mulVec c = 0 := by
            funext j
            have hj := congrArg (fun f : Idx n → ℝ[X] => f (e j)) hc
            simpa [Matrix.mulVec, dotProduct, V, mul_comm] using hj
          have h2 : V.det • c = 0 := by
            have := congrArg (Vᵀ.adjugate.mulVec) h1
            rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.det_transpose,
              Matrix.smul_mulVec, Matrix.one_mulVec] at this
            exact this
          intro i
          exact (mul_eq_zero.mp (congrArg (fun f : Fin m → ℝ[X] => f i) h2)).resolve_left hΔ_ne
        let v_in : Fin m → Msub s := fun i =>
          ⟨vR P0 i.1, Submodule.subset_span ⟨⟨i.1, by omega⟩, rfl⟩⟩
        have hli_in : LinearIndependent ℝ[X] v_in := by
          rw [Fintype.linearIndependent_iff]
          intro c hc
          exact Fintype.linearIndependent_iff.mp hli0 c (by
            have h := congrArg (fun x : Msub s => (x : Idx n → ℝ[X])) hc
            simpa [Submodule.coe_sum] using h)
        simpa using bk.card_le_card_of_linearIndependent hli_in
      exact le_antisymm hle1 hle2
    exact ⟨bk.reindex (Equiv.cast (congrArg Fin hks))⟩
  let basisM : ∀ s : ℕ, Module.Basis (Fin m) ℝ[X] (Msub s) := fun s => Classical.choice (hbasisM_ex s)
  let Umat : ℕ → Matrix (Fin m) (Fin m) ℝ[X] := fun s i j => (basisM s i : Idx n → ℝ[X]) (e j)
  let dseq : ℕ → ℕ := fun s => Polynomial.rootMultiplicity 1 (Umat s).det
  -- Step 1: Every `Umat s` has `det ≠ 0`, `dseq 0 ≤ t`, and `dseq (s + 1) ≤ dseq s`
  have hQ_ex : ∀ s : ℕ, ∃ Q : Matrix (Fin m) (Fin m) ℝ[X],
      Umat s = Q * Umat (s + 1) := by
    intro s
    refine ⟨Matrix.of fun i k => (basisM (s + 1)).repr ⟨(basisM s i : Idx n → ℝ[X]), hM_mono s (basisM s i).2⟩ k, ?_⟩
    apply Matrix.ext; intro i j
    have h := congrArg (fun x : Msub (s + 1) => (x : Idx n → ℝ[X]) (e j))
      ((basisM (s + 1)).sum_repr ⟨(basisM s i : Idx n → ℝ[X]), hM_mono s (basisM s i).2⟩)
    rw [Submodule.coe_sum, Finset.sum_apply] at h
    exact h.symm
  have hU_det_ne : ∀ s : ℕ, (Umat s).det ≠ 0 := by
    intro s
    let Q0 : Matrix (Fin m) (Fin m) ℝ[X] := fun i k =>
      (basisM s).repr ⟨vR P0 i.1, Submodule.subset_span ⟨⟨i.1, by omega⟩, rfl⟩⟩ k
    have hV0 : (Matrix.of fun i j : Fin m => vR P0 i.1 (e j)) = Q0 * Umat s := by
      apply Matrix.ext; intro i j
      have h := congrArg (fun x : Msub s => (x : Idx n → ℝ[X]) (e j))
        ((basisM s).sum_repr ⟨vR P0 i.1, Submodule.subset_span ⟨⟨i.1, by omega⟩, rfl⟩⟩)
      rw [Submodule.coe_sum, Finset.sum_apply] at h
      rw [Matrix.mul_apply]
      exact h.symm
    have hdet := congrArg Matrix.det hV0
    rw [Matrix.det_mul] at hdet
    intro h0; rw [h0, mul_zero] at hdet; exact hΔ_ne hdet
  have hd0_le : dseq 0 ≤ t := by
    let Q0 : Matrix (Fin m) (Fin m) ℝ[X] := fun i k =>
      (basisM 0).repr ⟨vR P0 i.1, Submodule.subset_span ⟨⟨i.1, by omega⟩, rfl⟩⟩ k
    have hV0 : (Matrix.of fun i j : Fin m => vR P0 i.1 (e j)) = Q0 * Umat 0 := by
      apply Matrix.ext; intro i j
      have h := congrArg (fun x : Msub 0 => (x : Idx n → ℝ[X]) (e j))
        ((basisM 0).sum_repr ⟨vR P0 i.1, Submodule.subset_span ⟨⟨i.1, by omega⟩, rfl⟩⟩)
      rw [Submodule.coe_sum, Finset.sum_apply] at h
      rw [Matrix.mul_apply]
      exact h.symm
    have hdet := congrArg Matrix.det hV0
    rw [Matrix.det_mul] at hdet
    have hmul : t = Polynomial.rootMultiplicity 1 Q0.det + dseq 0 := by
      dsimp [t, dseq]
      rw [hdet, Polynomial.rootMultiplicity_mul (by rwa [← hdet])]
    omega
  -- Step 2: Strict decrease: if `0 < dseq s`, then `dseq (s + 1) < dseq s`!
  have hstep_dec : ∀ s : ℕ, 0 < dseq s → dseq (s + 1) < dseq s := by
    intro s hds_pos
    obtain ⟨Q, hQ⟩ := hQ_ex s
    have hdet_eq : (Umat s).det = Q.det * (Umat (s + 1)).det := by
      conv_lhs => rw [hQ]
      exact Matrix.det_mul Q (Umat (s + 1))
    have hrm_add : dseq s = Polynomial.rootMultiplicity 1 Q.det + dseq (s + 1) := by
      dsimp only [dseq]
      conv_lhs => rw [hdet_eq]
      exact Polynomial.rootMultiplicity_mul (by rw [← hdet_eq]; exact hU_det_ne s)
    by_contra hnotlt
    have hQrm0 : Polynomial.rootMultiplicity 1 Q.det = 0 := by omega
    have hQ_ne : Q.det ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hdet_eq; exact hU_det_ne s hdet_eq
    have hQev1 : Q.det.eval 1 ≠ 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff] at hQrm0
      intro hroot
      exact hQ_ne (hQrm0 hroot)
    -- Define the localization `Mtilde := {w | ∃ p, p.eval 1 ≠ 0 ∧ p • w ∈ Msub s}`
    let Mtilde : Submodule ℝ[X] (Idx n → ℝ[X]) :=
      { carrier := {w | ∃ p : ℝ[X], p.eval 1 ≠ 0 ∧ p • w ∈ Msub s}
        add_mem' := fun {w1 w2} ⟨p1, hp1, hw1⟩ ⟨p2, hp2, hw2⟩ =>
          ⟨p1 * p2, by rw [Polynomial.eval_mul]; exact mul_ne_zero hp1 hp2, by
            rw [smul_add]
            refine (Msub s).add_mem ?_ ?_
            · rw [mul_comm, mul_smul]; exact (Msub s).smul_mem p2 hw1
            · rw [mul_smul]; exact (Msub s).smul_mem p1 hw2⟩
        zero_mem' := ⟨1, by simp, by simp⟩
        smul_mem' := fun q {w} ⟨p, hp, hw⟩ =>
          ⟨p, hp, by rw [smul_comm]; exact (Msub s).smul_mem q hw⟩ }
    -- Show `Msub (s + 1) ≤ Mtilde` using `Q.adjugate * Umat s = Q.det • Umat (s + 1)`
    have hMs1_le : Msub (s + 1) ≤ Mtilde := by
      have hQadj : Q.adjugate * Umat s = Q.det • Umat (s + 1) := by
        conv_lhs => rw [hQ]
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      have hbasis_in : ∀ k : Fin m, Q.det • (basisM (s + 1) k : Idx n → ℝ[X]) ∈ Msub s := by
        intro k
        have heq : Q.det • (basisM (s + 1) k : Idx n → ℝ[X]) =
            ∑ i : Fin m, Q.adjugate k i • (basisM s i : Idx n → ℝ[X]) := by
          funext p
          let j := e.symm p
          have hp : e j = p := e.apply_symm_apply p
          rw [← hp]
          have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ[X] => M k j) hQadj
          rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
        rw [heq]
        exact (Msub s).sum_mem fun i _ => (Msub s).smul_mem _ (basisM s i).2
      intro w hw
      refine ⟨Q.det, hQev1, ?_⟩
      have hrepr := congrArg (fun x : Msub (s + 1) => (x : Idx n → ℝ[X]))
        ((basisM (s + 1)).sum_repr ⟨w, hw⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hrepr
      rw [← hrepr, Finset.smul_sum]
      refine (Msub s).sum_mem fun k _ => ?_
      rw [smul_comm]
      exact (Msub s).smul_mem _ (hbasis_in k)
    -- Therefore `Mtilde` is `Lrow`-invariant!
    have hL_Mtilde : ∀ w ∈ Mtilde, Lrow w ∈ Mtilde := by
      have hL_Ms : ∀ w ∈ Msub s, Lrow w ∈ Mtilde := by
        intro w hw
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · intro w' hw'
          rcases hw' with ⟨i, hi⟩
          rw [← hi, ← vR_succ]
          exact hMs1_le (Submodule.subset_span ⟨⟨i.1 + 1, by omega⟩, rfl⟩)
        · have : Lrow (0 : Idx n → ℝ[X]) = 0 := by funext p; simp [Lrow]
          rw [this]; exact Mtilde.zero_mem
        · intro x y _ _ hx hy; rw [Lrow_add]; exact Mtilde.add_mem hx hy
        · intro p x hxS hxL
          rw [Lrow_smul]
          exact Mtilde.add_mem (Mtilde.smul_mem _ ⟨1, by simp, by simpa using hxS⟩)
            (Mtilde.smul_mem _ hxL)
      intro w hw
      obtain ⟨p, hp, hpw⟩ := hw
      have h1 : Lrow (p • w) ∈ Mtilde := hL_Ms (p • w) hpw
      rw [Lrow_smul] at h1
      have h2 : (Polynomial.X * p.derivative) • w ∈ Mtilde :=
        Mtilde.smul_mem _ ⟨p, hp, hpw⟩
      have h3 : p • Lrow w ∈ Mtilde := by simpa using Mtilde.sub_mem h1 h2
      obtain ⟨r, hr, hrp⟩ := h3
      exact ⟨r * p, by rw [Polynomial.eval_mul]; exact mul_ne_zero hr hp, by rwa [mul_smul]⟩
    -- Every `z ∈ ℝ[X]^m` satisfies `(Umat s).det • z ∈ Msub s`, hence `(X - 1)^(dseq s) • z ∈ Mtilde`!
    have hpow_in : ∀ z : Idx n → ℝ[X],
        ((Polynomial.X - (1 : ℝ[X])) ^ (dseq s)) • z ∈ Mtilde := by
      have hdvd : (Polynomial.X - (1 : ℝ[X])) ^ (dseq s) ∣ (Umat s).det := by
        simpa [dseq] using Polynomial.pow_rootMultiplicity_dvd (Umat s).det 1
      obtain ⟨q, hq⟩ := hdvd
      have hqev1 : q.eval 1 ≠ 0 := by
        intro hq0
        have h1 : (Polynomial.X - (1 : ℝ[X])) ∣ q := by
          rw [show (1 : ℝ[X]) = Polynomial.C (1 : ℝ) from Polynomial.C_1.symm,
            Polynomial.dvd_iff_isRoot]
          exact hq0
        obtain ⟨q', hq'⟩ := h1
        have hdvd1 : (Polynomial.X - Polynomial.C (1 : ℝ)) ^ (dseq s + 1) ∣ (Umat s).det :=
          ⟨q', by rw [Polynomial.C_1, hq, hq', pow_succ]; ring⟩
        have hle := (Polynomial.le_rootMultiplicity_iff (hU_det_ne s)).mpr hdvd1
        change dseq s + 1 ≤ dseq s at hle
        omega
      intro z
      refine ⟨q, hqev1, ?_⟩
      rw [← mul_smul, mul_comm, ← hq]
      -- `(Umat s).det • z = ∑ i, ((Umat s).adjugate *ᵥ (z ∘ e)) i • basisM s i`
      have heq : (Umat s).det • z =
          ∑ i : Fin m, (∑ k : Fin m, z (e k) * (Umat s).adjugate k i) • (basisM s i : Idx n → ℝ[X]) := by
        funext p
        let j := e.symm p
        have hp : e j = p := e.apply_symm_apply p
        rw [← hp]
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        have hmul : ∀ k : Fin m,
            (∑ i : Fin m, (Umat s).adjugate k i * Umat s i j) =
              if k = j then (Umat s).det else 0 := by
          intro k
          have h := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ[X] => M k j)
            (Matrix.adjugate_mul (Umat s))
          simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using h
        calc (Umat s).det * z (e j)
            = ∑ k : Fin m, z (e k) * (if k = j then (Umat s).det else 0) := by
              rw [Finset.sum_eq_single j]
              · simp [mul_comm]
              · intro k _ hk; simp [hk]
              · intro h; exact absurd (Finset.mem_univ _) h
          _ = ∑ k : Fin m, z (e k) * (∑ i : Fin m, (Umat s).adjugate k i * Umat s i j) := by
              refine Finset.sum_congr rfl fun k _ => by rw [hmul k]
          _ = ∑ i : Fin m, (∑ k : Fin m, z (e k) * (Umat s).adjugate k i) * Umat s i j := by
              simp_rw [Finset.mul_sum, Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [heq]
      exact (Msub s).sum_mem fun i _ => (Msub s).smul_mem _ (basisM s i).2
    -- Prove by induction on `k` that `(X - 1)^k • z ∈ Mtilde` for ALL `z` implies `k = 0` works too!
    have hall_in : ∀ k : ℕ, (∀ z : Idx n → ℝ[X], ((Polynomial.X - (1 : ℝ[X])) ^ k) • z ∈ Mtilde) →
        ∀ z : Idx n → ℝ[X], z ∈ Mtilde := by
      intro k
      induction k with
      | zero => intro hk z; simpa using hk z
      | succ k ihk =>
        intro hk1
        refine ihk fun z => ?_
        have hw : ((Polynomial.X - (1 : ℝ[X])) ^ (k + 1)) • z ∈ Mtilde := hk1 z
        have hLw : Lrow (((Polynomial.X - (1 : ℝ[X])) ^ (k + 1)) • z) ∈ Mtilde := hL_Mtilde _ hw
        rw [Lrow_smul] at hLw
        have hterm2 : ((Polynomial.X - (1 : ℝ[X])) ^ (k + 1)) • Lrow z ∈ Mtilde := hk1 (Lrow z)
        have hterm1 : (Polynomial.X * ((Polynomial.X - (1 : ℝ[X])) ^ (k + 1)).derivative) • z ∈ Mtilde := by
          simpa using Mtilde.sub_mem hLw hterm2
        have hderiv : Polynomial.X * ((Polynomial.X - (1 : ℝ[X])) ^ (k + 1)).derivative =
            (((k + 1 : ℕ) : ℝ[X]) * Polynomial.X) * (Polynomial.X - (1 : ℝ[X])) ^ k := by
          rw [Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_X,
            Polynomial.derivative_one, sub_zero, mul_one, Nat.add_sub_cancel,
            Polynomial.C_eq_natCast]
          ring
        rw [hderiv, mul_smul] at hterm1
        obtain ⟨p, hp, hpmem⟩ := hterm1
        refine ⟨p * (((k + 1 : ℕ) : ℝ[X]) * Polynomial.X), ?_, ?_⟩
        · rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X,
            mul_one]
          exact mul_ne_zero hp (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
        · rwa [mul_smul]
    -- So EVERY `z ∈ ℝ[X]^m` lies in `Mtilde`, contradicting `dseq s > 0` (`(Umat s).det.eval 1 = 0`)!
    have hMtilde_top : ∀ z : Idx n → ℝ[X], z ∈ Mtilde := hall_in (dseq s) hpow_in
    have hunit : ∀ j : Fin m, ∃ p : ℝ[X], p.eval 1 ≠ 0 ∧
        p • (Pi.single (e j) 1 : Idx n → ℝ[X]) ∈ Msub s :=
      fun j => hMtilde_top (Pi.single (e j) 1)
    choose pj hpj_ev hpj_mem using hunit
    let Pmat : Matrix (Fin m) (Fin m) ℝ[X] := Matrix.diagonal pj
    let Rmat : Matrix (Fin m) (Fin m) ℝ[X] := fun j i =>
      (basisM s).repr ⟨pj j • Pi.single (e j) 1, hpj_mem j⟩ i
    have hRU : Rmat * Umat s = Pmat := by
      apply Matrix.ext; intro j k
      have h := congrArg (fun x : Msub s => (x : Idx n → ℝ[X]) (e k))
        ((basisM s).sum_repr ⟨pj j • Pi.single (e j) 1, hpj_mem j⟩)
      rw [Submodule.coe_sum, Finset.sum_apply] at h
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
      dsimp only [Pmat]
      rw [Matrix.mul_apply, Matrix.diagonal_apply]
      by_cases hjk : j = k
      · subst hjk
        simpa only [Rmat, Umat, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
          ↓reduceIte, mul_one] using h
      · have hene : e k ≠ e j := fun heq => hjk (e.injective heq).symm
        simpa only [Rmat, Umat, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
          hjk, hene, ↓reduceIte, mul_zero] using h
    have hdet_ev := congrArg (fun M => (Matrix.det M).eval 1) hRU
    rw [Matrix.det_mul, Matrix.det_diagonal, Polynomial.eval_mul, Polynomial.eval_prod] at hdet_ev
    have hUev0 : (Umat s).det.eval 1 = 0 := by
      have h1 : Polynomial.IsRoot (Umat s).det 1 :=
        (Polynomial.rootMultiplicity_pos (hU_det_ne s)).mp hds_pos
      exact h1
    rw [hUev0, mul_zero] at hdet_ev
    have hprod_ne : (∏ j : Fin m, (pj j).eval 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hpj_ev j
    exact hprod_ne hdet_ev.symm
  -- Step 3: By induction, `dseq s ≤ t - s`, hence `dseq t = 0`, so `(Umat t).det.eval 1 ≠ 0`!
  have hd_le : ∀ s : ℕ, dseq s ≤ t - s := by
    intro s
    induction s with
    | zero => simpa using hd0_le
    | succ s ihs =>
      by_cases h0 : dseq s = 0
      · obtain ⟨Q, hQ⟩ := hQ_ex s
        have hdet_eq : (Umat s).det = Q.det * (Umat (s + 1)).det := by
          conv_lhs => rw [hQ]; exact Matrix.det_mul Q (Umat (s + 1))
        have hrm_add : dseq s = Polynomial.rootMultiplicity 1 Q.det + dseq (s + 1) := by
          dsimp only [dseq]
          conv_lhs => rw [hdet_eq]
          exact Polynomial.rootMultiplicity_mul (by rw [← hdet_eq]; exact hU_det_ne s)
        omega
      · have hlt := hstep_dec s (Nat.pos_of_ne_zero h0)
        omega
  have hdt0 : dseq t = 0 := by have := hd_le t; omega
  have hUt_ev1 : (Umat t).det.eval 1 ≠ 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero_iff] at hdt0
    intro hroot
    exact hU_det_ne t (hdt0 hroot)
  -- Step 4: Therefore `{ (vR P0 k)(1) : k < m + t }` spans `Fin m → ℝ`!
  let M1 : Matrix (Fin (m + t)) (Fin m) ℝ := fun i j => (vR P0 i.1 (e j)).eval 1
  have hspan_top : Submodule.span ℝ (Set.range M1) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    let U1 : Matrix (Fin m) (Fin m) ℝ := (Umat t).map (Polynomial.eval 1)
    have hU1_det : U1.det ≠ 0 := by
      have hmap : U1.det = (Umat t).det.eval 1 :=
        (RingHom.map_det (Polynomial.evalRingHom (1 : ℝ)) (Umat t)).symm
      rw [hmap]
      exact hUt_ev1
    obtain ⟨c, hy_eq⟩ := exists_row_comb_of_det_ne_zero U1 hU1_det y
    rw [hy_eq]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    -- Each row `U1 i = ((basisM t i) ∘ e)(1)` lies in `span_ℝ (range M1)` because `basisM t i ∈ Msub t`!
    have hmem : ∀ w ∈ Msub t, (fun j : Fin m => (w (e j)).eval 1) ∈ Submodule.span ℝ (Set.range M1) := by
      intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · intro w' hw'
        rcases hw' with ⟨i, hi⟩
        rw [← hi]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have : (fun j : Fin m => ((0 : Idx n → ℝ[X]) (e j)).eval 1) = 0 := by funext j; simp
        rw [this]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        have : (fun j : Fin m => ((x + y) (e j)).eval 1) =
            (fun j => (x (e j)).eval 1) + (fun j => (y (e j)).eval 1) := by funext j; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      · intro p x _ hx
        have : (fun j : Fin m => ((p • x) (e j)).eval 1) =
            (p.eval 1) • (fun j => (x (e j)).eval 1) := by funext j; simp
        rw [this]; exact Submodule.smul_mem _ _ hx
    exact hmem (basisM t i : Idx n → ℝ[X]) (basisM t i).2
  obtain ⟨f, hf_det⟩ := exists_submatrix_det_ne_zero_of_span_top M1 hspan_top
  exact ⟨fun i => (f i).1, fun i => (f i).2, hf_det⟩

/- ### Section 6: Determinant bounds and final contradiction -/

lemma ein_one_pos : 0 < Ein 1 := by
  have hs := summable_einTerm 1
  have ht := hs.hasSum.tendsto_sum_nat
  have hsub : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range (2 * (K + 1)), einTerm 1 k) atTop (nhds (Ein 1)) :=
    ht.comp (Filter.tendsto_atTop_mono (fun K => by dsimp; omega) tendsto_id)
  have hge : ∀ K : ℕ, (3 : ℝ) / 4 ≤ ∑ k ∈ Finset.range (2 * (K + 1)), einTerm 1 k := by
    intro K
    induction K with
    | zero =>
      simp only [mul_one, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
        zero_add, einTerm]
      norm_num
    | succ K ih =>
      have hsplit : 2 * (K + 1 + 1) = 2 * (K + 1) + 1 + 1 := by omega
      rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
      have hpair : 0 ≤ einTerm 1 (2 * (K + 1)) + einTerm 1 (2 * (K + 1) + 1) := by
        unfold einTerm
        have heven : (-1 : ℝ) ^ (2 * (K + 1)) = 1 := by rw [pow_mul]; norm_num
        have hodd : (-1 : ℝ) ^ (2 * (K + 1) + 1) = -1 := by rw [pow_succ, heven]; norm_num
        rw [heven, hodd, one_pow, one_pow, mul_one, mul_one]
        have h1 : (0 : ℝ) < ((2 * (K + 1) + 1 : ℕ) : ℝ) * ((2 * (K + 1) + 1).factorial : ℝ) := by positivity
        have h2 : ((2 * (K + 1) + 1 : ℕ) : ℝ) * ((2 * (K + 1) + 1).factorial : ℝ) ≤
            ((2 * (K + 1) + 1 + 1 : ℕ) : ℝ) * ((2 * (K + 1) + 1 + 1).factorial : ℝ) := by
          have ha : ((2 * (K + 1) + 1 : ℕ) : ℝ) ≤ ((2 * (K + 1) + 1 + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ _
          have hb : ((2 * (K + 1) + 1).factorial : ℝ) ≤ ((2 * (K + 1) + 1 + 1).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (Nat.le_succ _)
          exact mul_le_mul ha hb (by positivity) (by positivity)
        have hdiv := div_le_div_of_nonneg_left zero_le_one h1 h2
        linarith [show (-1 : ℝ) / (((2 * (K + 1) + 1 + 1 : ℕ) : ℝ) *
            ((2 * (K + 1) + 1 + 1).factorial : ℝ)) =
          -(1 / (((2 * (K + 1) + 1 + 1 : ℕ) : ℝ) *
            ((2 * (K + 1) + 1 + 1).factorial : ℝ))) by ring]
      linarith
  have hlim : (3 : ℝ) / 4 ≤ Ein 1 :=
    ge_of_tendsto hsub (Filter.Eventually.of_forall hge)
  linarith

lemma fVal_pos {n : ℕ} (p : Idx n) : 0 < fVal p :=
  mul_pos (Real.exp_pos _) (pow_pos ein_one_pos _)

noncomputable def polyNorm (Q : ℝ[X]) : ℝ :=
  ∑ j ∈ Finset.range (Q.natDegree + 1), |Q.coeff j|

lemma polyNorm_nonneg (Q : ℝ[X]) : 0 ≤ polyNorm Q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma polyNorm_eq_sum_of_le (Q : ℝ[X]) {D : ℕ} (hD : Q.natDegree ≤ D) :
    polyNorm Q = ∑ j ∈ Finset.range (D + 1), |Q.coeff j| := by
  unfold polyNorm
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
  simp only [Finset.mem_range, not_lt] at hj
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]

lemma abs_eval_one_le_polyNorm (Q : ℝ[X]) : |Q.eval 1| ≤ polyNorm Q := by
  rw [Polynomial.eval_eq_sum_range, polyNorm]
  calc |∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * (1 : ℝ) ^ i|
      ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i * (1 : ℝ) ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| := by
        refine Finset.sum_congr rfl fun i _ => by simp

lemma polyNorm_add_le (P Q : ℝ[X]) : polyNorm (P + Q) ≤ polyNorm P + polyNorm Q := by
  let D := max P.natDegree Q.natDegree
  rw [polyNorm_eq_sum_of_le (P + Q) ((Polynomial.natDegree_add_le P Q).trans le_rfl),
    polyNorm_eq_sum_of_le P (le_max_left _ _), polyNorm_eq_sum_of_le Q (le_max_right _ _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Polynomial.coeff_add]
  exact abs_add_le _ _

lemma polyNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    polyNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyNorm (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [polyNorm]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (polyNorm_add_le _ _).trans (add_le_add le_rfl ih)

lemma polyNorm_mul_le (P Q : ℝ[X]) : polyNorm (P * Q) ≤ polyNorm P * polyNorm Q := by
  let D := P.natDegree + Q.natDegree
  rw [polyNorm_eq_sum_of_le (P * Q) Polynomial.natDegree_mul_le]
  calc ∑ k ∈ Finset.range (D + 1), |(P * Q).coeff k|
      ≤ ∑ k ∈ Finset.range (D + 1), ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k,
          |P.coeff x.1| * |Q.coeff x.2| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Polynomial.coeff_mul]
        calc |∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2|
            ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, |P.coeff x.1 * Q.coeff x.2| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := Finset.sum_congr rfl fun x _ => abs_mul _ _
    _ ≤ (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|) *
        (∑ j ∈ Finset.range (Q.natDegree + 1), |Q.coeff j|) := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        have hsub : ∀ k ∈ Finset.range (D + 1),
            ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, |P.coeff x.1| * |Q.coeff x.2| =
            ∑ x ∈ (Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1)).filter
                (fun x => x.1 + x.2 = k), |P.coeff x.1| * |Q.coeff x.2| := by
          intro k _
          symm
          refine Finset.sum_subset ?_ ?_
          · intro x hx
            rw [Finset.HasAntidiagonal.mem_antidiagonal]
            exact (Finset.mem_filter.mp hx).2
          · intro x hx hnot
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hnot
            by_cases h1 : x.1 < P.natDegree + 1
            · have h2 : ¬ (x.2 < Q.natDegree + 1) := fun h2 => hnot ⟨h1, h2⟩ hx
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), abs_zero, mul_zero]
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by omega), abs_zero, zero_mul]
        rw [Finset.sum_congr rfl hsub]
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 + x.2)
          (t := Finset.range (D + 1)) (fun x hx => by
            simp only [Finset.mem_product, Finset.mem_range] at hx
            exact Finset.mem_range.mpr (by dsimp [D]; omega))]

lemma polyNorm_X_mul_derivative_le (Q : ℝ[X]) :
    polyNorm (Polynomial.X * Q.derivative) ≤ (Q.natDegree : ℝ) * polyNorm Q := by
  have hdeg : (Polynomial.X * Q.derivative).natDegree ≤ Q.natDegree := by
    by_cases h0 : Q.derivative = 0
    · simp [h0]
    · have h1 := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Q.derivative)
      have h2 := Polynomial.natDegree_derivative_le Q
      simp only [Polynomial.natDegree_X] at h1
      have hQpos : 1 ≤ Q.natDegree := by
        by_contra hlt; push Not at hlt
        have hQ0 : Q.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero hQ0, Polynomial.derivative_C] at h0
        exact h0 rfl
      omega
  rw [polyNorm_eq_sum_of_le _ hdeg, polyNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjle : j ≤ Q.natDegree := by have := Finset.mem_range.mp hj; omega
  cases j with
  | zero => simp; positivity
  | succ j =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)]
    have hle : (j : ℝ) + 1 ≤ (Q.natDegree : ℝ) := by exact_mod_cast hjle
    calc |Q.coeff (j + 1)| * ((j : ℝ) + 1)
        = ((j : ℝ) + 1) * |Q.coeff (j + 1)| := mul_comm _ _
      _ ≤ (Q.natDegree : ℝ) * |Q.coeff (j + 1)| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)

lemma polyNorm_AmatR_le (n : ℕ) (q p : Idx n) :
    polyNorm (AmatR n q p) ≤ 3 * (n : ℝ) + 1 := by
  have h1 : ∀ a : ℕ, polyNorm ((a : ℝ[X])) ≤ (a : ℝ) := by
    intro a
    rw [polyNorm_eq_sum_of_le _ (D := 0) (by simp [Polynomial.natDegree_natCast])]
    simp [Polynomial.coeff_natCast_ite]
  have h2 : ∀ a : ℕ, polyNorm (-(a : ℝ[X])) ≤ (a : ℝ) := by
    intro a
    have : polyNorm (-(a : ℝ[X])) = polyNorm ((a : ℝ[X])) := by
      rw [polyNorm_eq_sum_of_le (-(a : ℝ[X])) (D := 0) (by simp [Polynomial.natDegree_natCast]),
        polyNorm_eq_sum_of_le (a : ℝ[X]) (D := 0) (by simp [Polynomial.natDegree_natCast])]
      simp
    rw [this]; exact h1 a
  have h3 : ∀ a : ℕ, polyNorm (-(a : ℝ[X]) * Polynomial.X) ≤ (a : ℝ) := by
    intro a
    refine (polyNorm_mul_le _ _).trans ?_
    have hX : polyNorm (Polynomial.X : ℝ[X]) = 1 := by
      rw [polyNorm_eq_sum_of_le _ (D := 1) Polynomial.natDegree_X.le]
      simp [Finset.sum_range_succ]
    rw [hX, mul_one]; exact h2 a
  have hA : AmatR n q p =
      (if q = p then -(q.1.1.1 : ℝ[X]) * Polynomial.X else 0) +
      (if p.1.1.1 = q.1.1.1 ∧ p.1.2.1 + 1 = q.1.2.1 then (q.1.2.1 : ℝ[X]) else 0) +
      (if p.1.1.1 = q.1.1.1 + 1 ∧ p.1.2.1 + 1 = q.1.2.1 then -(q.1.2.1 : ℝ[X]) else 0) := by
    simp only [AmatR, Matrix.map_apply, AmatZ, Polynomial.map_add]
    congr 1
    · congr 1 <;> (split_ifs <;> simp)
    · split_ifs <;> simp
  rw [hA]
  have hq1 : (q.1.1.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show q.1.1.1 ≤ n by have := q.2; omega)
  have hq2 : (q.1.2.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show q.1.2.1 ≤ n by have := q.2; omega)
  have ht1 : polyNorm (if q = p then -(q.1.1.1 : ℝ[X]) * Polynomial.X else 0) ≤ (n : ℝ) := by
    split_ifs
    · exact (h3 _).trans hq1
    · simp [polyNorm]
  have ht2 : polyNorm (if p.1.1.1 = q.1.1.1 ∧ p.1.2.1 + 1 = q.1.2.1 then (q.1.2.1 : ℝ[X]) else 0) ≤ (n : ℝ) := by
    split_ifs
    · exact (h1 _).trans hq2
    · simp [polyNorm]
  have ht3 : polyNorm (if p.1.1.1 = q.1.1.1 + 1 ∧ p.1.2.1 + 1 = q.1.2.1 then -(q.1.2.1 : ℝ[X]) else 0) ≤ (n : ℝ) := by
    split_ifs
    · exact (h2 _).trans hq2
    · simp [polyNorm]
  have := (polyNorm_add_le _ _).trans (add_le_add ((polyNorm_add_le _ _).trans (add_le_add ht1 ht2)) ht3)
  linarith

lemma polyNorm_vR_le {n N : ℕ} (P0 : Idx n → ℤ[X]) {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hdeg0 : ∀ p, (vR P0 0 p).natDegree ≤ N)
    (hnorm0 : ∀ p, polyNorm (vR P0 0 p) ≤ B0) :
    ∀ k p, polyNorm (vR P0 k p) ≤
      (((N + k + Fintype.card (Idx n) * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0 := by
  intro k
  induction k with
  | zero => intro p; simpa using hnorm0 p
  | succ k ih =>
    intro p
    rw [vR_succ]
    unfold Lrow
    let m := Fintype.card (Idx n)
    have hstep1 : polyNorm (Polynomial.X * (vR P0 k p).derivative) ≤
        ((N + k : ℕ) : ℝ) * (((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0 := by
      refine (polyNorm_X_mul_derivative_le _).trans ?_
      have hd : ((vR P0 k p).natDegree : ℝ) ≤ ((N + k : ℕ) : ℝ) := by
        exact_mod_cast natDegree_vR_le P0 hdeg0 k p
      calc ((vR P0 k p).natDegree : ℝ) * polyNorm (vR P0 k p)
          ≤ ((N + k : ℕ) : ℝ) * ((((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0) :=
            mul_le_mul hd (ih p) (polyNorm_nonneg _) (by positivity)
        _ = _ := by ring
    have hstep2 : polyNorm (∑ q : Idx n, vR P0 k q * AmatR n q p) ≤
        ((m * (3 * n + 1) : ℕ) : ℝ) * (((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0 := by
      refine (polyNorm_sum_le _ _).trans ?_
      calc ∑ q : Idx n, polyNorm (vR P0 k q * AmatR n q p)
          ≤ ∑ _q : Idx n, ((((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0) * (3 * (n : ℝ) + 1) := by
            refine Finset.sum_le_sum fun q _ => (polyNorm_mul_le _ _).trans ?_
            exact mul_le_mul (ih q) (polyNorm_AmatR_le n q p) (polyNorm_nonneg _) (by positivity)
        _ = ((m * (3 * n + 1) : ℕ) : ℝ) * (((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
            push_cast; ring
    have hbase : ((N + k + m * (3 * n + 1) : ℕ) : ℝ) ≤
        ((N + (k + 1) + m * (3 * n + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : N + k + m * (3 * n + 1) ≤ N + (k + 1) + m * (3 * n + 1))
    calc polyNorm (Polynomial.X * (vR P0 k p).derivative + ∑ q : Idx n, vR P0 k q * AmatR n q p)
        ≤ polyNorm (Polynomial.X * (vR P0 k p).derivative) +
          polyNorm (∑ q : Idx n, vR P0 k q * AmatR n q p) := polyNorm_add_le _ _
      _ ≤ ((N + k : ℕ) : ℝ) * (((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0 +
          ((m * (3 * n + 1) : ℕ) : ℝ) * (((N + k + m * (3 * n + 1) : ℕ) : ℝ)) ^ k * B0 :=
            add_le_add hstep1 hstep2
      _ = ((N + k + m * (3 * n + 1) : ℕ) : ℝ) ^ (k + 1) * B0 := by
            rw [pow_succ']; push_cast; ring
      _ ≤ ((N + (k + 1) + m * (3 * n + 1) : ℕ) : ℝ) ^ (k + 1) * B0 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase (k + 1)) hB0

lemma hasSum_coeff_Rseq {n : ℕ} (P0 : Idx n → ℤ[X]) (k : ℕ) :
    HasSum (fun j : ℕ => PowerSeries.coeff j (Rseq P0 k))
      (∑ p : Idx n, (vR P0 k p).eval 1 * fVal p) := by
  have hterm : ∀ p : Idx n,
      HasSum (fun j : ℕ => PowerSeries.coeff j (((vR P0 k p : ℝ[X]) : PowerSeries ℝ) * fPS p))
        ((vR P0 k p).eval 1 * fVal p) := by
    intro p
    have hf := hasSum_and_summable_norm_coeff_fPS p
    exact hasSum_coeff_mul (hasSum_coeff_poly (vR P0 k p)) hf.1
      (summable_norm_coeff_poly (vR P0 k p)) hf.2
  have hsum := hasSum_sum (s := Finset.univ) fun p _ => hterm p
  refine hsum.congr_fun fun j => ?_
  rw [Rseq, map_sum]

lemma pow_div_factorial_le_two_pow_div (j k : ℕ) (hjk : 2 * k ≤ j) :
    (j : ℝ) ^ k / (j.factorial : ℝ) ≤ (2 : ℝ) ^ k / ((j - k).factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hjk' : 2 * k ≤ j := by omega
    have h1 := ih hjk'
    have hfac : ((j - k).factorial : ℝ) = ((j - k : ℕ) : ℝ) * ((j - (k + 1)).factorial : ℝ) := by
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this, Nat.factorial_succ, Nat.cast_mul]
    have h2 : (j : ℝ) ≤ 2 * ((j - k : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ 2 * (j - k))
    have hj_pos : (0 : ℝ) < ((j - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j - k)
    have hfk1_pos : (0 : ℝ) < ((j - (k + 1)).factorial : ℝ) := by positivity
    calc (j : ℝ) ^ (k + 1) / (j.factorial : ℝ)
        = (j : ℝ) * ((j : ℝ) ^ k / (j.factorial : ℝ)) := by rw [pow_succ']; ring
      _ ≤ (j : ℝ) * ((2 : ℝ) ^ k / ((j - k).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg j)
      _ ≤ (2 * ((j - k : ℕ) : ℝ)) * ((2 : ℝ) ^ k / (((j - k : ℕ) : ℝ) * ((j - (k + 1)).factorial : ℝ))) := by
          rw [hfac]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2 : ℝ) ^ (k + 1) / ((j - (k + 1)).factorial : ℝ) := by
          rw [pow_succ']; field_simp [hj_pos.ne', hfk1_pos.ne']

lemma factorial_lower_bound (K : ℕ) :
    (K : ℝ) ^ K / Real.exp (K : ℝ) ≤ (K.factorial : ℝ) := by
  have hexp : (K : ℝ) ^ K / (K.factorial : ℝ) ≤ Real.exp (K : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg K) (K + 1)
    have hmem : (K : ℝ) ^ K / (K.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (K + 1), (K : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (K : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self K))
    exact hmem.trans hsum
  have hfac_pos : (0 : ℝ) < (K.factorial : ℝ) := by positivity
  have hexp_pos : (0 : ℝ) < Real.exp (K : ℝ) := Real.exp_pos _
  rw [div_le_iff₀ hexp_pos]
  rw [div_le_iff₀ hfac_pos] at hexp
  linarith [mul_comm (Real.exp (K : ℝ)) (K.factorial : ℝ)]

lemma factorial_le_pow_self (N : ℕ) : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ']
    have h1 : (N : ℝ) ^ N ≤ ((N + 1 : ℕ) : ℝ) ^ N :=
      pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast Nat.le_succ N) N
    exact mul_le_mul_of_nonneg_left (ih.trans h1) (by positivity)

lemma abs_sum_Rseq_le {n N M H k : ℕ} (ptilde : Idx n × Fin (N + 1) → ℤ)
    (hbd : ∀ x, |ptilde x| ≤ (H : ℤ))
    (hvan : ∀ j < M,
      PowerSeries.coeff j (Rseq (fun p =>
        ∑ l : Fin (N + 1),
          Polynomial.C (((N.factorial / l.1.factorial : ℕ) : ℤ) * ptilde (p, l)) *
            Polynomial.X ^ l.1) 0) = 0)
    (h2k : 2 * k ≤ M) :
    let P0 : Idx n → ℤ[X] := fun p =>
      ∑ l : Fin (N + 1),
        Polynomial.C (((N.factorial / l.1.factorial : ℕ) : ℤ) * ptilde (p, l)) *
          Polynomial.X ^ l.1
    let A : ℝ := 2 * ((n : ℝ) + 1)
    |∑ p : Idx n, (vR P0 k p).eval 1 * fVal p| ≤
      (Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ k * A ^ M *
        Real.exp A / (((M - k).factorial : ℕ) : ℝ) := by
  intro P0 A
  have hA_pos : 0 < A := by dsimp [A]; positivity
  -- First bound `|coeff j (Rseq P0 0)|` for every `j : ℕ`
  have hcoeff0 : ∀ j : ℕ,
      |PowerSeries.coeff j (Rseq P0 0)| ≤
        (Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * A ^ j / (j.factorial : ℝ) := by
    intro j
    rw [Rseq, map_sum]
    calc |∑ p : Idx n, PowerSeries.coeff j (((vR P0 0 p : ℝ[X]) : PowerSeries ℝ) * fPS p)|
        ≤ ∑ p : Idx n, |PowerSeries.coeff j (((vR P0 0 p : ℝ[X]) : PowerSeries ℝ) * fPS p)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Idx n, (N.factorial : ℝ) * (H : ℝ) * A ^ j / (j.factorial : ℝ) := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          calc |∑ l ∈ Finset.range (j + 1),
                  PowerSeries.coeff l ((vR P0 0 p : ℝ[X]) : PowerSeries ℝ) *
                    PowerSeries.coeff (j - l) (fPS p)|
              ≤ ∑ l ∈ Finset.range (j + 1),
                  |PowerSeries.coeff l ((vR P0 0 p : ℝ[X]) : PowerSeries ℝ)| *
                    |PowerSeries.coeff (j - l) (fPS p)| := by
                refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
                rw [abs_mul]
            _ ≤ ∑ l ∈ Finset.range (j + 1),
                  ((N.factorial : ℝ) * (H : ℝ) / (j.factorial : ℝ)) *
                    (j.choose l : ℝ) * ((n : ℝ) + 1) ^ j := by
                refine Finset.sum_le_sum fun l hl => ?_
                have hlj : l ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
                have hpoly : |PowerSeries.coeff l ((vR P0 0 p : ℝ[X]) : PowerSeries ℝ)| ≤
                    (N.factorial : ℝ) / (l.factorial : ℝ) * (H : ℝ) := by
                  rw [Polynomial.coeff_coe, vR, vZ, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
                  simp only [Polynomial.coeff_C_mul_X_pow]
                  by_cases hlN : l < N + 1
                  · rw [Finset.sum_eq_single (⟨l, hlN⟩ : Fin (N + 1))]
                    · simp only [↓reduceIte, Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast,
                        abs_mul]
                      rw [abs_of_nonneg (a := ((N.factorial / l.factorial : ℕ) : ℝ)) (Nat.cast_nonneg _)]
                      have hdiv : ((N.factorial / l.factorial : ℕ) : ℝ) =
                          (N.factorial : ℝ) / (l.factorial : ℝ) := by
                        have hdvd := Nat.factorial_dvd_factorial (show l ≤ N by omega)
                        have hmul : ((N.factorial / l.factorial : ℕ) : ℝ) * (l.factorial : ℝ) =
                            (N.factorial : ℝ) := by exact_mod_cast Nat.div_mul_cancel hdvd
                        exact eq_div_of_mul_eq (by positivity) hmul
                      rw [hdiv]
                      have hbdR : |(ptilde (p, ⟨l, hlN⟩) : ℝ)| ≤ (H : ℝ) := by
                        exact_mod_cast hbd (p, ⟨l, hlN⟩)
                      exact mul_le_mul_of_nonneg_left hbdR
                        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
                    · intro m' _ hml
                      have : l ≠ m'.1 := fun h => hml (Fin.ext h.symm)
                      simp [this]
                    · intro h; exact absurd (Finset.mem_univ _) h
                  · have hz : (∑ m' : Fin (N + 1),
                        if l = m'.1 then ((N.factorial / m'.1.factorial : ℕ) : ℤ) * ptilde (p, m') else 0) = 0 := by
                      refine Finset.sum_eq_zero fun m' _ => ?_
                      have : l ≠ m'.1 := by omega
                      simp [this]
                    rw [hz, map_zero, abs_zero]
                    positivity
                have hf_bd : |PowerSeries.coeff (j - l) (fPS p)| ≤
                    ((n : ℝ) + 1) ^ j / ((j - l).factorial : ℝ) := by
                  rw [coeff_fPS_eq_cQ, abs_div,
                    abs_of_nonneg (a := ((j - l).factorial : ℝ)) (Nat.cast_nonneg _)]
                  have hc1 : |(cQ p (j - l) : ℝ)| ≤ ((n : ℝ) + 1) ^ (j - l) := by
                    exact_mod_cast cQ_abs_le p (j - l)
                  have hc2 : ((n : ℝ) + 1) ^ (j - l) ≤ ((n : ℝ) + 1) ^ j :=
                    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (Nat.sub_le j l)
                  exact div_le_div_of_nonneg_right (hc1.trans hc2) (Nat.cast_nonneg _)
                have hch : (j.choose l : ℝ) * (l.factorial : ℝ) * ((j - l).factorial : ℝ) =
                    (j.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hlj
                have hfl : (l.factorial : ℝ) ≠ 0 := by positivity
                have hfjl : ((j - l).factorial : ℝ) ≠ 0 := by positivity
                have hfj : (j.factorial : ℝ) ≠ 0 := by positivity
                have hch_ne : (j.choose l : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hlj).ne'
                calc |PowerSeries.coeff l ((vR P0 0 p : ℝ[X]) : PowerSeries ℝ)| *
                      |PowerSeries.coeff (j - l) (fPS p)|
                    ≤ ((N.factorial : ℝ) / (l.factorial : ℝ) * (H : ℝ)) *
                      (((n : ℝ) + 1) ^ j / ((j - l).factorial : ℝ)) :=
                      mul_le_mul hpoly hf_bd (abs_nonneg _) (by positivity)
                  _ = ((N.factorial : ℝ) * (H : ℝ) / (j.factorial : ℝ)) *
                      (j.choose l : ℝ) * ((n : ℝ) + 1) ^ j := by
                      rw [← hch]; field_simp [hfl, hfjl, hch_ne]
            _ = (N.factorial : ℝ) * (H : ℝ) * A ^ j / (j.factorial : ℝ) := by
                have hbinom : (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ)) = (2 : ℝ) ^ j := by
                  have h1 := add_pow (1 : ℝ) (1 : ℝ) j
                  norm_num at h1
                  simpa using h1.symm
                rw [← Finset.sum_mul, ← Finset.mul_sum, hbinom]
                dsimp [A]; rw [mul_pow]; ring
      _ = _ := by simp [Finset.sum_const, mul_div_assoc, mul_assoc]
  -- Now sum `|coeff j (Rseq P0 k)|` over `j ≥ M` using `pow_div_factorial_le_two_pow_div`
  let C : ℝ := (Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ k *
      A ^ M / (((M - k).factorial : ℕ) : ℝ)
  have hC_nn : 0 ≤ C := by dsimp [C]; positivity
  have hdom : ∀ s : ℕ,
      |PowerSeries.coeff (M + s) (Rseq P0 k)| ≤ C * (A ^ s / (s.factorial : ℝ)) := by
    intro s
    rw [coeff_Rseq, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hcoeff0 (M + s)
    have h2 := pow_div_factorial_le_two_pow_div (M + s) k (by omega)
    have hfac_split : (((M - k).factorial : ℕ) : ℝ) * (s.factorial : ℝ) ≤
        (((M + s - k).factorial : ℕ) : ℝ) := by
      have hnat : (M - k).factorial * s.factorial ≤ (M + s - k).factorial := by
        have hch := Nat.choose_mul_factorial_mul_factorial (show M - k ≤ M + s - k by omega)
        have hsub : M + s - k - (M - k) = s := by omega
        rw [hsub] at hch
        have hpos : 1 ≤ (M + s - k).choose (M - k) := Nat.choose_pos (by omega)
        nlinarith
      exact_mod_cast hnat
    calc ((M + s : ℕ) : ℝ) ^ k * |PowerSeries.coeff (M + s) (Rseq P0 0)|
        ≤ ((M + s : ℕ) : ℝ) ^ k *
            ((Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * A ^ (M + s) /
              ((M + s).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * A ^ (M + s)) *
            (((M + s : ℕ) : ℝ) ^ k / ((M + s).factorial : ℝ)) := by ring
      _ ≤ ((Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * A ^ (M + s)) *
            ((2 : ℝ) ^ k / (((M + s - k).factorial : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ ((Fintype.card (Idx n) : ℝ) * (N.factorial : ℝ) * (H : ℝ) * A ^ (M + s)) *
            ((2 : ℝ) ^ k / ((((M - k).factorial : ℕ) : ℝ) * (s.factorial : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac_split
      _ = C * (A ^ s / (s.factorial : ℝ)) := by
          dsimp [C]; rw [pow_add]; ring
  have hsum_R := hasSum_coeff_Rseq P0 k
  have hsum_shift : HasSum (fun s : ℕ => PowerSeries.coeff (s + M) (Rseq P0 k))
      (∑ p : Idx n, (vR P0 k p).eval 1 * fVal p) := by
    have hfin0 : (∑ i ∈ Finset.range M, PowerSeries.coeff i (Rseq P0 k)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_Rseq, hvan i (Finset.mem_range.mp hi), mul_zero]
    have hsum_R' : HasSum (fun j : ℕ => PowerSeries.coeff j (Rseq P0 k))
        ((∑ p : Idx n, (vR P0 k p).eval 1 * fVal p) +
          ∑ i ∈ Finset.range M, PowerSeries.coeff i (Rseq P0 k)) := by
      rwa [hfin0, add_zero]
    exact (hasSum_nat_add_iff (f := fun j : ℕ => PowerSeries.coeff j (Rseq P0 k)) M).mpr hsum_R'
  have hsum_rhs : HasSum (fun s : ℕ => C * (A ^ s / (s.factorial : ℝ))) (C * Real.exp A) := by
    have hexp : HasSum (fun s : ℕ => A ^ s / (s.factorial : ℝ)) (Real.exp A) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      exact (Real.summable_pow_div_factorial A).hasSum
    exact hexp.mul_left C
  have hdom' : ∀ s : ℕ,
      ‖PowerSeries.coeff (s + M) (Rseq P0 k)‖ ≤ C * (A ^ s / (s.factorial : ℝ)) := by
    intro s
    rw [Real.norm_eq_abs, add_comm]
    exact hdom s
  have hsum_norm : Summable (fun s : ℕ => ‖PowerSeries.coeff (s + M) (Rseq P0 k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom' hsum_rhs.summable
  have hle_tsum : |∑ p : Idx n, (vR P0 k p).eval 1 * fVal p| ≤
      ∑' s : ℕ, ‖PowerSeries.coeff (s + M) (Rseq P0 k)‖ := by
    rw [← Real.norm_eq_abs, ← hsum_shift.tsum_eq]
    exact norm_tsum_le_tsum_norm hsum_norm
  have hle_C : (∑' s : ℕ, ‖PowerSeries.coeff (s + M) (Rseq P0 k)‖) ≤ C * Real.exp A := by
    rw [← hsum_rhs.tsum_eq]
    exact hsum_norm.tsum_le_tsum hdom' hsum_rhs.summable
  calc |∑ p : Idx n, (vR P0 k p).eval 1 * fVal p|
      ≤ C * Real.exp A := hle_tsum.trans hle_C
    _ = _ := by dsimp [C]; ring

private lemma rivoal_asymptotic_contradiction
    (m C4 N0 t : ℕ) (A Cc f0 detVal : ℝ)
    (hm2 : 2 ≤ m) (hC4_pos : 1 ≤ C4) (hA_ge1 : (1 : ℝ) ≤ A) (hCc_pos : 0 < Cc) (hf0_pos : 0 < f0)
    (hN0_1 : 16 * m ^ 3 + 16 ≤ N0)
    (hN0_2 : 2 * (Nat.ceil ((C4 : ℝ) ^ m * (4 : ℝ) ^ m * A ^ (2 * m) *
      (Real.exp 1) ^ (2 * m) * (4 : ℝ) ^ (m ^ 2)) + 1) ^ 4 ≤ N0)
    (hN0_3 : 4 * (Nat.ceil ((m.factorial : ℝ) * Cc * (m : ℝ) * Real.exp A *
      ((Nat.ceil ((C4 : ℝ) ^ m * (4 : ℝ) ^ m * A ^ (2 * m) *
        (Real.exp 1) ^ (2 * m) * (4 : ℝ) ^ (m ^ 2)) + 1 : ℕ) : ℝ) ^ 3 / f0) + 2) ≤ N0)
    (ht_bound : t ≤ (4 * N0) / (4 * m) + m ^ 2)
    (hlower : f0 ≤ detVal)
    (hdet_upper :
      let N := 4 * N0
      let δ := N / (4 * m)
      let M := m * (N + 1) - δ
      let K := M - (m + t)
      let H := C4 ^ N
      let Pbound : ℝ := ((2 * N : ℕ) : ℝ) ^ (m + t) * ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ)
      let Rbound : ℝ := (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (m + t) * A ^ M *
        Real.exp A / (K.factorial : ℝ)
      detVal ≤ (m.factorial : ℝ) * Cc * Rbound * Pbound ^ (m - 2)) : False := by
  let Cconst : ℝ := (m.factorial : ℝ) * Cc * (m : ℝ) * Real.exp A
  have hm_pos : 0 < m := by omega
  have hCconst_pos : 0 < Cconst := by
    dsimp [Cconst]
    have hmf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    exact mul_pos (mul_pos (mul_pos hmf hCc_pos) hmR) (Real.exp_pos A)
  let Cexp : ℝ :=
    ((C4 : ℝ) ^ m) * ((4 : ℝ) ^ m) * (A ^ (2 * m)) * ((Real.exp 1) ^ (2 * m)) * (4 : ℝ) ^ (m ^ 2)
  have hCexp_ge1 : (1 : ℝ) ≤ Cexp := by
    dsimp [Cexp]
    have h1 : (1 : ℝ) ≤ (C4 : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast hC4_pos)
    have h2 : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ A ^ (2 * m) := one_le_pow₀ hA_ge1
    have h4 : (1 : ℝ) ≤ (Real.exp 1) ^ (2 * m) := one_le_pow₀ (Real.one_le_exp zero_le_one)
    have h5 : (1 : ℝ) ≤ (4 : ℝ) ^ (m ^ 2) := one_le_pow₀ (by norm_num)
    have h12 : (1 : ℝ) ≤ (C4 : ℝ) ^ m * (4 : ℝ) ^ m := by nlinarith
    have h123 : (1 : ℝ) ≤ (C4 : ℝ) ^ m * (4 : ℝ) ^ m * A ^ (2 * m) := by nlinarith
    have h1234 : (1 : ℝ) ≤ (C4 : ℝ) ^ m * (4 : ℝ) ^ m * A ^ (2 * m) * (Real.exp 1) ^ (2 * m) := by nlinarith
    nlinarith
  let Cbig : ℕ := Nat.ceil Cexp + 1
  have hCbig_ge : Cexp ≤ (Cbig : ℝ) := by
    dsimp [Cbig]
    calc Cexp ≤ (Nat.ceil Cexp : ℝ) := Nat.le_ceil Cexp
      _ ≤ (Nat.ceil Cexp : ℝ) + 1 := by linarith
      _ = ((Nat.ceil Cexp + 1 : ℕ) : ℝ) := by push_cast; ring
  have hCbig_ge2 : 2 ≤ Cbig := by
    dsimp [Cbig]
    have h1 : 1 ≤ Nat.ceil Cexp := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.ceil_eq_zero.mp h0
      linarith)
    omega
  let N : ℕ := 4 * N0
  let δ : ℕ := N / (4 * m)
  let M : ℕ := m * (N + 1) - δ
  let K : ℕ := M - (m + t)
  let H : ℕ := C4 ^ N
  let Pbound : ℝ := ((2 * N : ℕ) : ℝ) ^ (m + t) * ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ)
  let Rbound : ℝ := (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (m + t) * A ^ M *
    Real.exp A / (K.factorial : ℝ)
  have hA_nn : (0 : ℝ) ≤ A := zero_le_one.trans hA_ge1
  have hPbound_pos : 0 ≤ Pbound :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hm_le_m2 : m ≤ m ^ 2 := by nlinarith
  have hm2_le_m3 : m ^ 2 ≤ m ^ 3 := by nlinarith
  have hN_ge_16m3 : 16 * m ^ 3 + 16 ≤ N := by dsimp [N]; omega
  have ht_bound' : t ≤ δ + m ^ 2 := ht_bound
  let E : ℕ := (m - 1) * N + (m - 2) * (m + t)
  have hE_add_le_K : E + N / 4 ≤ K := by
    have hδ_bound : 4 * m * δ ≤ N := Nat.mul_div_le N (4 * m)
    have hmt_le : m + t ≤ m + δ + m ^ 2 := by omega
    have hmul_m2 : (m - 2) * (m + t) ≤ (m - 2) * δ + (m - 2) * (m + m ^ 2) := by
      calc (m - 2) * (m + t) ≤ (m - 2) * (m + δ + m ^ 2) := Nat.mul_le_mul_left _ hmt_le
        _ = (m - 2) * δ + (m - 2) * (m + m ^ 2) := by ring
    have hmδ : m * δ ≤ N / 4 := by
      have : 4 * (m * δ) ≤ N := by linarith
      omega
    have hm_cubed : (m - 2) * (m + m ^ 2) + m + m ^ 2 ≤ 4 * m ^ 3 := by
      have h1 : (m - 2) * (m + m ^ 2) ≤ m * (m + m ^ 2) := Nat.mul_le_mul_right _ (Nat.sub_le m 2)
      have h2 : m * (m + m ^ 2) = m ^ 2 + m ^ 3 := by ring
      omega
    have hmN1 : m * (N + 1) = (m - 1) * N + N + m := by
      rw [mul_add, mul_one, ← Nat.sub_add_cancel (Nat.le_mul_of_pos_left N hm_pos), Nat.sub_mul, one_mul]
    have hδ_split : (m - 2) * δ + 2 * δ = m * δ := by
      calc (m - 2) * δ + 2 * δ = ((m - 2) + 2) * δ := by ring
        _ = m * δ := by rw [Nat.sub_add_cancel hm2]
    dsimp only [K, M, E]
    omega
  have hN_le_K : N ≤ K := by
    have h1 : N ≤ (m - 1) * N := Nat.le_mul_of_pos_left N (by omega)
    dsimp only [E] at hE_add_le_K
    omega
  have hmN_le_2mN : m * (N + 1) ≤ 2 * m * N := by
    have h1 : N + 1 ≤ 2 * N := by omega
    calc m * (N + 1) ≤ m * (2 * N) := Nat.mul_le_mul_left m h1
      _ = 2 * m * N := by ring
  have hM_le_2mN : M ≤ 2 * m * N := (Nat.sub_le _ _).trans hmN_le_2mN
  have hK_le_2mN : K ≤ 2 * m * N := (Nat.sub_le _ _).trans hM_le_2mN
  have hP_simplify : Pbound ≤
      (N : ℝ) ^ (N + (m + t)) * (2 : ℝ) ^ (m + t) * (2 : ℝ) ^ N * (C4 : ℝ) ^ N := by
    have h2N : ((2 * N : ℕ) : ℝ) ^ (m + t) = (2 : ℝ) ^ (m + t) * (N : ℝ) ^ (m + t) := by
      push_cast; rw [mul_pow]
    have hN1 : ((N + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by
      have : N + 1 ≤ 2 ^ N := by
        have hlt := Nat.lt_two_pow_self (n := N)
        omega
      exact_mod_cast this
    have hfac := factorial_le_pow_self N
    dsimp [Pbound, H]
    rw [h2N, Nat.cast_pow]
    calc (2 : ℝ) ^ (m + t) * (N : ℝ) ^ (m + t) * ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (C4 : ℝ) ^ N
        ≤ (2 : ℝ) ^ (m + t) * (N : ℝ) ^ (m + t) * (2 : ℝ) ^ N * (N : ℝ) ^ N * (C4 : ℝ) ^ N := by
          have h1 : ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) ≤ (2 : ℝ) ^ N * (N : ℝ) ^ N :=
            mul_le_mul hN1 hfac (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
          have h2 : 0 ≤ (2 : ℝ) ^ (m + t) * (N : ℝ) ^ (m + t) :=
            mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Nat.cast_nonneg _) _)
          have h3 : 0 ≤ (C4 : ℝ) ^ N := pow_nonneg (Nat.cast_nonneg _) _
          have h12 := mul_le_mul_of_nonneg_left h1 h2
          have h123 := mul_le_mul_of_nonneg_right h12 h3
          linarith
      _ = (N : ℝ) ^ (N + (m + t)) * (2 : ℝ) ^ (m + t) * (2 : ℝ) ^ N * (C4 : ℝ) ^ N := by
          rw [pow_add]; ring
  have hP_pow : Pbound ^ (m - 2) ≤
      (N : ℝ) ^ ((m - 2) * N + (m - 2) * (m + t)) *
      (2 : ℝ) ^ ((m - 2) * (m + t)) * (2 : ℝ) ^ ((m - 2) * N) * (C4 : ℝ) ^ ((m - 2) * N) := by
    refine (pow_le_pow_left₀ hPbound_pos hP_simplify (m - 2)).trans ?_
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    rw [mul_comm (N + (m + t)) (m - 2), mul_add, mul_comm (m + t) (m - 2), mul_comm N (m - 2)]
  have hinvK : (1 : ℝ) / (K.factorial : ℝ) ≤ (Real.exp 1) ^ (2 * m * N) / (K : ℝ) ^ K := by
    have hlb := factorial_lower_bound K
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    have hKpow_pos : (0 : ℝ) < (K : ℝ) ^ K := pow_pos hKpos K
    have hKf_pos : (0 : ℝ) < (K.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos K
    have hexp_eq : Real.exp (K : ℝ) = (Real.exp 1) ^ K := by
      rw [← Real.exp_nat_mul, mul_one]
    have h1 : (1 : ℝ) / (K.factorial : ℝ) ≤ (Real.exp 1) ^ K / (K : ℝ) ^ K := by
      rw [div_le_div_iff₀ hKf_pos hKpow_pos, one_mul, ← hexp_eq]
      have := (div_le_iff₀ (Real.exp_pos (K : ℝ))).mp hlb
      linarith [mul_comm (Real.exp (K : ℝ)) (K.factorial : ℝ)]
    have h2 : (Real.exp 1) ^ K ≤ (Real.exp 1) ^ (2 * m * N) :=
      pow_le_pow_right₀ (Real.one_le_exp zero_le_one) hK_le_2mN
    exact h1.trans (div_le_div_of_nonneg_right h2 hKpow_pos.le)
  have hR_simplify : Rbound ≤
      (m : ℝ) * Real.exp A * (N : ℝ) ^ N * (C4 : ℝ) ^ N * (2 : ℝ) ^ (m + t) *
        A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N) / (K : ℝ) ^ K := by
    dsimp [Rbound, H]
    rw [Nat.cast_pow]
    have hfac := factorial_le_pow_self N
    have hA_le : A ^ M ≤ A ^ (2 * m * N) := pow_le_pow_right₀ hA_ge1 hM_le_2mN
    calc (m : ℝ) * (N.factorial : ℝ) * (C4 : ℝ) ^ N * (2 : ℝ) ^ (m + t) * A ^ M * Real.exp A /
            (K.factorial : ℝ)
        = ((m : ℝ) * Real.exp A * (N.factorial : ℝ) * (C4 : ℝ) ^ N * (2 : ℝ) ^ (m + t) * A ^ M) *
            (1 / (K.factorial : ℝ)) := by ring
      _ ≤ ((m : ℝ) * Real.exp A * (N : ℝ) ^ N * (C4 : ℝ) ^ N * (2 : ℝ) ^ (m + t) * A ^ (2 * m * N)) *
            ((Real.exp 1) ^ (2 * m * N) / (K : ℝ) ^ K) := by
          refine mul_le_mul ?_ hinvK (div_nonneg zero_le_one (Nat.cast_nonneg _))
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
              (Real.exp_pos A).le) (pow_nonneg (Nat.cast_nonneg _) _))
              (pow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg (by norm_num) _))
              (pow_nonneg hA_nn _))
          have h1 : (N.factorial : ℝ) * A ^ M ≤ (N : ℝ) ^ N * A ^ (2 * m * N) :=
            mul_le_mul hfac hA_le (pow_nonneg hA_nn _) (pow_nonneg (Nat.cast_nonneg _) _)
          have h2 : 0 ≤ (m : ℝ) * Real.exp A * (C4 : ℝ) ^ N * (2 : ℝ) ^ (m + t) :=
            mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos A).le)
              (pow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg (by norm_num) _)
          have h12 := mul_le_mul_of_nonneg_left h1 h2
          linarith
      _ = _ := by ring
  have hpow_2_comb : (2 : ℝ) ^ (m + t) * (2 : ℝ) ^ ((m - 2) * (m + t)) * (2 : ℝ) ^ ((m - 2) * N) ≤
      ((4 : ℝ) ^ m * (4 : ℝ) ^ (m ^ 2)) ^ N := by
    have hexp_le : (m + t) + (m - 2) * (m + t) + (m - 2) * N ≤ 2 * m * N + 2 * m ^ 2 * N := by
      have hmt : m + t ≤ N + m ^ 2 := by
        have hδN : δ ≤ N := Nat.div_le_self N (4 * m)
        have hm_le_N : m ≤ N := by omega
        --Wait: `m + t ≤ m + δ + m^2`. Since `4 * m * δ ≤ N` and `m ≥ 2`, `δ ≤ N / 8` and `m ≤ N / 16`, so `m + δ ≤ N`!
        have hδ_le_N2 : 2 * δ ≤ N := by
          have h1 : 4 * m * δ ≤ N := Nat.mul_div_le N (4 * m)
          have h2 : 2 * δ ≤ 4 * m * δ := Nat.mul_le_mul_right δ (by omega)
          exact h2.trans h1
        have h2m_le_N : 2 * m ≤ N := by omega
        omega
      have h1 : (m - 1) * (m + t) ≤ m * (N + m ^ 2) := Nat.mul_le_mul (by omega) hmt
      have h2 : (m + t) + (m - 2) * (m + t) = (m - 1) * (m + t) := by
        calc (m + t) + (m - 2) * (m + t) = (1 + (m - 2)) * (m + t) := by ring
          _ = (m - 1) * (m + t) := by rw [show 1 + (m - 2) = m - 1 by omega]
      have h3 : m * m ^ 2 ≤ m ^ 2 * N := by
        rw [mul_comm m (m ^ 2)]
        exact Nat.mul_le_mul_left (m ^ 2) (by omega)
      have h4 : (m - 2) * N ≤ m * N := Nat.mul_le_mul_right N (by omega)
      have h5 : m * (N + m ^ 2) = m * N + m * m ^ 2 := by ring
      have h6 : 2 * m * N = m * N + m * N := by ring
      have h7 : 2 * m ^ 2 * N = m ^ 2 * N + m ^ 2 * N := by ring
      omega
    have h4eq : ((4 : ℝ) ^ m * (4 : ℝ) ^ (m ^ 2)) ^ N = (2 : ℝ) ^ (2 * m * N + 2 * m ^ 2 * N) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_mul, add_mul, mul_assoc, mul_assoc]
    rw [← pow_add, ← pow_add, h4eq]
    exact pow_le_pow_right₀ (by norm_num) hexp_le
  have hC4_comb : (C4 : ℝ) ^ N * (C4 : ℝ) ^ ((m - 2) * N) ≤ ((C4 : ℝ) ^ m) ^ N := by
    rw [← pow_add, ← pow_mul, mul_comm m N]
    refine pow_le_pow_right₀ (by exact_mod_cast hC4_pos) ?_
    have : N + (m - 2) * N = (m - 1) * N := by
      calc N + (m - 2) * N = (1 + (m - 2)) * N := by ring
        _ = (m - 1) * N := by rw [show 1 + (m - 2) = m - 1 by omega]
    rw [this, mul_comm N m]; exact Nat.mul_le_mul_right N (by omega)
  have hNK_ratio : (N : ℝ) ^ E / (K : ℝ) ^ K ≤ (1 : ℝ) / (N : ℝ) ^ (N / 4) := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    have hKge : (N : ℝ) ^ (E + N / 4) ≤ (K : ℝ) ^ K := by
      calc (N : ℝ) ^ (E + N / 4)
          ≤ (N : ℝ) ^ K := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ N by omega)) hE_add_le_K
        _ ≤ (K : ℝ) ^ K := pow_le_pow_left₀ hNpos.le (by exact_mod_cast hN_le_K) K
    rw [div_le_div_iff₀ (pow_pos hKpos K) (pow_pos hNpos _), one_mul, ← pow_add]
    exact hKge
  have hcomb : (m.factorial : ℝ) * Cc * Rbound * Pbound ^ (m - 2) ≤
      Cconst * Cexp ^ N / (N : ℝ) ^ (N / 4) := by
    have h1 := mul_le_mul hR_simplify hP_pow (pow_nonneg hPbound_pos _)
      (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (Nat.cast_nonneg _) (Real.exp_pos A).le) (pow_nonneg (Nat.cast_nonneg _) _))
        (pow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg (by norm_num) _))
        (pow_nonneg hA_nn _)) (pow_nonneg (Real.exp_pos 1).le _))
        (pow_nonneg (Nat.cast_nonneg _) _))
    have h2 : (m.factorial : ℝ) * Cc * (Rbound * Pbound ^ (m - 2)) ≤
        Cconst *
          (((C4 : ℝ) ^ N * (C4 : ℝ) ^ ((m - 2) * N)) *
           ((2 : ℝ) ^ (m + t) * (2 : ℝ) ^ ((m - 2) * (m + t)) * (2 : ℝ) ^ ((m - 2) * N)) *
           A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N)) *
          ((N : ℝ) ^ E / (K : ℝ) ^ K) := by
      have hNE : (N : ℝ) ^ N * (N : ℝ) ^ ((m - 2) * N + (m - 2) * (m + t)) = (N : ℝ) ^ E := by
        rw [← pow_add]
        congr 1
        dsimp [E]
        have hE1 : N + (m - 2) * N = (m - 1) * N := by
          calc N + (m - 2) * N = (1 + (m - 2)) * N := by ring
            _ = (m - 1) * N := by rw [show 1 + (m - 2) = m - 1 by omega]
        omega
      have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg m.factorial) hCc_pos.le)
      refine hmul.trans_eq ?_
      dsimp [Cconst]
      rw [← hNE]
      ring
    have hCexp_eq : Cexp ^ N =
        ((C4 : ℝ) ^ m) ^ N * ((4 : ℝ) ^ m * (4 : ℝ) ^ (m ^ 2)) ^ N *
          A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N) := by
      dsimp [Cexp]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul A, ← pow_mul (Real.exp 1)]
      ring
    have hcoeff_le :
        ((C4 : ℝ) ^ N * (C4 : ℝ) ^ ((m - 2) * N)) *
          ((2 : ℝ) ^ (m + t) * (2 : ℝ) ^ ((m - 2) * (m + t)) * (2 : ℝ) ^ ((m - 2) * N)) *
          A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N) ≤ Cexp ^ N := by
      rw [hCexp_eq]
      have h12 := mul_le_mul hC4_comb hpow_2_comb
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
          (pow_nonneg (by norm_num) _))
        (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
      have h34 : 0 ≤ A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N) :=
        mul_nonneg (pow_nonneg hA_nn _) (pow_nonneg (Real.exp_pos 1).le _)
      calc _ = (((C4 : ℝ) ^ N * (C4 : ℝ) ^ ((m - 2) * N)) *
                  ((2 : ℝ) ^ (m + t) * (2 : ℝ) ^ ((m - 2) * (m + t)) * (2 : ℝ) ^ ((m - 2) * N))) *
                  (A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N)) := by ring
        _ ≤ (((C4 : ℝ) ^ m) ^ N * ((4 : ℝ) ^ m * (4 : ℝ) ^ (m ^ 2)) ^ N) *
                  (A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N)) :=
            mul_le_mul_of_nonneg_right h12 h34
        _ = _ := by ring
    calc (m.factorial : ℝ) * Cc * Rbound * Pbound ^ (m - 2)
        = (m.factorial : ℝ) * Cc * (Rbound * Pbound ^ (m - 2)) := by ring
      _ ≤ Cconst *
            (((C4 : ℝ) ^ N * (C4 : ℝ) ^ ((m - 2) * N)) *
             ((2 : ℝ) ^ (m + t) * (2 : ℝ) ^ ((m - 2) * (m + t)) * (2 : ℝ) ^ ((m - 2) * N)) *
             A ^ (2 * m * N) * (Real.exp 1) ^ (2 * m * N)) *
            ((N : ℝ) ^ E / (K : ℝ) ^ K) := h2
      _ ≤ Cconst * Cexp ^ N * ((1 : ℝ) / (N : ℝ) ^ (N / 4)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcoeff_le hCconst_pos.le) hNK_ratio
            (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
            (mul_nonneg hCconst_pos.le (pow_nonneg (zero_le_one.trans hCexp_ge1) _))
      _ = Cconst * Cexp ^ N / (N : ℝ) ^ (N / 4) := by ring
  have hfinal_lt : Cconst * Cexp ^ N / (N : ℝ) ^ (N / 4) < f0 := by
    have hNdiv : N / 4 = N0 := by dsimp [N]; omega
    have hN_eq : N = 4 * N0 := rfl
    have hCexp_N : Cexp ^ N ≤ ((Cbig : ℝ) ^ 4) ^ N0 := by
      rw [hN_eq, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans hCexp_ge1) 4)
        (pow_le_pow_left₀ (zero_le_one.trans hCexp_ge1) hCbig_ge 4) N0
    have hN_ge_2C : 2 * (Cbig : ℝ) ^ 4 ≤ (N : ℝ) := by
      have : 2 * Cbig ^ 4 ≤ N := by dsimp [N, Cbig, Cexp]; omega
      exact_mod_cast this
    have hratio : ((Cbig : ℝ) ^ 4) ^ N0 / (N : ℝ) ^ N0 ≤ (1 : ℝ) / (2 : ℝ) ^ N0 := by
      rw [← div_pow, ← _root_.one_div_pow]
      refine pow_le_pow_left₀ (div_nonneg (pow_nonneg (Nat.cast_nonneg _) 4) (Nat.cast_nonneg _)) ?_ N0
      rw [div_le_div_iff₀ (by exact_mod_cast (show 0 < N by omega)) (by norm_num)]
      linarith
    have h2N0_gt : Cconst / f0 < (2 : ℝ) ^ N0 := by
      have hceil : Nat.ceil (Cconst * (Cbig : ℝ) ^ 3 / f0) + 2 ≤ N0 := by
        dsimp [Cconst, Cbig, Cexp]; omega
      have hlt_pow : N0 < 2 ^ N0 := Nat.lt_two_pow_self
      have hCbig3 : (1 : ℝ) ≤ (Cbig : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ Cbig by omega))
      have hle1 : Cconst / f0 ≤ Cconst * (Cbig : ℝ) ^ 3 / f0 := by
        refine div_le_div_of_nonneg_right ?_ hf0_pos.le
        exact le_mul_of_one_le_right hCconst_pos.le hCbig3
      have hle2 : Cconst * (Cbig : ℝ) ^ 3 / f0 ≤ (Nat.ceil (Cconst * (Cbig : ℝ) ^ 3 / f0) : ℝ) :=
        Nat.le_ceil _
      have hlt3 : (Nat.ceil (Cconst * (Cbig : ℝ) ^ 3 / f0) : ℝ) < (2 : ℝ) ^ N0 := by
        exact_mod_cast (show Nat.ceil (Cconst * (Cbig : ℝ) ^ 3 / f0) < 2 ^ N0 by omega)
      exact lt_of_le_of_lt (hle1.trans hle2) hlt3
    rw [hNdiv]
    calc Cconst * Cexp ^ N / (N : ℝ) ^ N0
        ≤ Cconst * ((Cbig : ℝ) ^ 4) ^ N0 / (N : ℝ) ^ N0 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCexp_N hCconst_pos.le)
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ = Cconst * (((Cbig : ℝ) ^ 4) ^ N0 / (N : ℝ) ^ N0) := by ring
      _ ≤ Cconst * ((1 : ℝ) / (2 : ℝ) ^ N0) := mul_le_mul_of_nonneg_left hratio hCconst_pos.le
      _ = Cconst / (2 : ℝ) ^ N0 := by ring
      _ < f0 := by
          rw [div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) N0)]
          have := (div_lt_iff₀ hf0_pos).mp h2N0_gt
          linarith [mul_comm f0 ((2 : ℝ) ^ N0)]
  exact not_lt.mpr (hlower.trans (hdet_upper.trans hcomb)) hfinal_lt

private lemma det_abs_le_of_row_col_bounds {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (i0 j0 : Fin m) (Cc Rbound Pbound : ℝ)
    (hCc_nn : 0 ≤ Cc) (hR_nn : 0 ≤ Rbound) (hP_nn : 0 ≤ Pbound)
    (hzero_ij : M i0 j0 = 0)
    (hrow : ∀ j : Fin m, |M i0 j| ≤ Cc)
    (hcol : ∀ i : Fin m, i ≠ i0 → |M i j0| ≤ Rbound)
    (hrest : ∀ i j : Fin m, i ≠ i0 → j ≠ j0 → |M i j| ≤ Pbound) :
    |M.det| ≤ (m.factorial : ℝ) * Cc * Rbound * Pbound ^ (m - 2) := by
  rw [Matrix.det_apply]
  calc |∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin m), |Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), Cc * Rbound * Pbound ^ (m - 2) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have hsign : |Equiv.Perm.sign σ • ∏ i : Fin m, M (σ i) i| =
            ∏ i : Fin m, |M (σ i) i| := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod]
        rw [hsign]
        by_cases hhit : σ j0 = i0
        · have hzero : (∏ i : Fin m, |M (σ i) i|) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ j0) (by rw [hhit, hzero_ij, abs_zero])
          rw [hzero]
          exact mul_nonneg (mul_nonneg hCc_nn hR_nn) (pow_nonneg hP_nn _)
        · let j1 : Fin m := σ.symm i0
          have hj1_ne : j1 ≠ j0 := fun h => hhit (by rw [← h]; exact σ.apply_symm_apply i0)
          have hσj1 : σ j1 = i0 := σ.apply_symm_apply i0
          let Srest : Finset (Fin m) := (Finset.univ.erase j0).erase j1
          have hcard_rest : Srest.card = m - 2 := by
            have h1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj1_ne, Finset.mem_univ _⟩
            rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ j0),
              Finset.card_univ, Fintype.card_fin]
            omega
          have hprod_split : (∏ i : Fin m, |M (σ i) i|) =
              |M (σ j1) j1| * |M (σ j0) j0| * ∏ i ∈ Srest, |M (σ i) i| := by
            have h1 := (Finset.mul_prod_erase Finset.univ (fun i => |M (σ i) i|) (Finset.mem_univ j0)).symm
            have hj1_mem : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj1_ne, Finset.mem_univ _⟩
            have h2 := (Finset.mul_prod_erase (Finset.univ.erase j0) (fun i => |M (σ i) i|) hj1_mem).symm
            rw [h1, h2]; ring
          rw [hprod_split]
          have hb1 : |M (σ j1) j1| ≤ Cc := by rw [hσj1]; exact hrow j1
          have hb2 : |M (σ j0) j0| ≤ Rbound := hcol (σ j0) hhit
          have hb3 : (∏ i ∈ Srest, |M (σ i) i|) ≤ Pbound ^ (m - 2) := by
            calc ∏ i ∈ Srest, |M (σ i) i|
                ≤ ∏ _i ∈ Srest, Pbound := by
                  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => ?_
                  have hi1 : i ≠ j1 := (Finset.mem_erase.mp hi).1
                  have hi0 : i ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
                  have hσi : σ i ≠ i0 := fun h => hi1 (by rw [← hσj1] at h; exact σ.injective h)
                  exact hrest (σ i) i hσi hi0
              _ = Pbound ^ Srest.card := Finset.prod_const Pbound
              _ = Pbound ^ (m - 2) := by rw [hcard_rest]
          have hb12 : |M (σ j1) j1| * |M (σ j0) j0| ≤ Cc * Rbound :=
            mul_le_mul hb1 hb2 (abs_nonneg _) hCc_nn
          exact mul_le_mul hb12 hb3 (Finset.prod_nonneg fun _ _ => abs_nonneg _)
            (mul_nonneg hCc_nn hR_nn)
    _ = (m.factorial : ℝ) * Cc * Rbound * Pbound ^ (m - 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma not_both_algebraic
    (hγ : IsAlgebraic ℚ Real.eulerMascheroniConstant)
    (hδ : IsAlgebraic ℚ gompertzConstant) : False := by
  obtain ⟨n, c, ⟨p0, hp0⟩, hrel⟩ := exists_int_linear_relation_of_algebraic hγ hδ
  let m := Fintype.card (Idx n)
  let e : Fin m ≃ Idx n := (Fintype.equivFin (Idx n)).symm
  have hm_pos : 0 < m := by
    dsimp [m]; rw [card_idx]; exact Nat.div_pos (by nlinarith) (by norm_num)
  -- Handle `m = 1` directly
  by_cases hm1 : m = 1
  · have hall : ∀ p : Idx n, p = p0 := by
      intro p
      have hcard : Fintype.card (Idx n) = 1 := hm1
      exact (Fintype.card_le_one_iff.mp hcard.le) p p0
    have hsum1 : ∑ p : Idx n, (c p : ℝ) * fVal p = (c p0 : ℝ) * fVal p0 := by
      rw [Finset.sum_eq_single p0]
      · intro p _ hp; exact absurd (hall p) hp
      · intro h; exact absurd (Finset.mem_univ _) h
    have h0 : (c p0 : ℝ) * fVal p0 = 0 := by rw [← hsum1]; exact hrel
    have hc0 : (c p0 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hp0
    exact (mul_ne_zero hc0 (fVal_pos p0).ne') h0
  have hm2 : 2 ≤ m := by omega
  obtain ⟨C4, hC4_pos, hPade⟩ := exists_pade_form n
  let A : ℝ := 2 * ((n : ℝ) + 1)
  have hA_ge1 : (1 : ℝ) ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) n]
  let Cc : ℝ := ∑ p : Idx n, |(c p : ℝ)| + 1
  have hCc_pos : 0 < Cc := by
    have : 0 ≤ ∑ p : Idx n, |(c p : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [Cc]; linarith
  -- Choose a single big constant `Cbig : ℕ` so that `|fVal p0| ≤ Cconst * Cbig^N / N^(N/4)`
  -- Let's make explicit `N`-independent constants:
  let Cconst : ℝ := (m.factorial : ℝ) * Cc * (m : ℝ) * Real.exp A
  have hCconst_pos : 0 < Cconst := by
    dsimp [Cconst]
    have hmf : (0 : ℝ) < (m.factorial : ℝ) := by positivity
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have hexp : (0 : ℝ) < Real.exp A := Real.exp_pos A
    positivity
  -- Base exponential constant `Cexp : ℝ` (`≥ 1`)
  let Cexp : ℝ :=
    ((C4 : ℝ) ^ m) * ((4 : ℝ) ^ m) * (A ^ (2 * m)) * ((Real.exp 1) ^ (2 * m)) * (4 : ℝ) ^ (m ^ 2)
  have hCexp_ge1 : (1 : ℝ) ≤ Cexp := by
    dsimp [Cexp]
    have h1 : (1 : ℝ) ≤ (C4 : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast hC4_pos)
    have h2 : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ A ^ (2 * m) := one_le_pow₀ hA_ge1
    have h4 : (1 : ℝ) ≤ (Real.exp 1) ^ (2 * m) := one_le_pow₀ (Real.one_le_exp zero_le_one)
    have h5 : (1 : ℝ) ≤ (4 : ℝ) ^ (m ^ 2) := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (C4 : ℝ) ^ m) (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ m),
      one_le_mul_of_one_le_of_one_le h1 h2,
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3,
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4]
  let Cbig : ℕ := Nat.ceil Cexp + 1
  have hCbig_ge : Cexp ≤ (Cbig : ℝ) :=
    (Nat.le_ceil Cexp).trans (by exact_mod_cast Nat.le_succ _)
  have hCbig_ge2 : 2 ≤ Cbig := by
    have : 1 ≤ Nat.ceil Cexp := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.le_ceil Cexp
      rw [h0, Nat.cast_zero] at this
      linarith)
    dsimp [Cbig]; omega
  -- Pick `N` large enough for EVERY condition simultaneously (keep `N0` opaque to avoid `whnf` unfolding)!
  obtain ⟨N0, hN0_1, hN0_2, hN0_3⟩ :
      ∃ N0 : ℕ,
        16 * m ^ 3 + 8 * m * (3 * n + 1) + 16 ≤ N0 ∧
        2 * Cbig ^ 4 ≤ N0 ∧
        4 * (Nat.ceil (Cconst * (Cbig : ℝ) ^ 3 / fVal p0) + 2) ≤ N0 :=
    ⟨max (16 * m ^ 3 + 8 * m * (3 * n + 1) + 16)
      (max (2 * Cbig ^ 4) (4 * (Nat.ceil (Cconst * (Cbig : ℝ) ^ 3 / fVal p0) + 2))),
      le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  let N : ℕ := 4 * N0
  have hm_le_m2 : m ≤ m ^ 2 := by rw [sq]; exact Nat.le_mul_self m
  have hm2_le_m3 : m ^ 2 ≤ m ^ 3 := by
    calc m ^ 2 = m ^ 2 * 1 := (mul_one _).symm
      _ ≤ m ^ 2 * m := Nat.mul_le_mul_left _ hm_pos
      _ = m ^ 3 := by ring
  have hN_ge_8m : 8 * m ≤ N := by
    have : 16 * m ^ 3 ≤ N0 := le_trans (by omega) hN0_1
    dsimp [N]; omega
  have hN_ge_16m3 : 16 * m ^ 3 + 8 * m * (3 * n + 1) + 16 ≤ N := by
    dsimp [N]; omega
  -- Construct Padé form at degree `N`
  let δ := N / (4 * m)
  let M := m * (N + 1) - δ
  obtain ⟨ptilde, hptilde_ne, hptilde_bd, hvan⟩ := hPade N hN_ge_8m
  let P0 : Idx n → ℤ[X] := fun p =>
    ∑ l : Fin (N + 1),
      Polynomial.C (((N.factorial / l.1.factorial : ℕ) : ℤ) * ptilde (p, l)) *
        Polynomial.X ^ l.1
  have hP0_ne : ∃ p, P0 p ≠ 0 := by
    obtain ⟨⟨p, l⟩, hpl⟩ := hptilde_ne
    refine ⟨p, ?_⟩
    intro h0
    have hl := congrArg (fun Q : ℤ[X] => Q.coeff l.1) h0
    simp only [P0, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hl
    rw [Finset.sum_eq_single l] at hl
    · simp only [↓reduceIte] at hl
      have hfac_pos : 0 < N.factorial / l.1.factorial :=
        Nat.div_pos (Nat.factorial_le (Nat.le_of_lt_succ l.2)) (Nat.factorial_pos _)
      have hne1 : ((N.factorial / l.1.factorial : ℕ) : ℤ) ≠ 0 := by omega
      exact mul_ne_zero hne1 hpl hl
    · intro l' _ hl'
      have : l.1 ≠ l'.1 := fun h => hl' (Fin.ext h.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdeg0 : ∀ p : Idx n, (vR P0 0 p).natDegree ≤ N := by
    intro p
    refine Polynomial.natDegree_map_le.trans ?_
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun l _ => ?_⟩
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ l.2)
  have hM_big : (m - 1) * N + m * m < M := by
    have hδ_le : δ ≤ N0 := by
      have h1 : δ ≤ N / 4 := by
        dsimp [δ]; exact Nat.div_le_div_left (by omega : 4 ≤ 4 * m) (by norm_num)
      have h2 : N / 4 = N0 := by dsimp [N]; omega
      omega
    have hmN_split : (m - 1) * N + N = m * N := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left N hm_pos)]
    have hmN1 : m * (N + 1) = (m - 1) * N + N + m := by rw [hmN_split]; ring
    have hmsq : m * m = m ^ 2 := (sq m).symm
    dsimp only [M]
    rw [hmN1, hmsq]
    have hN_eq4 : N = 4 * N0 := rfl
    omega
  obtain ⟨hΔ_ne, ht_le⟩ := shidlovskii_zero_order P0 hP0_ne hdeg0 hvan hM_big
  obtain ⟨k, hk_lt, hM1_det⟩ := exists_full_rank_rows_at_one P0 hΔ_ne
  let t := Polynomial.rootMultiplicity 1 (Matrix.of fun i j : Fin m => vR P0 i.1 (e j)).det
  have ht_bound : t ≤ δ + m ^ 2 := by
    have ht_le' : t ≤ m * N + m * (m - 1) / 2 - M := ht_le
    have h1 : m * (m - 1) / 2 ≤ m ^ 2 :=
      (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left m (Nat.sub_le m 1))
    have h2 : m * N + m * (m - 1) / 2 - M ≤ δ + m ^ 2 := by
      have hmN1 : m * (N + 1) = m * N + m := by ring
      have hδU : δ ≤ m * N + m := (Nat.div_le_self N (4 * m)).trans (by nlinarith)
      refine Nat.sub_le_of_le_add ?_
      have hM_add : M + δ = m * N + m := by
        dsimp only [M]; rw [hmN1]; exact Nat.sub_add_cancel hδU
      omega
    exact ht_le'.trans h2
  -- Replace one row of the integer matrix `MZ` by `c ∘ e` preserving `det ≠ 0`
  let MZ : Matrix (Fin m) (Fin m) ℤ := fun i j => (vZ P0 (k i) (e j)).eval 1
  let M1 : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => (vR P0 (k i) (e j)).eval 1
  have hM1_map : M1 = MZ.map (Int.castRingHom ℝ) := by
    apply Matrix.ext; intro i j
    simp only [M1, MZ, vR, Matrix.of_apply, Polynomial.eval_map]
    have h1 : (1 : ℝ) = (Int.castRingHom ℝ) (1 : ℤ) := by simp
    rw [h1, Polynomial.eval₂_hom]
    rfl
  -- Express `cR := fun j => (c (e j) : ℝ)` as `∑ i, lam i • M1 i`
  let cR : Fin m → ℝ := fun j => (c (e j) : ℝ)
  obtain ⟨lam, hcR_eq⟩ := exists_row_comb_of_det_ne_zero M1 hM1_det cR
  have hlam_ne : ∃ i0 : Fin m, lam i0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hc0 : cR = 0 := by rw [hcR_eq]; simp [hall]
    have h1 := congrArg (fun f : Fin m → ℝ => f (e.symm p0)) hc0
    simp only [cR, e.apply_symm_apply, Pi.zero_apply, Int.cast_eq_zero] at h1
    exact hp0 h1
  obtain ⟨i0, hi0⟩ := hlam_ne
  let MtildeZ : Matrix (Fin m) (Fin m) ℤ := MZ.updateRow i0 (fun j => c (e j))
  let MtildeR : Matrix (Fin m) (Fin m) ℝ := M1.updateRow i0 cR
  have hMtilde_map : MtildeR = MtildeZ.map (Int.castRingHom ℝ) := by
    apply Matrix.ext; intro i j
    by_cases hi : i = i0
    · subst hi; simp [MtildeR, MtildeZ, cR]
    · simp [MtildeR, MtildeZ, hi, hM1_map]
  have hMtilde_det_ne : MtildeR.det ≠ 0 := by
    have hdet : MtildeR.det = lam i0 * M1.det := by
      dsimp [MtildeR]
      rw [hcR_eq, Matrix.det_updateRow_sum, smul_eq_mul]
    rw [hdet]
    exact mul_ne_zero hi0 hM1_det
  have hdet_ge_one : (1 : ℝ) ≤ |MtildeR.det| := by
    have hmap : MtildeR.det = (MtildeZ.det : ℝ) := by
      rw [hMtilde_map]
      exact (RingHom.map_det (Int.castRingHom ℝ) MtildeZ).symm
    rw [hmap]
    have hZne : MtildeZ.det ≠ 0 := by
      intro h0; apply hMtilde_det_ne; rw [hmap, h0, Int.cast_zero]
    have h1 : (1 : ℤ) ≤ |MtildeZ.det| := Int.one_le_abs hZne
    exact_mod_cast h1
  -- Column operation on column `j0 = e.symm p0` using `fVal`
  let j0 : Fin m := e.symm p0
  let Mcol : Matrix (Fin m) (Fin m) ℝ :=
    MtildeR.updateCol j0 (fun i => ∑ j : Fin m, fVal (e j) • MtildeR i j)
  have hMcol_det : Mcol.det = fVal p0 * MtildeR.det := by
    have h1 := Matrix.det_updateCol_sum MtildeR j0 (fun j => fVal (e j))
    simpa [Mcol, j0, e.apply_symm_apply, smul_eq_mul] using h1
  have hMcol_i0_j0 : Mcol i0 j0 = 0 := by
    simp only [Mcol, Matrix.updateCol_self, smul_eq_mul, MtildeR, Matrix.updateRow_self, cR]
    calc ∑ j : Fin m, fVal (e j) * (c (e j) : ℝ)
        = ∑ p : Idx n, (c p : ℝ) * fVal p := by
          rw [← Equiv.sum_comp e (fun p => (c p : ℝ) * fVal p)]
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := hrel
  -- Bounds on polynomial entries and remainder entries
  let H : ℕ := C4 ^ N
  have hnorm0 : ∀ p : Idx n, polyNorm (vR P0 0 p) ≤ ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ) := by
    intro p
    rw [vR, vZ]
    have hmapP0 : (P0 p).map (Int.castRingHom ℝ) =
        ∑ l : Fin (N + 1),
          Polynomial.C (((N.factorial / l.1.factorial : ℕ) : ℝ) * (ptilde (p, l) : ℝ)) *
            Polynomial.X ^ l.1 := by
      simp only [P0, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast]
    rw [hmapP0]
    refine (polyNorm_sum_le _ _).trans ?_
    calc ∑ l : Fin (N + 1),
            polyNorm (Polynomial.C (((N.factorial / l.1.factorial : ℕ) : ℝ) * (ptilde (p, l) : ℝ)) *
              Polynomial.X ^ l.1)
        ≤ ∑ _l : Fin (N + 1), (N.factorial : ℝ) * (H : ℝ) := by
          refine Finset.sum_le_sum fun l _ => ?_
          have hdeg_term : (Polynomial.C (((N.factorial / l.1.factorial : ℕ) : ℝ) *
              (ptilde (p, l) : ℝ)) * Polynomial.X ^ l.1).natDegree ≤ l.1 :=
            Polynomial.natDegree_C_mul_X_pow_le _ _
          rw [polyNorm_eq_sum_of_le _ hdeg_term]
          simp only [Polynomial.coeff_C_mul_X_pow]
          rw [Finset.sum_eq_single l.1]
          · simp only [↓reduceIte, abs_mul]
            rw [abs_of_nonneg (a := ((N.factorial / l.1.factorial : ℕ) : ℝ)) (Nat.cast_nonneg _)]
            have hdiv_le : ((N.factorial / l.1.factorial : ℕ) : ℝ) ≤ (N.factorial : ℝ) := by
              exact_mod_cast Nat.div_le_self N.factorial l.1.factorial
            have hbd_le : |(ptilde (p, l) : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hptilde_bd (p, l)
            exact mul_le_mul hdiv_le hbd_le (abs_nonneg _) (Nat.cast_nonneg _)
          · intro r _ hrl; simp [hrl]
          · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
      _ = ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ) := by simp [mul_assoc]
  let Pbound : ℝ :=
    ((2 * N : ℕ) : ℝ) ^ (m + t) * ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ)
  have hB0_nn : 0 ≤ ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hPbound_pos : 0 ≤ Pbound :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hbase_le_2N : ∀ i : Fin m, N + k i + m * (3 * n + 1) ≤ 2 * N := by
    intro i
    have hki : k i < m + t := hk_lt i
    have hδ_le : δ ≤ N0 := by
      have h1 : δ ≤ N / 4 := by
        dsimp [δ]; exact Nat.div_le_div_left (by omega : 4 ≤ 4 * m) (by norm_num)
      have h2 : N / 4 = N0 := by dsimp [N]; omega
      omega
    have hm8 : 8 * m * (3 * n + 1) = 8 * (m * (3 * n + 1)) := by ring
    have hN_eq4 : N = 4 * N0 := rfl
    omega
  have hMcol_poly_bd : ∀ (i j : Fin m), i ≠ i0 → j ≠ j0 → |Mcol i j| ≤ Pbound := by
    intro i j hi hj
    have hentry : Mcol i j = (vR P0 (k i) (e j)).eval 1 := by
      dsimp only [Mcol]
      rw [Matrix.updateCol_ne hj]
      dsimp only [MtildeR]
      rw [Matrix.updateRow_ne hi]
      rfl
    rw [hentry]
    refine (abs_eval_one_le_polyNorm _).trans ?_
    refine (polyNorm_vR_le P0 hB0_nn hdeg0 hnorm0 (k i) (e j)).trans ?_
    have h1 : (((N + k i + m * (3 * n + 1) : ℕ) : ℝ)) ^ (k i) ≤ ((2 * N : ℕ) : ℝ) ^ (m + t) := by
      have ha : ((N + k i + m * (3 * n + 1) : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
        exact_mod_cast hbase_le_2N i
      have hb : ((2 * N : ℕ) : ℝ) ^ (k i) ≤ ((2 * N : ℕ) : ℝ) ^ (m + t) :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * N by omega)) (hk_lt i).le
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) ha (k i)).trans hb
    calc (((N + k i + m * (3 * n + 1) : ℕ) : ℝ)) ^ (k i) *
            (((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ))
        ≤ ((2 * N : ℕ) : ℝ) ^ (m + t) * (((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) * (H : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hB0_nn
      _ = Pbound := by dsimp [Pbound]; ring
  let K : ℕ := M - (m + t)
  have h2mt_le_M : 2 * (m + t) ≤ M := by
    have hδ_le : δ ≤ N0 := by
      have h1 : δ ≤ N / 4 := by
        dsimp [δ]; exact Nat.div_le_div_left (by omega : 4 ≤ 4 * m) (by norm_num)
      have h2 : N / 4 = N0 := by dsimp [N]; omega
      omega
    have hmN : 2 * N ≤ m * (N + 1) := by nlinarith
    have hN_eq4 : N = 4 * N0 := rfl
    dsimp [M]; omega
  let Rbound : ℝ :=
    (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (m + t) * A ^ M *
      Real.exp A / (K.factorial : ℝ)
  have hA_nn : (0 : ℝ) ≤ A := zero_le_one.trans hA_ge1
  have hRbound_pos : 0 ≤ Rbound := by
    dsimp [Rbound]
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (pow_nonneg (by norm_num) _))
      (pow_nonneg hA_nn _)) (Real.exp_pos A).le
  have hMcol_rem_bd : ∀ i : Fin m, i ≠ i0 → |Mcol i j0| ≤ Rbound := by
    intro i hi
    have hcol_eq : Mcol i j0 = ∑ p : Idx n, (vR P0 (k i) p).eval 1 * fVal p := by
      have h1 : Mcol i j0 = ∑ j : Fin m, fVal (e j) * MtildeR i j := by
        dsimp only [Mcol]
        rw [Matrix.updateCol_self]
        rfl
      rw [h1, ← Equiv.sum_comp e (fun p => (vR P0 (k i) p).eval 1 * fVal p)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 : MtildeR i j = (vR P0 (k i) (e j)).eval 1 := by
        dsimp only [MtildeR]; rw [Matrix.updateRow_ne hi]; rfl
      rw [h2, mul_comm]
    rw [hcol_eq]
    have hki_lt : k i < m + t := hk_lt i
    have h2ki : 2 * k i ≤ M := by omega
    have hbd_ki := abs_sum_Rseq_le (M := M) (H := H) (k := k i) ptilde hptilde_bd hvan h2ki
    refine hbd_ki.trans ?_
    have hpow2 : (2 : ℝ) ^ (k i) ≤ (2 : ℝ) ^ (m + t) :=
      pow_le_pow_right₀ (by norm_num) hki_lt.le
    have hfac_le : (K.factorial : ℝ) ≤ ((M - k i).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (show K ≤ M - k i by dsimp [K]; omega)
    have hnum_le : (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (k i) * A ^ M * Real.exp A ≤
        (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (m + t) * A ^ M * Real.exp A := by
      have ha : 0 ≤ (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hb : 0 ≤ A ^ M * Real.exp A := mul_nonneg (pow_nonneg hA_nn _) (Real.exp_pos A).le
      calc (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (k i) * A ^ M * Real.exp A
          = ((m : ℝ) * (N.factorial : ℝ) * (H : ℝ)) * (2 : ℝ) ^ (k i) * (A ^ M * Real.exp A) := by ring
        _ ≤ ((m : ℝ) * (N.factorial : ℝ) * (H : ℝ)) * (2 : ℝ) ^ (m + t) * (A ^ M * Real.exp A) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow2 ha) hb
        _ = _ := by ring
    have hnum_nn : 0 ≤ (m : ℝ) * (N.factorial : ℝ) * (H : ℝ) * (2 : ℝ) ^ (m + t) * A ^ M * Real.exp A :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (pow_nonneg (by norm_num) _))
        (pow_nonneg hA_nn _)) (Real.exp_pos A).le
    have hKf_pos : (0 : ℝ) < (K.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos K
    exact div_le_div₀ hnum_nn hnum_le hKf_pos hfac_le
  have hMcol_i0_bd : ∀ j : Fin m, |Mcol i0 j| ≤ Cc := by
    intro j
    by_cases hj : j = j0
    · rw [hj, hMcol_i0_j0, abs_zero]; exact hCc_pos.le
    · simp only [Mcol, Matrix.updateCol_ne hj, MtildeR, Matrix.updateRow_self, cR]
      have h1 : |(c (e j) : ℝ)| ≤ ∑ p : Idx n, |(c p : ℝ)| :=
        Finset.single_le_sum (f := fun p : Idx n => |(c p : ℝ)|) (fun p _ => abs_nonneg _) (Finset.mem_univ (e j))
      dsimp [Cc]; linarith
  -- Bound `|Mcol.det|` via Leibniz expansion
  have hdet_upper : |Mcol.det| ≤ (m.factorial : ℝ) * Cc * Rbound * Pbound ^ (m - 2) :=
    det_abs_le_of_row_col_bounds Mcol i0 j0 Cc Rbound Pbound hCc_pos.le hRbound_pos hPbound_pos
      hMcol_i0_j0 hMcol_i0_bd hMcol_rem_bd hMcol_poly_bd
  -- Final pure-`ℕ`-power asymptotic comparison: `fVal p0 ≤ |Mcol.det| < fVal p0`!
  have hlower : fVal p0 ≤ |Mcol.det| := by
    rw [hMcol_det, abs_mul, abs_of_pos (fVal_pos p0)]
    calc fVal p0 = fVal p0 * 1 := (mul_one _).symm
      _ ≤ fVal p0 * |MtildeR.det| := mul_le_mul_of_nonneg_left hdet_ge_one (fVal_pos p0).le
  exact rivoal_asymptotic_contradiction m C4 N0 t A Cc (fVal p0) |Mcol.det|
    hm2 hC4_pos hA_ge1 hCc_pos (fVal_pos p0) (by omega) hN0_2 hN0_3 ht_bound hlower hdet_upper

end OMA_Rivoal_2012

theorem OMA.solution :
    type_of% @Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hγ : IsAlgebraic ℚ Real.eulerMascheroniConstant := by
    unfold Transcendental at h1
    push Not at h1
    exact h1
  have hδ : IsAlgebraic ℚ gompertzConstant := by
    unfold Transcendental at h2
    push Not at h2
    exact h2
  exact OMA_Rivoal_2012.not_both_algebraic hγ hδ
