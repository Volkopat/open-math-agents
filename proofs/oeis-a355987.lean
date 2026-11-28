import OMAStatements.S_oeis_a355987
import Mathlib

open Filter Finset Topology Asymptotics OMA.S_oeis_a355987
open scoped Nat
namespace A355987Count

private noncomputable def block (n k : ℕ) : ℝ :=
  (((n / (k+1) : ℕ) : ℝ) - (n / (k+2) : ℕ)) / n / ((k+1)! : ℝ)

lemma fiber (n k : ℕ) : (Finset.Icc 1 n).filter (fun j => n/j = k+1) =
    Finset.Ioc (n/(k+2)) (n/(k+1)) := by
  ext j
  simp only [mem_filter, mem_Icc, mem_Ioc]
  by_cases hj : 0 < j
  · have hlow : k+1 ≤ n/j ↔ j ≤ n/(k+1) := by
      rw [Nat.le_div_iff_mul_le hj, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    have hupp : n/j < k+2 ↔ n/(k+2) < j := by
      rw [Nat.div_lt_iff_lt_mul hj, Nat.div_lt_iff_lt_mul (by omega), Nat.mul_comm]
    have := Nat.div_le_self n (k+1)
    omega
  · have : j = 0 := by omega
    simp [this]

private lemma group_sum (n : ℕ) : (∑ j ∈ Finset.Icc 1 n, 1 / ((n/j)! : ℝ)) / n =
    ∑' k, block n k := by
  classical
  have hp {j : ℕ} (hj : j ∈ Finset.Icc 1 n) : 0 < n/j :=
    Nat.div_pos (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hj).1
  rw [tsum_eq_sum (s := range n) (fun k hk => by
    have h := Nat.le_of_not_gt (fun h => hk (mem_range.mpr h))
    simp [block, Nat.div_eq_of_lt (show n < k+1 by omega),
      Nat.div_eq_of_lt (show n < k+2 by omega)])]
  have hm : ∀ j ∈ Finset.Icc 1 n, n/j-1 ∈ range n := by
    intro j hj
    have := hp hj
    have := Nat.div_le_self n j
    exact mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun j => n/j-1) hm, Finset.sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hfilter : (Finset.Icc 1 n).filter (fun j => n/j-1=k) =
      (Finset.Icc 1 n).filter (fun j => n/j=k+1) := by
    apply Finset.filter_congr
    intro j hj
    have := hp hj
    omega
  rw [hfilter]
  have hc : ∀ j ∈ (Finset.Icc 1 n).filter (fun j => n/j=k+1),
      (1 / ((n/j)! : ℝ)) = 1/((k+1)! : ℝ) := fun j hj => by rw [(mem_filter.mp hj).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, fiber, Nat.card_Ioc, nsmul_eq_mul,
    Nat.cast_sub (Nat.div_le_div_left (by omega : k+1 ≤ k+2) (by omega))]
  unfold block
  ring

private lemma div_limit (q : ℕ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => ((n/q : ℕ) : ℝ) / n) atTop (𝓝 (1/(q : ℝ))) := by
  have hq' : (0 : ℝ) < q := by positivity
  have herr : Tendsto (fun n : ℕ => ((n%q : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) (fun n => div_le_div_of_nonneg_right
      (show ((n%q : ℕ) : ℝ) ≤ q by exact_mod_cast (Nat.mod_lt n hq).le) (by positivity))
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub herr
  have hh := h.div_const (q : ℝ)
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have he : ((n%q : ℕ) : ℝ) + q * ((n/q : ℕ) : ℝ) = n := by exact_mod_cast Nat.mod_add_div n q
  field_simp
  nlinarith

private lemma limit_sum : Tendsto (fun n : ℕ => (∑ j ∈ Finset.Icc 1 n,
    1 / ((n/j)! : ℝ)) / n) atTop (𝓝 S) := by
  simp_rw [group_sum]
  apply tendsto_tsum_of_dominated_convergence (bound := fun k : ℕ => 1/((k+1)! : ℝ))
  · simpa [Function.comp_def] using (Real.summable_pow_div_factorial (1 : ℝ)).comp_injective Nat.succ_injective
  · intro k
    have h := ((div_limit (k+1) (by omega)).sub (div_limit (k+2) (by omega))).div_const ((k+1)! : ℝ)
    convert h using 1
    · ext n
      simp [block, sub_div]
    · congr 1
      rw [Nat.factorial_succ (k+1)]
      push_cast
      field_simp
      ring
  · apply Eventually.of_forall
    intro n k
    have h1 : ((n/(k+2) : ℕ) : ℝ) ≤ (n/(k+1) : ℕ) := by
      exact_mod_cast Nat.div_le_div_left (by omega : k+1 ≤ k+2) (by omega)
    have h2 : ((n/(k+1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n (k+1)
    simp only [block, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
      (((n/(k+1) : ℕ) : ℝ) - (n/(k+2) : ℕ)) / n / ((k+1)! : ℝ))]
    apply div_le_div_of_nonneg_right _ (by positivity)
    by_cases hn : n = 0
    · simp [hn]
    · apply (div_le_one (by positivity)).mpr
      linarith [show (0 : ℝ) ≤ (n/(k+2) : ℕ) by positivity]

lemma equiv : (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => S * (n ! : ℝ) * (n : ℝ)) := by
  have hs : 0 < S := by
    apply Summable.tsum_pos (i := 0) _ (fun _ => by positivity) (by positivity)
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (f := fun k : ℕ => 1/((k+2)! : ℝ))
    · intro k
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have h : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith [show 0 ≤ ((k+2)! : ℝ) by positivity]
    · simpa [Function.comp_def] using ((Real.summable_pow_div_factorial (1 : ℝ)).comp_injective
        (show Function.Injective (fun k : ℕ => k+2) by intro x y h; exact Nat.add_right_cancel h))
  rw [isEquivalent_iff_tendsto_one]
  · have h := limit_sum.div_const S
    rw [div_self hs.ne'] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [a]
    field_simp
  · filter_upwards [eventually_ge_atTop 1] with n hn
    positivity

end A355987Count

/- The integral representation of Euler’s constant through Ein is adapted from @ppleskov’s merged proof of Rivoal’s theorem (ffb193d32). -/
open scoped BigOperators Topology Nat
open Filter MeasureTheory Set Real Polynomial Matrix

namespace A355987PV

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


open OMA.S_oeis_a355987
private noncomputable def reg (t : ℝ) := dslope Real.exp 0 t

private lemma reg_cont : Continuous reg := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope (Filter.univ_mem : (Set.univ : Set ℝ) ∈ 𝓝 0)).mpr
    ⟨Real.continuous_exp.continuousOn, Real.differentiableAt_exp⟩

private lemma reg_val {t : ℝ} (ht : t ≠ 0) : reg t = (Real.exp t - 1) / t := by
  simp [reg, dslope_of_ne _ ht, slope_def_module, div_eq_inv_mul]

private noncomputable def avg (k : ℕ) : ℝ :=
  1 / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))

private lemma avg_summable : Summable avg := by
  refine Summable.of_nonneg_of_le (fun _ => by unfold avg; positivity) (f := fun k : ℕ => 1/((k+1)! : ℝ)) ?_ ?_
  · intro k
    unfold avg
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    nlinarith [show 0 ≤ ((k+1)! : ℝ) by positivity]
  · simpa [Function.comp_def] using (Real.summable_pow_div_factorial (1 : ℝ)).comp_injective Nat.succ_injective

private lemma reg_series {t : ℝ} (ht : t ≠ 0) :
    reg t = ∑' k : ℕ, t^k / ((k+1)! : ℝ) := by
  have h := (Real.summable_pow_div_factorial t).tsum_eq_zero_add
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  rw [reg_val ht, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  dsimp only
  rw [h, add_sub_cancel_left,
    ← tsum_div_const]
  apply tsum_congr
  intro k
  rw [pow_succ]
  field_simp

private lemma integral_reg : (∫ t in (0 : ℝ)..1, reg t) = ∑' k, avg k := by
  have hm (k : ℕ) : IntegrableOn (fun t : ℝ => t^k / ((k+1)! : ℝ)) (Set.Ioc 0 1) := by
    exact (show Continuous (fun t : ℝ => t^k / ((k+1)! : ℝ)) by fun_prop).integrableOn_Ioc
  have hb : Summable (fun k : ℕ => ∫ t in Set.Ioc (0 : ℝ) 1, ‖t^k / ((k+1)! : ℝ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (f := fun k : ℕ => 1/((k+1)! : ℝ))
    · intro k
      calc _ ≤ ∫ _t in Set.Ioc (0 : ℝ) 1, 1 / ((k+1)! : ℝ) := by
              apply setIntegral_mono_on (hm k).norm (integrableOn_const (by simp)) measurableSet_Ioc
              intro t ht
              rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg ht.1.le _) (by positivity))]
              exact div_le_div_of_nonneg_right (pow_le_one₀ ht.1.le ht.2) (by positivity)
           _ = _ := by simp
    · simpa [Function.comp_def] using (Real.summable_pow_div_factorial (1 : ℝ)).comp_injective Nat.succ_injective
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∑' k : ℕ, t^k / ((k+1)! : ℝ) :=
          setIntegral_congr_fun measurableSet_Ioc (fun t ht => reg_series ht.1.ne')
       _ = _ := by
          rw [← integral_tsum_of_summable_integral_norm hm hb]
          apply tsum_congr
          intro k
          rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
            intervalIntegral.integral_div, integral_pow]
          simp [avg, div_eq_mul_inv, mul_comm]

private noncomputable def both (t : ℝ) := reg t + reg (-t)
private noncomputable def tail := ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t)/t
private noncomputable def pv := (∫ t in (0 : ℝ)..1, both t) - tail

private lemma cut_eq {x : ℝ} (hx : 0 < x) (h1 : x ≤ 1) :
    EiOneCut x = (∫ t in x..1, both t) - tail := by
  have hi (a : ℝ) : IntervalIntegrable (fun t => Real.exp (a*t) / t) volume x 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    exact (hx.trans_le ht.1).ne'
  have hp : IntervalIntegrable (fun t => Real.exp t/t) volume x 1 := by simpa using hi 1
  have hn : IntervalIntegrable (fun t => Real.exp (-t)/t) volume x 1 := by simpa using hi (-1)
  have hb : (∫ t in x..1, both t) = ∫ t in x..1, (Real.exp t/t - Real.exp (-t)/t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    have ht' := (hx.trans_le ht.1).ne'
    rw [both, reg_val ht', reg_val (neg_ne_zero.mpr ht')]
    ring
  have hneg : (∫ t in Set.Iic (-x), Real.exp t/t) = -(∫ t in Set.Ioi x, Real.exp (-t)/t) := by
    rw [← integral_comp_neg_Ioi x (fun t : ℝ => Real.exp t/t)]
    simp only [div_neg, integral_neg]
  rw [EiOneCut, hneg, ← intervalIntegral.integral_interval_add_Ioi' hn integrableOn_exp_neg_div_Ioi,
    hb, intervalIntegral.integral_sub hp hn, tail]
  ring

lemma pv_limit : Tendsto EiOneCut (𝓝[>] 0) (𝓝 pv) := by
  have hc : Continuous both := reg_cont.add (reg_cont.comp continuous_neg)
  have hi := (intervalIntegral.continuous_primitive (μ := volume) (fun a b => hc.intervalIntegrable a b) 1).neg.sub (continuous_const (y := tail))
  have ht := hi.continuousAt (x := 0) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  change Tendsto (fun x : ℝ => -(∫ t in (1 : ℝ)..x, both t) - tail) _ (𝓝 (-(∫ t in (1 : ℝ)..0, both t) - tail)) at ht
  apply Tendsto.congr' _ (show Tendsto (fun x => -(∫ t in (1 : ℝ)..x, both t) - tail)
    (𝓝[>] 0) (𝓝 pv) by simpa [pv, intervalIntegral.integral_symm 1] using ht)
  filter_upwards [self_mem_nhdsWithin, (show Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num)))] with x hx h1
  rw [cut_eq hx (le_of_lt h1), intervalIntegral.integral_symm 1]

lemma pv_eval : S = 2 - Real.exp 1 - Real.eulerMascheroniConstant + pv := by
  have hexp : Summable (fun k : ℕ => 1/((k+2)! : ℝ)) := by
    simpa [Function.comp_def] using (Real.summable_pow_div_factorial (1 : ℝ)).comp_injective
      (show Function.Injective (fun k : ℕ => k+2) by intro i j h; exact Nat.add_right_cancel h)
  have hs : S = (∑' k, avg k) - ∑' k : ℕ, 1/((k+2)! : ℝ) := by
    rw [← avg_summable.tsum_sub hexp]
    apply tsum_congr
    intro k
    simp only [avg, Nat.factorial_succ (k+1), Nat.cast_mul]
    push_cast
    field_simp
    ring
  have he : (∑' k : ℕ, 1/((k+2)! : ℝ)) = Real.exp 1 - 2 := by
    have h1 := (Real.summable_pow_div_factorial (1 : ℝ)).tsum_eq_zero_add
    have h2 := ((Real.summable_pow_div_factorial (1 : ℝ)).comp_injective Nat.succ_injective).tsum_eq_zero_add
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    simp [Function.comp_def] at h1 h2 ⊢
    linarith
  have hn : (∫ t in (0 : ℝ)..1, reg (-t)) = Ein 1 := by
    rw [ein_one_eq_integral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [reg_val (neg_ne_zero.mpr ht.1.ne')]
    ring
  rw [hs, he, pv]
  unfold both
  rw [intervalIntegral.integral_add (reg_cont.intervalIntegrable _ _)
    (show IntervalIntegrable (fun t : ℝ => reg (-t)) volume 0 1 from (reg_cont.comp continuous_neg).intervalIntegrable _ _), hn, integral_reg,
    eulerMascheroni_eq_ein_one_sub_integral, tail]
  ring
end A355987PV


theorem OMA.solution : type_of% @OMA.S_oeis_a355987.main :=
  ⟨A355987Count.equiv, _, A355987PV.pv_limit, A355987PV.pv_eval⟩
