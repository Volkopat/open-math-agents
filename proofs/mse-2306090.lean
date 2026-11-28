import OMAStatements.S_mse_2306090

namespace OMA.P_mse_2306090

open OMA.S_mse_2306090 MeasureTheory Filter Topology

/-! ### Part 1: Euler integral for `₂F₁(1, b; 2 + x; z)` -/

private lemma descPochhammer_smeval_eq_prod (b : ℝ) (n : ℕ) :
    (descPochhammer ℤ n).smeval (b + (n : ℝ) - 1) = ∏ k ∈ Finset.range n, (b + (k : ℝ)) := by
  induction n generalizing b with
  | zero => simp [descPochhammer_zero]
  | succ n ih =>
    rw [descPochhammer_succ_left, Polynomial.smeval_mul, Polynomial.smeval_X]
    have hcomp : ((descPochhammer ℤ n).comp (Polynomial.X - 1)).smeval (b + ((n + 1 : ℕ) : ℝ) - 1) =
        (descPochhammer ℤ n).smeval (b + (n : ℝ) - 1) := by
      rw [Polynomial.smeval_comp]
      simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_one]
      congr 1; push_cast; ring
    rw [hcomp, ih b, Finset.prod_range_succ]
    have : b + ((n + 1 : ℕ) : ℝ) - 1 = b + (n : ℝ) := by push_cast; ring
    rw [this, pow_one, mul_comm]

private lemma ring_choose_eq_prod_div_fact (b : ℝ) (n : ℕ) :
    Ring.choose (b + (n : ℝ) - 1) n =
      (∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_prod, smul_eq_mul, div_eq_inv_mul]

private lemma hasSum_one_sub_rpow_neg (b y : ℝ) (hy : |y| < 1) :
    HasSum (fun n : ℕ => ((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * y ^ n)
      ((1 - y) ^ (-b)) := by
  have hfps := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero b
  have hy_ball : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_lt_one.mpr hy
  have hsum := hfps.hasSum hy_ball
  have h1y : 0 < 1 - y := by linarith [(abs_lt.mp hy).2]
  have hrpow : 1 / (1 - y) ^ b = (1 - y) ^ (-b) := by
    rw [Real.rpow_neg (le_of_lt h1y), one_div]
  rw [zero_add, hrpow] at hsum
  refine hsum.congr_fun (fun n => ?_)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, ring_choose_eq_prod_div_fact]

private lemma summable_norm_poch_div_fact (b z : ℝ) (hz : |z| < 1) :
    Summable (fun n : ℕ => |((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * z ^ n|) := by
  set r : ℝ := (|z| + 1) / 2
  have hr_pos : 0 < r := by simp only [r]; linarith [abs_nonneg z]
  have hzr : |z| < r := by simp only [r]; linarith
  have hr1 : |r| < 1 := by rw [abs_of_pos hr_pos]; simp only [r]; linarith
  have hs_r := (hasSum_one_sub_rpow_neg b r hr1).summable
  have ht0 : Tendsto (fun n : ℕ => ((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * r ^ n)
      atTop (nhds 0) := hs_r.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht0) 1 one_pos
  have hratio_lt : |z| / r < 1 := (div_lt_one hr_pos).mpr hzr
  have hgeom : Summable (fun n : ℕ => (|z| / r) ^ n) :=
    summable_geometric_of_lt_one (div_nonneg (abs_nonneg z) (le_of_lt hr_pos)) hratio_lt
  apply Summable.of_norm_bounded_eventually (g := fun n : ℕ => (|z| / r) ^ n) hgeom
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbd : |((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * r ^ n| < 1 := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    exact h
  rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_pow]
  rw [abs_mul, abs_pow, abs_of_pos hr_pos] at hbd
  have hrne : r ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hr_pos)
  calc |(∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)| * |z| ^ n
      = (|(∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)| * r ^ n) * (|z| / r) ^ n := by
        rw [show (|z| / r) ^ n = |z| ^ n / r ^ n from div_pow |z| r n, mul_assoc,
            mul_div_cancel₀ _ hrne]
    _ ≤ 1 * (|z| / r) ^ n := mul_le_mul_of_nonneg_right (le_of_lt hbd) (by positivity)
    _ = (|z| / r) ^ n := one_mul _

private lemma integral_one_sub_rpow_mul_pow (n : ℕ) :
    ∀ x : ℝ, 0 < x →
      ∫ t in (0 : ℝ)..1, (1 - t) ^ x * t ^ n =
        (n.factorial : ℝ) / ((x + 1) * ∏ k ∈ Finset.range n, (2 + x + (k : ℝ))) := by
  induction n with
  | zero =>
    intro x hx
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Finset.prod_range_zero, mul_one]
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => -((1 - u) ^ (x + 1)) / (x + 1)) ((1 - t) ^ x) t := by
      intro t ht
      have h1t : 0 < 1 - t := by linarith [ht.2]
      have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      have h2 := h1.rpow_const (Or.inl (ne_of_gt h1t)) (p := x + 1)
      have h3 := h2.neg.div_const (x + 1)
      have hx1 : x + 1 ≠ 0 := by linarith
      have hderiv_eq : -(-1 * (x + 1) * (1 - t) ^ (x + 1 - 1)) / (x + 1) = (1 - t) ^ x := by
        rw [add_sub_cancel_right]; field_simp
      rw [← hderiv_eq]
      exact h3
    have hcont : ContinuousOn (fun u : ℝ => -((1 - u) ^ (x + 1)) / (x + 1)) (Set.Icc 0 1) := by
      have hc : ContinuousOn (fun u : ℝ => (1 - u) ^ (x + 1)) (Set.Icc 0 1) :=
        ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun _ _ => Or.inr (by linarith))
      exact hc.neg.div_const _
    have hint : IntervalIntegrable (fun t : ℝ => (1 - t) ^ x) volume 0 1 :=
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (le_of_lt hx))).intervalIntegrable_of_Icc (by norm_num)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint]
    rw [sub_self, Real.zero_rpow (by linarith), sub_zero, Real.one_rpow]
    ring
  | succ n ih =>
    intro x hx
    have hx1 : 0 < x + 1 := by linarith
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => -((1 - u) ^ (x + 1)) * u ^ (n + 1))
          ((x + 1) * ((1 - t) ^ x * t ^ (n + 1)) - ((n + 1 : ℕ) : ℝ) * ((1 - t) ^ (x + 1) * t ^ n)) t := by
      intro t ht
      have h1t : 0 < 1 - t := by linarith [ht.2]
      have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      have h2 : HasDerivAt (fun u : ℝ => -((1 - u) ^ (x + 1))) ((x + 1) * (1 - t) ^ x) t := by
        have h2' := (h1.rpow_const (Or.inl (ne_of_gt h1t)) (p := x + 1)).neg
        have hderiv_eq : -(-1 * (x + 1) * (1 - t) ^ (x + 1 - 1)) = (x + 1) * (1 - t) ^ x := by
          rw [add_sub_cancel_right]; ring
        rw [← hderiv_eq]
        exact h2'
      have h3 : HasDerivAt (fun u : ℝ => u ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * t ^ n) t := by
        simpa using hasDerivAt_pow (n + 1) t
      have h4 := h2.mul h3
      have hfun : (fun u : ℝ => -((1 - u) ^ (x + 1)) * u ^ (n + 1)) =
          (fun u : ℝ => (-((1 - u) ^ (x + 1))) * u ^ (n + 1)) := by
        ext u; ring
      have hdeq : ((x + 1) * (1 - t) ^ x) * t ^ (n + 1) +
          (-((1 - t) ^ (x + 1))) * (((n + 1 : ℕ) : ℝ) * t ^ n) =
          (x + 1) * ((1 - t) ^ x * t ^ (n + 1)) -
          ((n + 1 : ℕ) : ℝ) * ((1 - t) ^ (x + 1) * t ^ n) := by ring
      rw [hfun, ← hdeq]
      exact h4
    have hcont : ContinuousOn (fun u : ℝ => -((1 - u) ^ (x + 1)) * u ^ (n + 1)) (Set.Icc 0 1) := by
      have hc : ContinuousOn (fun u : ℝ => (1 - u) ^ (x + 1)) (Set.Icc 0 1) :=
        ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun _ _ => Or.inr (by linarith))
      exact hc.neg.mul (continuousOn_pow _)
    have hint1 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ x * t ^ (n + 1)) volume 0 1 :=
      ((ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (le_of_lt hx))).mul (continuousOn_pow _)).intervalIntegrable_of_Icc (by norm_num)
    have hint2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (x + 1) * t ^ n) volume 0 1 :=
      ((ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (le_of_lt hx1))).mul (continuousOn_pow _)).intervalIntegrable_of_Icc (by norm_num)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv
      ((hint1.const_mul (x + 1)).sub (hint2.const_mul ((n + 1 : ℕ) : ℝ)))
    rw [sub_self, Real.zero_rpow (by linarith), zero_pow (Nat.succ_ne_zero n)] at hftc
    simp only [neg_zero, zero_mul, mul_zero, sub_self] at hftc
    rw [intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    have hih := ih (x + 1) hx1
    have hprod_eq : (x + 1 + 1) * ∏ k ∈ Finset.range n, (2 + (x + 1) + (k : ℝ)) =
        ∏ k ∈ Finset.range (n + 1), (2 + x + (k : ℝ)) := by
      conv_rhs => rw [Finset.prod_range_succ', mul_comm]
      simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
      congr 1
      · ring
      · apply Finset.prod_congr rfl
        intro k _; ring
    rw [hih, hprod_eq] at hftc
    have hx1ne : x + 1 ≠ 0 := by linarith
    have hprodne : (∏ k ∈ Finset.range (n + 1), (2 + x + (k : ℝ))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hstep : (x + 1) * (∫ t in (0 : ℝ)..1, (1 - t) ^ x * t ^ (n + 1)) =
        ((n + 1 : ℕ) : ℝ) * ((n.factorial : ℝ) / ∏ k ∈ Finset.range (n + 1), (2 + x + (k : ℝ))) := by
      linarith
    have hdiv := congrArg (fun v => v / (x + 1)) hstep
    rw [mul_div_cancel_left₀ _ hx1ne] at hdiv
    rw [hdiv]
    field_simp

private lemma hyp2F1_1_eq_euler_integral (b x z : ℝ) (hx : 0 < x) (hz : |z| < 1) :
    hyp2F1_1 b (2 + x) z =
      (x + 1) * ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - z * t) ^ (-b) := by
  let f : ℕ → ℝ → ℝ := fun n t =>
    (1 - t) ^ x * (((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * (z * t) ^ n)
  have hsum_pt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      HasSum (fun n => f n t) ((1 - t) ^ x * (1 - z * t) ^ (-b)) := by
    intro t ht
    have hzt : |z * t| < 1 := by
      rw [abs_mul, abs_of_pos ht.1]
      calc |z| * t ≤ |z| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg z)
        _ = |z| := mul_one _
        _ < 1 := hz
    exact (hasSum_one_sub_rpow_neg b (z * t) hzt).mul_left ((1 - t) ^ x)
  have hf_int : ∀ n : ℕ, IntegrableOn (f n) (Set.Ioc (0 : ℝ) 1) volume := by
    intro n
    have hc : ContinuousOn (f n) (Set.Icc 0 1) := by
      refine (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (le_of_lt hx))).mul ?_
      exact continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).pow n)
    exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  let M : ℕ → ℝ := fun n =>
    |((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * z ^ n|
  have hM_sum : Summable M := summable_norm_poch_div_fact b z hz
  have hf_le_M : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ‖f n t‖ ≤ M n := by
    intro n t ht
    simp only [f, M, Real.norm_eq_abs, mul_pow, abs_mul, abs_pow]
    have h1t : |(1 - t) ^ x| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [ht.2]) x)]
      exact Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) (le_of_lt hx)
    have htn : |t| ^ n ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact pow_le_one₀ ht.1 ht.2
    have h0 : 0 ≤ |(∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)| * |z| ^ n := by positivity
    calc |(1 - t) ^ x| * (|(∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)| * (|z| ^ n * |t| ^ n))
        ≤ 1 * (|(∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)| * (|z| ^ n * 1)) := by
          gcongr
      _ = |(∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)| * |z| ^ n := by ring
  have hF_int : IntervalIntegrable (fun t : ℝ => (1 - t) ^ x * (1 - z * t) ^ (-b)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ?_
    refine (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      (fun _ _ => Or.inr (le_of_lt hx))).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
    intro t ht
    left
    have hzt : |z * t| < 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      calc |z| * t ≤ |z| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg z)
        _ = |z| := mul_one _
        _ < 1 := hz
    linarith [(abs_lt.mp hzt).2]
  have hf_int' : ∀ n : ℕ, IntervalIntegrable (f n) volume 0 1 := fun n =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf_int n)
  have hterm_int : ∀ n : ℕ,
      (x + 1) * (∫ t in (0 : ℝ)..1, f n t) =
        (∏ k ∈ Finset.range n, (b + (k : ℝ)) / (2 + x + (k : ℝ))) * z ^ n := by
    intro n
    have hfac : ∀ t : ℝ, f n t =
        (((∏ k ∈ Finset.range n, (b + (k : ℝ))) / (n.factorial : ℝ)) * z ^ n) * ((1 - t) ^ x * t ^ n) := by
      intro t; simp only [f, mul_pow]; ring
    simp_rw [hfac]
    rw [intervalIntegral.integral_const_mul, integral_one_sub_rpow_mul_pow n x hx]
    have hx1 : x + 1 ≠ 0 := by linarith
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [Finset.prod_div_distrib]
    field_simp
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1, f n t)
      atTop (nhds (∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - z * t) ^ (-b))) := by
    have htail_zero : Tendsto (fun N : ℕ => (∑' n : ℕ, M n) - ∑ n ∈ Finset.range N, M n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := ∑' n : ℕ, M n)).sub hM_sum.hasSum.tendsto_sum_nat
    rw [Metric.tendsto_atTop] at htail_zero ⊢
    intro ε hε
    obtain ⟨N0, hN0⟩ := htail_zero ε hε
    refine ⟨N0, fun N hN => ?_⟩
    have hsum_int : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, f n t) volume 0 1 := by
      clear hN
      induction N with
      | zero => simp
      | succ k ih => simpa [Finset.sum_range_succ] using ih.add (hf_int' k)
    rw [dist_eq_norm, ← intervalIntegral.integral_finsetSum (fun n _ => hf_int' n),
        ← intervalIntegral.integral_sub hsum_int hF_int]
    have htail_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖(∑ n ∈ Finset.range N, f n t) - (1 - t) ^ x * (1 - z * t) ^ (-b)‖ ≤
          (∑' n : ℕ, M n) - ∑ n ∈ Finset.range N, M n := by
      intro t ht
      have hzt : |z * t| < 1 := by
        rw [abs_mul, abs_of_nonneg ht.1]
        calc |z| * t ≤ |z| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg z)
          _ = |z| := mul_one _
          _ < 1 := hz
      have hsum_t : HasSum (fun n => f n t) ((1 - t) ^ x * (1 - z * t) ^ (-b)) :=
        (hasSum_one_sub_rpow_neg b (z * t) hzt).mul_left ((1 - t) ^ x)
      have htsum_t : (1 - t) ^ x * (1 - z * t) ^ (-b) = ∑' n : ℕ, f n t := hsum_t.tsum_eq.symm
      rw [htsum_t, norm_sub_rev]
      have hsplit_f : (∑' n : ℕ, f n t) - ∑ n ∈ Finset.range N, f n t = ∑' k : ℕ, f (k + N) t := by
        rw [← hsum_t.summable.sum_add_tsum_nat_add N]; ring
      have hsplit_M : (∑' n : ℕ, M n) - ∑ n ∈ Finset.range N, M n = ∑' k : ℕ, M (k + N) := by
        rw [← hM_sum.sum_add_tsum_nat_add N]; ring
      rw [hsplit_f, hsplit_M]
      have hs_fN : Summable (fun k : ℕ => f (k + N) t) := (summable_nat_add_iff N).mpr hsum_t.summable
      have hs_MN : Summable (fun k : ℕ => M (k + N)) := (summable_nat_add_iff N).mpr hM_sum
      calc ‖∑' k : ℕ, f (k + N) t‖
          ≤ ∑' k : ℕ, ‖f (k + N) t‖ := norm_tsum_le_tsum_norm hs_fN.norm
        _ ≤ ∑' k : ℕ, M (k + N) :=
            Summable.tsum_le_tsum (fun k => hf_le_M (k + N) t ht) hs_fN.norm hs_MN
    have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := (∑' n : ℕ, M n) - ∑ n ∈ Finset.range N, M n) (fun t ht => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact htail_eq t (Set.Ioc_subset_Icc_self ht))
    simp only [sub_zero, abs_one, mul_one] at hint_le
    have htail_lt := hN0 N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
      rw [show (∑' n : ℕ, M n) - ∑ n ∈ Finset.range N, M n = ∑' k : ℕ, M (k + N) by
        rw [← hM_sum.sum_add_tsum_nat_add N]; ring]
      exact tsum_nonneg (fun k => abs_nonneg _))] at htail_lt
    linarith
  have hsum_hyp : HasSum (fun n : ℕ => (∏ k ∈ Finset.range n, (b + (k : ℝ)) / (2 + x + (k : ℝ))) * z ^ n)
      ((x + 1) * ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - z * t) ^ (-b)) := by
    have hmul : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (x + 1) * (∫ t in (0 : ℝ)..1, f n t))
        atTop (nhds ((x + 1) * ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - z * t) ^ (-b))) := by
      simpa only [← Finset.mul_sum] using htend.const_mul (x + 1)
    simp_rw [hterm_int] at hmul
    -- Summability of the 2F1 series from hM_sum!
    have hs_hyp : Summable (fun n : ℕ => (∏ k ∈ Finset.range n, (b + (k : ℝ)) / (2 + x + (k : ℝ))) * z ^ n) := by
      refine Summable.of_norm_bounded (g := fun n => (x + 1) * M n) (hM_sum.mul_left _) (fun n => ?_)
      rw [← hterm_int n, norm_mul, Real.norm_of_nonneg (by linarith : 0 ≤ x + 1)]
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := M n) (fun t ht => by
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
          exact hf_le_M n t (Set.Ioc_subset_Icc_self ht))
      simp only [sub_zero, abs_one, mul_one] at hle
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    exact (tendsto_nhds_unique hs_hyp.hasSum.tendsto_sum_nat hmul) ▸ hs_hyp.hasSum
  exact hsum_hyp.tsum_eq

/-! ### Part 2: Exact FTC proofs of Identity (2) and Identity (3) -/

private lemma K_eq_integral (a x : ℝ) (ha : 1 < |a|) (hx : 0 < x) :
    K a x = ((a - 1) * x - 1) * ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - (1 / a) * t) ^ (-(a * x)) := by
  unfold K
  have hinv : |1 / a| < 1 := by
    rw [one_div, abs_inv]
    exact inv_lt_one_of_one_lt₀ ha
  rw [hyp2F1_1_eq_euler_integral (a * x) x (1 / a) hx hinv]
  have hx1 : x + 1 ≠ 0 := by linarith
  field_simp

private lemma identity2 (a x : ℝ) (ha : 2 < a) (hx : 0 < x) :
    2 + K a x + K (1 - a) x = 0 := by
  have ha1 : 1 < |a| := by rw [abs_of_pos (by linarith)]; linarith
  have h1a : 1 < |1 - a| := by rw [abs_of_neg (by linarith)]; linarith
  rw [K_eq_integral a x ha1 hx, K_eq_integral (1 - a) x h1a hx]
  set b : ℝ := a - 1
  have hb : 0 < b := by simp only [b]; linarith
  have ha_pos : 0 < a := by linarith
  -- Substitute t = φ(u) = a * u / (b + u) in the first integral!
  let φ : ℝ → ℝ := fun u => a * u / (b + u)
  let φ' : ℝ → ℝ := fun u => a * b / (b + u) ^ 2
  have hφ_deriv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hbu : b + u ≠ 0 := by linarith [hu.1]
    have h1 : HasDerivAt (fun v : ℝ => a * v) a u := by
      simpa using (hasDerivAt_id u).const_mul a
    have h2 : HasDerivAt (fun v : ℝ => b + v) 1 u := by
      simpa using (hasDerivAt_id u).const_add b
    have hdeq : (a * (b + u) - a * u * 1) / (b + u) ^ 2 = φ' u := by simp only [φ']; ring
    rw [← hdeq]
    exact h1.div h2 hbu
  have hφ'_cont : ContinuousOn φ' (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2) ?_
    intro u hu
    have : 0 < b + u := by linarith [hu.1]
    positivity
  have hf_cont : ContinuousOn (fun t : ℝ => (1 - t) ^ x * (1 - (1 / a) * t) ^ (-(a * x)))
      (φ '' Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.mono ?_ (s := Set.Icc (0 : ℝ) 1) ?_
    · refine (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (le_of_lt hx))).mul ?_
      refine ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
      intro t ht
      left
      have : (1 / a) * t ≤ 1 / a := by
        have : 0 < 1 / a := by positivity
        nlinarith [ht.2]
      have : 1 / a < 1 := by rw [div_lt_one ha_pos]; linarith
      linarith
    · rintro _ ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      have hbu : 0 < b + u := by linarith [hu.1]
      constructor
      · exact div_nonneg (mul_nonneg (le_of_lt ha_pos) hu.1) (le_of_lt hbu)
      · rw [div_le_one hbu]; simp only [b]; nlinarith [hu.2]
  have hsub := intervalIntegral.integral_comp_mul_deriv' hφ_deriv hφ'_cont hf_cont
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφ1 : φ 1 = 1 := by
    simp only [φ, mul_one, b]
    have hne : a - 1 + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hφ0, hφ1] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  -- Combine both integrals into ∫_0^1 H'(u) du = H(1) - H(0) = 0 - 2 = -2!
  let H : ℝ → ℝ := fun u =>
    (2 + u / b) * (1 - u) ^ (x + 1) * ((b + u) / b) ^ (b * x - 1)
  have hintegrand : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ((a - 1) * x - 1) * (((1 - φ u) ^ x * (1 - (1 / a) * φ u) ^ (-(a * x))) * φ' u) +
      ((1 - a - 1) * x - 1) * ((1 - u) ^ x * (1 - (1 / (1 - a)) * u) ^ (-((1 - a) * x))) =
      (1 - u) ^ x * ((b + u) / b) ^ (b * x - 2) *
        ((b * x - 1) * (a / b) + (-a * x - 1) * ((b + u) / b) ^ 2) := by
    intro u hu
    have hbu : 0 < b + u := by linarith [hu.1]
    have h1u : 0 < 1 - u := by linarith [hu.2]
    have hq : 0 < (b + u) / b := div_pos hbu hb
    have h1φ : 1 - φ u = (1 - u) / ((b + u) / b) := by
      have hbu_ne : b + u ≠ 0 := ne_of_gt hbu
      have hb_ne : b ≠ 0 := ne_of_gt hb
      have hab : a = b + 1 := by simp only [b]; ring
      simp only [φ]
      rw [hab]; field_simp; ring
    have h2φ : 1 - (1 / a) * φ u = ((b + u) / b)⁻¹ := by
      have hbu_ne : b + u ≠ 0 := ne_of_gt hbu
      have hb_ne : b ≠ 0 := ne_of_gt hb
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      simp only [φ]; field_simp; ring
    have h1m : 1 - (1 / (1 - a)) * u = (b + u) / b := by
      have : 1 - a = -b := by simp only [b]; ring
      have hb_ne : b ≠ 0 := ne_of_gt hb
      rw [this]; field_simp; ring
    have hφ'_eq : φ' u = (a / b) * ((b + u) / b) ^ (-2 : ℝ) := by
      have hbu_ne : b + u ≠ 0 := ne_of_gt hbu
      have hb_ne : b ≠ 0 := ne_of_gt hb
      rw [Real.rpow_neg (le_of_lt hq), Real.rpow_two]
      simp only [φ']; field_simp
    have hr1 : (1 - φ u) ^ x * (1 - (1 / a) * φ u) ^ (-(a * x)) * φ' u =
        (a / b) * (1 - u) ^ x * ((b + u) / b) ^ (b * x - 2) := by
      rw [h1φ, h2φ, hφ'_eq, Real.div_rpow (le_of_lt h1u) (le_of_lt hq),
          Real.inv_rpow (le_of_lt hq), ← Real.rpow_neg (le_of_lt hq), neg_neg]
      have hcomb : ((b + u) / b) ^ x = (((b + u) / b) ^ (-x))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hq), inv_inv]
      have he : -x + a * x + (-2 : ℝ) = b * x - 2 := by simp only [b]; ring
      calc (1 - u) ^ x / ((b + u) / b) ^ x * ((b + u) / b) ^ (a * x) * ((a / b) * ((b + u) / b) ^ (-2 : ℝ))
          = (a / b) * (1 - u) ^ x * (((b + u) / b) ^ (-x) * ((b + u) / b) ^ (a * x) * ((b + u) / b) ^ (-2 : ℝ)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hq)]; ring
        _ = (a / b) * (1 - u) ^ x * ((b + u) / b) ^ (b * x - 2) := by
            rw [← Real.rpow_add hq, ← Real.rpow_add hq, he]
    have hr2 : (1 - u) ^ x * (1 - (1 / (1 - a)) * u) ^ (-((1 - a) * x)) =
        (1 - u) ^ x * ((b + u) / b) ^ (b * x - 2) * ((b + u) / b) ^ 2 := by
      rw [h1m]
      have he1 : -((1 - a) * x) = (b * x - 2) + (2 : ℝ) := by simp only [b]; ring
      rw [he1, Real.rpow_add hq, Real.rpow_two]
      ring
    rw [hr1, hr2]
    have hcoeff1 : (a - 1) * x - 1 = b * x - 1 := rfl
    have hcoeff2 : (1 - a - 1) * x - 1 = -a * x - 1 := by ring
    rw [hcoeff1, hcoeff2]
    ring
  have hH_deriv : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt H
        (((a - 1) * x - 1) * (((1 - φ u) ^ x * (1 - (1 / a) * φ u) ^ (-(a * x))) * φ' u) +
         ((1 - a - 1) * x - 1) * ((1 - u) ^ x * (1 - (1 / (1 - a)) * u) ^ (-((1 - a) * x)))) u := by
    intro u hu
    rw [hintegrand u hu]
    have hbu : 0 < b + u := by linarith [hu.1]
    have h1u : 0 < 1 - u := by linarith [hu.2]
    have hq : 0 < (b + u) / b := div_pos hbu hb
    have hd1 : HasDerivAt (fun v : ℝ => 2 + v / b) (1 / b) u := by
      simpa using ((hasDerivAt_id u).div_const b).const_add (2 : ℝ)
    have hd2 : HasDerivAt (fun v : ℝ => (1 - v) ^ (x + 1)) (-(x + 1) * (1 - u) ^ x) u := by
      have h1 : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
      have h2 := h1.rpow_const (Or.inl (ne_of_gt h1u)) (p := x + 1)
      have hdeq : -1 * (x + 1) * (1 - u) ^ (x + 1 - 1) = -(x + 1) * (1 - u) ^ x := by
        rw [add_sub_cancel_right]; ring
      rw [← hdeq]; exact h2
    have hd3 : HasDerivAt (fun v : ℝ => ((b + v) / b) ^ (b * x - 1))
        (((b * x - 1) / b) * ((b + u) / b) ^ (b * x - 2)) u := by
      have h1 : HasDerivAt (fun v : ℝ => (b + v) / b) (1 / b) u := by
        simpa using ((hasDerivAt_id u).const_add b).div_const b
      have h2 := h1.rpow_const (Or.inl (ne_of_gt hq)) (p := b * x - 1)
      have hdeq : 1 / b * (b * x - 1) * ((b + u) / b) ^ (b * x - 1 - 1) =
          ((b * x - 1) / b) * ((b + u) / b) ^ (b * x - 2) := by
        rw [show b * x - 1 - 1 = b * x - 2 by ring]; ring
      rw [← hdeq]; exact h2
    have hprod := (hd1.mul hd2).mul hd3
    have h1u_pow : (1 - u) ^ (x + 1) = (1 - u) ^ x * (1 - u) := by
      rw [Real.rpow_add h1u, Real.rpow_one]
    have hq_pow : ((b + u) / b) ^ (b * x - 1) = ((b + u) / b) ^ (b * x - 2) * ((b + u) / b) := by
      rw [show b * x - 1 = (b * x - 2) + 1 by ring, Real.rpow_add hq, Real.rpow_one]
    have hdeq : ((1 / b * (1 - u) ^ (x + 1) + (2 + u / b) * (-(x + 1) * (1 - u) ^ x)) *
          ((b + u) / b) ^ (b * x - 1) +
        ((2 + u / b) * (1 - u) ^ (x + 1)) * (((b * x - 1) / b) * ((b + u) / b) ^ (b * x - 2))) =
        (1 - u) ^ x * ((b + u) / b) ^ (b * x - 2) *
          ((b * x - 1) * (a / b) + (-a * x - 1) * ((b + u) / b) ^ 2) := by
      rw [h1u_pow, hq_pow]
      have hbne : b ≠ 0 := ne_of_gt hb
      have ha_eq : a = b + 1 := by simp only [b]; ring
      rw [ha_eq]
      field_simp
      ring
    rw [← hdeq]
    exact hprod
  have hH_cont : ContinuousOn H (Set.Icc 0 1) := by
    refine ((continuousOn_const.add (continuousOn_id.div_const b)).mul
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (by linarith)))).mul ?_
    refine ContinuousOn.rpow_const ((continuousOn_const.add continuousOn_id).div_const b) ?_
    intro u hu
    left
    exact ne_of_gt (div_pos (by linarith [hu.1]) hb)
  have hintA : IntervalIntegrable
      (fun u => ((a - 1) * x - 1) * (((1 - φ u) ^ x * (1 - (1 / a) * φ u) ^ (-(a * x))) * φ' u))
      volume 0 1 := by
    refine (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ?_)
    refine continuousOn_const.mul ((hf_cont.comp ?_ ?_).mul ?_)
    · refine (continuousOn_const.mul continuousOn_id).div (continuousOn_const.add continuousOn_id) ?_
      intro u hu; linarith [hu.1]
    · intro u hu; exact Set.mem_image_of_mem φ (by rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])
    · simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hφ'_cont
  have hintB : IntervalIntegrable
      (fun u => ((1 - a - 1) * x - 1) * ((1 - u) ^ x * (1 - (1 / (1 - a)) * u) ^ (-((1 - a) * x))))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) ?_
    refine continuousOn_const.mul ((ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
      (fun _ _ => Or.inr (le_of_lt hx))).mul ?_)
    refine ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
    intro u hu
    left
    have h1a_neg : 1 - a < 0 := by linarith
    have : 0 ≤ -(1 / (1 - a)) * u := by
      have : 0 < -(1 / (1 - a)) := by rw [neg_pos]; exact div_neg_of_pos_of_neg one_pos h1a_neg
      nlinarith [hu.1]
    linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hH_cont hH_deriv
    (hintA.add hintB)
  rw [intervalIntegral.integral_add hintA hintB] at hftc
  have hH0 : H 0 = 2 := by
    simp only [H, zero_div, add_zero, sub_zero, Real.one_rpow, div_self (ne_of_gt hb), mul_one]
  have hH1 : H 1 = 0 := by
    simp only [H, sub_self, Real.zero_rpow (by linarith : x + 1 ≠ 0), mul_zero, zero_mul]
  rw [hH0, hH1] at hftc
  simp only [Function.comp_apply, b] at hftc ⊢
  linarith

private lemma half_beta_eq (a x : ℝ) (ha : 1 < a) (hx : 0 < x) :
    (a ^ (a * x - 1) / (a - 1) ^ ((a - 1) * x - 1)) *
      (x * ∫ w in (0 : ℝ)..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
      (1 / a) * K a x = 1 := by
  have ha_pos : 0 < a := by linarith
  have ha1 : 1 < |a| := by rw [abs_of_pos ha_pos]; exact ha
  have hb : 0 < a - 1 := by linarith
  have h1a_pos : 0 < 1 / a := by positivity
  have h1a_lt1 : 1 / a < 1 := by rw [div_lt_one ha_pos]; exact ha
  rw [K_eq_integral a x ha1 hx]
  -- Substitute t = ψ(w) = (1 - a * w) / (1 - w) on [0, 1/a] (maps 0 ↦ 1, 1/a ↦ 0)!
  let ψ : ℝ → ℝ := fun w => (1 - a * w) / (1 - w)
  let ψ' : ℝ → ℝ := fun w => -(a - 1) / (1 - w) ^ 2
  have hψ_deriv : ∀ w ∈ Set.uIcc (0 : ℝ) (1 / a), HasDerivAt ψ (ψ' w) w := by
    intro w hw
    rw [Set.uIcc_of_le (le_of_lt h1a_pos)] at hw
    have h1w : 1 - w ≠ 0 := by linarith [hw.2]
    have h1 : HasDerivAt (fun v : ℝ => 1 - a * v) (-a) w := by
      simpa using ((hasDerivAt_id w).const_mul a).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun v : ℝ => 1 - v) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub (1 : ℝ)
    have hdeq : (-a * (1 - w) - (1 - a * w) * (-1)) / (1 - w) ^ 2 = ψ' w := by
      simp only [ψ']; ring
    rw [← hdeq]
    exact h1.div h2 h1w
  have hψ'_cont : ContinuousOn ψ' (Set.uIcc (0 : ℝ) (1 / a)) := by
    rw [Set.uIcc_of_le (le_of_lt h1a_pos)]
    refine continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2) ?_
    intro w hw
    have : 0 < 1 - w := by linarith [hw.2]
    positivity
  have hf_cont : ContinuousOn (fun t : ℝ => (1 - t) ^ x * (1 - (1 / a) * t) ^ (-(a * x)))
      (ψ '' Set.uIcc (0 : ℝ) (1 / a)) := by
    refine ContinuousOn.mono ?_ (s := Set.Icc (0 : ℝ) 1) ?_
    · refine (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        (fun _ _ => Or.inr (le_of_lt hx))).mul ?_
      refine ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
      intro t ht
      left
      have : (1 / a) * t ≤ 1 / a := by nlinarith [ht.2]
      linarith
    · rintro _ ⟨w, hw, rfl⟩
      rw [Set.uIcc_of_le (le_of_lt h1a_pos)] at hw
      have h1w : 0 < 1 - w := by linarith [hw.2]
      constructor
      · apply div_nonneg _ (le_of_lt h1w)
        have : a * w ≤ 1 := by
          have := mul_le_mul_of_nonneg_left hw.2 (le_of_lt ha_pos)
          rwa [mul_one_div_cancel (ne_of_gt ha_pos)] at this
        linarith
      · rw [div_le_one h1w]; nlinarith [hw.1]
  have hsub := intervalIntegral.integral_comp_mul_deriv' hψ_deriv hψ'_cont hf_cont
  have hψ0 : ψ 0 = 1 := by simp [ψ]
  have hψ1 : ψ (1 / a) = 0 := by
    simp only [ψ, mul_one_div_cancel (ne_of_gt ha_pos), sub_self, zero_div]
  rw [hψ0, hψ1, intervalIntegral.integral_symm (0 : ℝ) 1] at hsub
  -- So ∫_0^1 f = - ∫_0^{1/a} f(ψ w) * ψ' w!
  set C : ℝ := a ^ (a * x - 1) / (a - 1) ^ ((a - 1) * x - 1)
  have hK_eq : (1 / a) * (((a - 1) * x - 1) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - (1 / a) * t) ^ (-(a * x))) =
      C * (((a - 1) * x - 1) * ∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2)) := by
    have hint_eq : ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - (1 / a) * t) ^ (-(a * x)) =
        ∫ w in (0 : ℝ)..(1 / a),
          (a ^ (a * x) / (a - 1) ^ ((a - 1) * x - 1)) * (w ^ x * (1 - w) ^ ((a - 1) * x - 2)) := by
      have hneg : ∫ t in (0 : ℝ)..1, (1 - t) ^ x * (1 - (1 / a) * t) ^ (-(a * x)) =
          ∫ w in (0 : ℝ)..(1 / a), -(((1 - ψ w) ^ x * (1 - (1 / a) * ψ w) ^ (-(a * x))) * ψ' w) := by
        rw [intervalIntegral.integral_neg]
        dsimp only [Function.comp_apply] at hsub
        linarith
      rw [hneg]
      apply intervalIntegral.integral_congr_ae
      have hne0 : ∀ᵐ w ∂volume, w ≠ (0 : ℝ) := by
        rw [ae_iff]; simp only [not_not]; exact Real.volume_singleton
      filter_upwards [hne0] with w hw0 hw
      rw [Set.uIoc_of_le (le_of_lt h1a_pos)] at hw
      have hw_pos : 0 < w := hw.1
      have h1w : 0 < 1 - w := by linarith [hw.2]
      have h1ψ : 1 - ψ w = (a - 1) * w / (1 - w) := by
        simp only [ψ]; field_simp; ring
      have h2ψ : 1 - (1 / a) * ψ w = (a - 1) / (a * (1 - w)) := by
        simp only [ψ]; field_simp; ring
      rw [h1ψ, h2ψ]
      rw [Real.div_rpow (mul_nonneg (le_of_lt hb) (le_of_lt hw_pos)) (le_of_lt h1w),
          Real.mul_rpow (le_of_lt hb) (le_of_lt hw_pos),
          Real.div_rpow (le_of_lt hb) (mul_nonneg (le_of_lt ha_pos) (le_of_lt h1w)),
          Real.mul_rpow (le_of_lt ha_pos) (le_of_lt h1w)]
      rw [Real.rpow_neg (le_of_lt hb), Real.rpow_neg (le_of_lt ha_pos),
          Real.rpow_neg (le_of_lt h1w)]
      simp only [ψ']
      have hsub_b : (a - 1) ^ x * ((a - 1) ^ (a * x))⁻¹ * (a - 1) =
          ((a - 1) ^ ((a - 1) * x - 1))⁻¹ := by
        rw [← Real.rpow_neg (le_of_lt hb), ← Real.rpow_neg (le_of_lt hb)]
        have h1 : (a - 1) ^ (x + -(a * x) + 1) = (a - 1) ^ x * (a - 1) ^ (-(a * x)) * (a - 1) := by
          rw [Real.rpow_add hb, Real.rpow_add hb, Real.rpow_one]
        rw [← h1]
        congr 1; ring
      have hsub_w : ((1 - w) ^ x)⁻¹ * (1 - w) ^ (a * x) * ((1 - w) ^ 2)⁻¹ =
          (1 - w) ^ ((a - 1) * x - 2) := by
        rw [← Real.rpow_neg (le_of_lt h1w), ← Real.rpow_two (1 - w),
            ← Real.rpow_neg (le_of_lt h1w), ← Real.rpow_add h1w, ← Real.rpow_add h1w]
        congr 1; ring
      have h1w_ne : (1 - w) ^ x ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1w x)
      have ha_ne : a ^ (a * x) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha_pos _)
      have hb_ne : (a - 1) ^ (a * x) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
      have h1w2_ne : (1 - w) ^ 2 ≠ 0 := by positivity
      calc -((a - 1) ^ x * w ^ x / (1 - w) ^ x *
              (((a - 1) ^ (a * x))⁻¹ / ((a ^ (a * x))⁻¹ * ((1 - w) ^ (a * x))⁻¹)) *
              (-(a - 1) / (1 - w) ^ 2))
          = a ^ (a * x) * ((a - 1) ^ x * ((a - 1) ^ (a * x))⁻¹ * (a - 1)) *
              (w ^ x * (((1 - w) ^ x)⁻¹ * (1 - w) ^ (a * x) * ((1 - w) ^ 2)⁻¹)) := by
            field_simp
        _ = a ^ (a * x) / (a - 1) ^ ((a - 1) * x - 1) * (w ^ x * (1 - w) ^ ((a - 1) * x - 2)) := by
            rw [hsub_b, hsub_w, div_eq_mul_inv]
    rw [hint_eq, intervalIntegral.integral_const_mul]
    have ha_div : (1 / a) * (a ^ (a * x) / (a - 1) ^ ((a - 1) * x - 1)) = C := by
      simp only [C]
      have hpow : a ^ (a * x) = a ^ (a * x - 1) * a := by
        conv_lhs => rw [show a * x = (a * x - 1) + 1 by ring]
        rw [Real.rpow_add ha_pos, Real.rpow_one]
      rw [hpow]
      field_simp
    linear_combination (((a - 1) * x - 1) * ∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2)) * ha_div
  rw [hK_eq]
  -- Now prove x * ∫_0^{1/a} w^(x-1)*(1-w)^((a-1)x-1) - ((a-1)x-1) * ∫_0^{1/a} w^x*(1-w)^((a-1)x-2)
  -- = (1/a)^x * (1 - 1/a)^((a-1)x - 1) = C⁻¹!
  have hint_beta : IntervalIntegrable (fun w : ℝ => w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
      volume 0 (1 / a) := by
    apply IntervalIntegrable.mul_continuousOn
    · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) ?_
      intro w hw
      rw [Set.uIcc_of_le (le_of_lt h1a_pos)] at hw
      left; linarith [hw.2]
  have hint_K : IntervalIntegrable (fun w : ℝ => w ^ x * (1 - w) ^ ((a - 1) * x - 2))
      volume 0 (1 / a) := by
    refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt h1a_pos) ?_
    refine (ContinuousOn.rpow_const continuousOn_id (fun _ _ => Or.inr (le_of_lt hx))).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) ?_
    intro w hw
    left; linarith [hw.2]
  let F : ℝ → ℝ := fun w => w ^ x * (1 - w) ^ ((a - 1) * x - 1)
  have hftc_eps : ∀ ε : ℝ, 0 < ε → ε < 1 / a →
      x * (∫ w in ε..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
        ((a - 1) * x - 1) * (∫ w in ε..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2)) =
      F (1 / a) - F ε := by
    intro ε hε0 hε1
    have hderiv : ∀ w ∈ Set.uIcc ε (1 / a),
        HasDerivAt F
          (x * (w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
            ((a - 1) * x - 1) * (w ^ x * (1 - w) ^ ((a - 1) * x - 2))) w := by
      intro w hw
      rw [Set.uIcc_of_le (le_of_lt hε1)] at hw
      have hw0 : 0 < w := lt_of_lt_of_le hε0 hw.1
      have h1w : 0 < 1 - w := by linarith [hw.2]
      have hd1 : HasDerivAt (fun v : ℝ => v ^ x) (x * w ^ (x - 1)) w := by
        simpa using (hasDerivAt_id w).rpow_const (Or.inl (ne_of_gt hw0)) (p := x)
      have hd2 : HasDerivAt (fun v : ℝ => (1 - v) ^ ((a - 1) * x - 1))
          (-(((a - 1) * x - 1) * (1 - w) ^ ((a - 1) * x - 2))) w := by
        have h1 : HasDerivAt (fun v : ℝ => 1 - v) (-1) w := by
          simpa using (hasDerivAt_id w).const_sub (1 : ℝ)
        have h2 := h1.rpow_const (Or.inl (ne_of_gt h1w)) (p := (a - 1) * x - 1)
        have hdeq : -1 * ((a - 1) * x - 1) * (1 - w) ^ ((a - 1) * x - 1 - 1) =
            -(((a - 1) * x - 1) * (1 - w) ^ ((a - 1) * x - 2)) := by
          rw [show (a - 1) * x - 1 - 1 = (a - 1) * x - 2 by ring]; ring
        rw [← hdeq]; exact h2
      have hdeq : (x * w ^ (x - 1)) * (1 - w) ^ ((a - 1) * x - 1) +
          w ^ x * (-(((a - 1) * x - 1) * (1 - w) ^ ((a - 1) * x - 2))) =
          x * (w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
          ((a - 1) * x - 1) * (w ^ x * (1 - w) ^ ((a - 1) * x - 2)) := by ring
      rw [← hdeq]
      exact hd1.mul hd2
    have hint1 : IntervalIntegrable (fun w : ℝ => w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
        volume ε (1 / a) :=
      hint_beta.mono_set (by
        rw [Set.uIcc_of_le (le_of_lt hε1), Set.uIcc_of_le (le_of_lt h1a_pos)]
        exact Set.Icc_subset_Icc (le_of_lt hε0) le_rfl)
    have hint2 : IntervalIntegrable (fun w : ℝ => w ^ x * (1 - w) ^ ((a - 1) * x - 2))
        volume ε (1 / a) :=
      hint_K.mono_set (by
        rw [Set.uIcc_of_le (le_of_lt hε1), Set.uIcc_of_le (le_of_lt h1a_pos)]
        exact Set.Icc_subset_Icc (le_of_lt hε0) le_rfl)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hint1.const_mul x).sub (hint2.const_mul ((a - 1) * x - 1)))
    rw [intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    exact hftc
  -- Take limit as ε → 0⁺!
  have hlim_L : Tendsto (fun ε : ℝ =>
      x * (∫ w in ε..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
        ((a - 1) * x - 1) * (∫ w in ε..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (x * (∫ w in (0 : ℝ)..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
        ((a - 1) * x - 1) * (∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2)))) := by
    have hint_beta_uIcc : IntegrableOn (fun w : ℝ => w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
        (Set.uIcc 0 (1 / a)) volume := by
      rw [Set.uIcc_of_le (le_of_lt h1a_pos), integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt h1a_pos)).mp hint_beta
    have hint_K_uIcc : IntegrableOn (fun w : ℝ => w ^ x * (1 - w) ^ ((a - 1) * x - 2))
        (Set.uIcc 0 (1 / a)) volume := by
      rw [Set.uIcc_of_le (le_of_lt h1a_pos), integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt h1a_pos)).mp hint_K
    have hc1 : ContinuousOn (fun ε : ℝ => ∫ w in ε..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
        (Set.uIcc 0 (1 / a)) :=
      intervalIntegral.continuousOn_primitive_interval_left hint_beta_uIcc
    have hc2 : ContinuousOn (fun ε : ℝ => ∫ w in ε..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2))
        (Set.uIcc 0 (1 / a)) :=
      intervalIntegral.continuousOn_primitive_interval_left hint_K_uIcc
    have ht1 : Tendsto (fun ε : ℝ => ∫ w in ε..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
        (nhdsWithin 0 (Set.Ioo 0 (1 / a)))
        (nhds (∫ w in (0 : ℝ)..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))) := by
      have h0 := hc1 0 (Set.left_mem_uIcc)
      refine h0.mono_left (nhdsWithin_mono 0 ?_)
      rw [Set.uIcc_of_le (le_of_lt h1a_pos)]
      exact Set.Ioo_subset_Icc_self
    have ht2 : Tendsto (fun ε : ℝ => ∫ w in ε..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2))
        (nhdsWithin 0 (Set.Ioo 0 (1 / a)))
        (nhds (∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2))) := by
      have h0 := hc2 0 (Set.left_mem_uIcc)
      refine h0.mono_left (nhdsWithin_mono 0 ?_)
      rw [Set.uIcc_of_le (le_of_lt h1a_pos)]
      exact Set.Ioo_subset_Icc_self
    have hnhds : nhdsWithin (0 : ℝ) (Set.Ioo 0 (1 / a)) = nhdsWithin 0 (Set.Ioi 0) :=
      nhdsWithin_Ioo_eq_nhdsGT h1a_pos
    rw [hnhds] at ht1 ht2
    exact (ht1.const_mul x).sub (ht2.const_mul _)
  have hlim_R : Tendsto (fun ε : ℝ => F (1 / a) - F ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (F (1 / a))) := by
    have hF0 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Tendsto (fun ε : ℝ => ε ^ x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa [Real.zero_rpow (ne_of_gt hx)] using
          ((Real.continuousAt_rpow_const 0 x (Or.inr (le_of_lt hx))).tendsto).mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun ε : ℝ => (1 - ε) ^ ((a - 1) * x - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have hc : ContinuousAt (fun ε : ℝ => (1 - ε) ^ ((a - 1) * x - 1)) 0 :=
          ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num)))
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      simpa [F] using h1.mul h2
    simpa using tendsto_const_nhds.sub hF0
  have hev : (fun ε : ℝ =>
      x * (∫ w in ε..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
        ((a - 1) * x - 1) * (∫ w in ε..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2))) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ => F (1 / a) - F ε) := by
    filter_upwards [Ioo_mem_nhdsGT h1a_pos] with ε hε
    exact hftc_eps ε hε.1 hε.2
  have heq : x * (∫ w in (0 : ℝ)..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
      ((a - 1) * x - 1) * (∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2)) = F (1 / a) :=
    tendsto_nhds_unique (hlim_L.congr' hev) hlim_R
  have hCF : C * F (1 / a) = 1 := by
    simp only [C, F]
    have h1 : 1 - 1 / a = (a - 1) / a := by field_simp
    rw [h1, Real.div_rpow zero_le_one (le_of_lt ha_pos), Real.one_rpow,
        Real.div_rpow (le_of_lt hb) (le_of_lt ha_pos)]
    have ha_comb : a ^ (a * x - 1) = a ^ x * a ^ ((a - 1) * x - 1) := by
      rw [← Real.rpow_add ha_pos]; congr 1; ring
    rw [ha_comb]
    have hax : a ^ x ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha_pos _)
    have hbx : (a - 1) ^ ((a - 1) * x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
    have hab : a ^ ((a - 1) * x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha_pos _)
    field_simp
  calc C * (x * ∫ w in (0 : ℝ)..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
        C * (((a - 1) * x - 1) * ∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2))
      = C * (x * (∫ w in (0 : ℝ)..(1 / a), w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) -
          ((a - 1) * x - 1) * (∫ w in (0 : ℝ)..(1 / a), w ^ x * (1 - w) ^ ((a - 1) * x - 2))) := by ring
    _ = C * F (1 / a) := by rw [heq]
    _ = 1 := hCF

private lemma real_beta_integral_eq_betaFn (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∫ w in (0 : ℝ)..1, w ^ (x - 1) * (1 - w) ^ (y - 1) = betaFn x y := by
  have hC := Complex.betaIntegral_eq_Gamma_mul_div (x : ℂ) (y : ℂ)
    (by simpa using hx) (by simpa using hy)
  have hre := congrArg Complex.re hC
  have hrhs : (Complex.Gamma (x : ℂ) * Complex.Gamma (y : ℂ) / Complex.Gamma ((x : ℂ) + (y : ℂ))).re =
      betaFn x y := by
    unfold betaFn
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    norm_cast
  have hlhs : (Complex.betaIntegral (x : ℂ) (y : ℂ)).re =
      ∫ w in (0 : ℝ)..1, w ^ (x - 1) * (1 - w) ^ (y - 1) := by
    unfold Complex.betaIntegral
    have hpt : ∀ᵐ w ∂volume, w ∈ Set.uIoc (0 : ℝ) 1 →
        (w : ℂ) ^ ((x : ℂ) - 1) * (1 - (w : ℂ)) ^ ((y : ℂ) - 1) =
        ((w ^ (x - 1) * (1 - w) ^ (y - 1) : ℝ) : ℂ) := by
      have hne1 : ∀ᵐ w ∂volume, w ≠ (1 : ℝ) := by
        rw [ae_iff]; simp only [not_not]; exact Real.volume_singleton
      filter_upwards [hne1] with w hw1 hw
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hw
      have hw0 : 0 ≤ w := le_of_lt hw.1
      have h1w : 0 ≤ 1 - w := by linarith [hw.2]
      push_cast
      rw [Complex.ofReal_cpow hw0, Complex.ofReal_cpow h1w]
      push_cast; rfl
    have heq : (∫ w in (0 : ℝ)..1, (w : ℂ) ^ ((x : ℂ) - 1) * (1 - (w : ℂ)) ^ ((y : ℂ) - 1)) =
        ∫ w in (0 : ℝ)..1, ((w ^ (x - 1) * (1 - w) ^ (y - 1) : ℝ) : ℂ) :=
      intervalIntegral.integral_congr_ae hpt
    rw [heq, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  linarith

private lemma identity3 (a x : ℝ) (ha : 1 < a) (hx : 0 < x) :
    2 + (1 / a) * K a x + ((a - 1) / a) * K (a / (a - 1)) ((a - 1) * x) =
      a * x * (a - 1) ^ (x - 1) * (a / (a - 1)) ^ (a * x - 2) * betaFn x ((a - 1) * x) := by
  have ha_pos : 0 < a := by linarith
  have hb : 0 < a - 1 := by linarith
  have h1 := half_beta_eq a x ha hx
  set a' : ℝ := a / (a - 1)
  set x' : ℝ := (a - 1) * x
  have ha' : 1 < a' := by simp only [a']; rw [one_lt_div hb]; linarith
  have hx' : 0 < x' := mul_pos hb hx
  have h2 := half_beta_eq a' x' ha' hx'
  have ha'_sub : a' - 1 = 1 / (a - 1) := by simp only [a']; field_simp; ring
  have h1_div_a' : 1 / a' = 1 - 1 / a := by simp only [a']; field_simp
  have hax' : (a' - 1) * x' = x := by rw [ha'_sub]; simp only [x']; field_simp
  have ha'x' : a' * x' = a * x := by simp only [a', x']; field_simp
  -- Transform the integral in h2 via w = 1 - v (from 0..(1 - 1/a) to (1/a)..1):
  have hint_flip : ∫ v in (0 : ℝ)..(1 / a'), v ^ (x' - 1) * (1 - v) ^ ((a' - 1) * x' - 1) =
      ∫ w in (1 / a)..1, w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1) := by
    rw [h1_div_a', hax']
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun w : ℝ => w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1)) (1 : ℝ) (a := (0 : ℝ)) (b := 1 - 1 / a)
    simp only [sub_zero, sub_sub_cancel] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [x']
    ring
  -- Check the constant in h2 equals C * x = (a ^ (a*x - 1) / (a - 1) ^ ((a-1)*x - 1)) * x!
  have hconst2 : (a' ^ (a' * x' - 1) / (a' - 1) ^ ((a' - 1) * x' - 1)) * x' =
      (a ^ (a * x - 1) / (a - 1) ^ ((a - 1) * x - 1)) * x := by
    rw [ha'x', hax', ha'_sub]
    simp only [a', x']
    rw [Real.div_rpow (le_of_lt ha_pos) (le_of_lt hb),
        Real.div_rpow zero_le_one (le_of_lt hb), Real.one_rpow]
    have hb_comb : (a - 1) ^ (a * x - 1) = (a - 1) ^ ((a - 1) * x - 1) * (a - 1) ^ (x - 1) * (a - 1) := by
      rw [show a * x - 1 = ((a - 1) * x - 1) + (x - 1) + 1 by ring,
          Real.rpow_add hb, Real.rpow_add hb, Real.rpow_one]
    rw [hb_comb]
    have h1 : (a - 1) ^ ((a - 1) * x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
    have h2 : (a - 1) ^ (x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
    have h3 : a - 1 ≠ 0 := ne_of_gt hb
    field_simp
  have h1a'_eq : 1 / a' = (a - 1) / a := by simp only [a']; field_simp
  rw [hint_flip, ← mul_assoc, hconst2, h1a'_eq] at h2
  rw [← mul_assoc] at h1
  -- Split Beta integral at 1/a:
  have hbeta_int1 : IntervalIntegrable (fun w : ℝ => w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
      volume 0 (1 / a) := by
    apply IntervalIntegrable.mul_continuousOn
    · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) ?_
      intro w hw
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 1 / a)] at hw
      have h1a_lt : 1 / a < 1 := by rw [div_lt_one ha_pos]; exact ha
      left; linarith [hw.2]
  have hbeta_int2 : IntervalIntegrable (fun w : ℝ => w ^ (x - 1) * (1 - w) ^ ((a - 1) * x - 1))
      volume (1 / a) 1 := by
    have hcomp : IntervalIntegrable (fun v : ℝ => (1 - v) ^ (x - 1) * v ^ ((a - 1) * x - 1))
        volume 0 (1 - 1 / a) := by
      have hcomm : (fun v : ℝ => (1 - v) ^ (x - 1) * v ^ ((a - 1) * x - 1)) =
          fun v => v ^ ((a - 1) * x - 1) * (1 - v) ^ (x - 1) := by ext v; ring
      rw [hcomm]
      apply IntervalIntegrable.mul_continuousOn
      · exact intervalIntegral.intervalIntegrable_rpow' (by linarith [mul_pos hb hx])
      · refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) ?_
        intro v hv
        rw [Set.uIcc_of_le (by
          have : 1 / a < 1 := by rw [div_lt_one ha_pos]; exact ha
          linarith)] at hv
        left; linarith [hv.2, div_pos one_pos ha_pos]
    have hsub := hcomp.comp_sub_left (1 : ℝ)
    simpa [sub_sub_cancel] using hsub.symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hbeta_int1 hbeta_int2
  rw [real_beta_integral_eq_betaFn x ((a - 1) * x) hx (mul_pos hb hx)] at hsplit
  have hC_rhs : (a ^ (a * x - 1) / (a - 1) ^ ((a - 1) * x - 1)) * x =
      a * x * (a - 1) ^ (x - 1) * (a / (a - 1)) ^ (a * x - 2) := by
    rw [Real.div_rpow (le_of_lt ha_pos) (le_of_lt hb)]
    have ha_c : a ^ (a * x - 1) = a * a ^ (a * x - 2) := by
      rw [show a * x - 1 = 1 + (a * x - 2) by ring, Real.rpow_add ha_pos, Real.rpow_one]
    have hb_c : (a - 1) ^ (a * x - 2) = (a - 1) ^ ((a - 1) * x - 1) * (a - 1) ^ (x - 1) := by
      rw [← Real.rpow_add hb]; congr 1; ring
    rw [ha_c, hb_c]
    have h1 : (a - 1) ^ ((a - 1) * x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
    have h2 : (a - 1) ^ (x - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
    field_simp
  have hsum : (a ^ (a * x - 1) / (a - 1) ^ ((a - 1) * x - 1)) * x * betaFn x ((a - 1) * x) -
      (1 / a) * K a x - ((a - 1) / a) * K a' x' = 2 := by
    rw [← hsplit]
    linarith
  rw [hC_rhs] at hsum
  linarith

private theorem main_proof : type_of% @OMA.S_mse_2306090.main :=
  ⟨identity2, identity3⟩

end OMA.P_mse_2306090

theorem OMA.solution : type_of% @OMA.S_mse_2306090.main :=
  OMA.P_mse_2306090.main_proof
