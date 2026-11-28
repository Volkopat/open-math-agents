import OMAStatements.S_arxiv_1801_06737

-- Problem: At What Frequency Should the Kelly Bettor Bet? (arXiv:1801.06737), Conjectures 1 and 2.
-- Credit: @ricnov (the owner of the agent is credited as the solver)
--
-- Conjecture 2 (the sufficient attractiveness inequality is necessary). Suppose the inequality
-- fails. Then the one-period problem has an interior optimal fraction Ks, where the marginal growth
-- E[X / (1 + Ks X)] vanishes (Fatou's lemma and the intermediate value theorem). Holding a fraction K
-- for two periods is the same as betting K in the first period and the drifted fraction
-- K (1 + X) / (1 + K X) in the second. A second-order bound for the logarithm turns the distance of
-- these two fractions from Ks into a loss of growth, and the two distances cannot both be small
-- unless the return is constant. So the optimal growth with two periods between bets is strictly
-- below the one-period optimum.
--
-- Conjecture 1 (the optimal growth is non-increasing in the number n of periods between bets).
-- Let T be the total return over n periods and D(K) = E[T / (1 + K T)]. For every e > 0 some
-- fraction K in [0, 1) satisfies E[1 / (1 + K T)] ≤ 1 + e and E[(1 + T) / (1 + K T)] ≤ 1 + e:
-- take K = 0 if D(0) ≤ 0, a root of D if D changes sign on [0, 1), and K close to 1 otherwise
-- (OMA.exists_cert). Now take n + 1 periods and let T_j be the total return over the n periods
-- other than j. The product of the n + 1 gross returns 1 + T_j is the n-th power of the full gross
-- return, so by the Loomis–Whitney inequality (OMA.lw, proved here by integrating one coordinate
-- at a time with Hölder's inequality) the kernel F = ∏_j ((1 + e) (1 + K T_j)) ^ (-1/n) satisfies
-- E[F] ≤ 1 and E[(1 + T') F] ≤ 1, where T' is the total return over all n + 1 periods. For the
-- wealth W = 1 + K' T' of any fraction K', the bound log W ≤ W F - 1 - log F then gives
-- E[log W] ≤ ((n + 1) / n) (E[log(1 + K T)] + log(1 + e)) (OMA.core). Letting e tend to 0 proves
-- that the optimal growth for n + 1 periods is at most the one for n periods.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma OMA.log_second_order (u w b : ℝ) (hu : 0 < u) (hw : 0 < w) (hub : u ≤ b) (hwb : w ≤ b) :
    Real.log w ≤ Real.log u + (w - u) / u - (w - u) ^ 2 / (4 * b ^ 2) := by
  have hb : 0 < b := lt_of_lt_of_le hu hub
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℝ, 0 < p ∧ p ^ 2 = u :=
    ⟨Real.sqrt u, Real.sqrt_pos.2 hu, Real.sq_sqrt hu.le⟩
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 < q ∧ q ^ 2 = w :=
    ⟨Real.sqrt w, Real.sqrt_pos.2 hw, Real.sq_sqrt hw.le⟩
  have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at h1
  rw [Real.log_pow, Real.log_pow]
  have key : (q ^ 2 - p ^ 2) ^ 2 / (4 * b ^ 2) ≤ (q - p) ^ 2 / p ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (q ^ 2 - p ^ 2) ^ 2 * p ^ 2 = (q - p) ^ 2 * (p ^ 2 * (q + p) ^ 2) := by ring
    rw [e]
    have h2 : p ^ 2 * (q + p) ^ 2 ≤ 4 * b ^ 2 := by
      have h3 : (q + p) ^ 2 ≤ 4 * b := by nlinarith [sq_nonneg (q - p)]
      nlinarith [sq_nonneg p, sq_nonneg (q + p)]
    nlinarith [sq_nonneg (q - p)]
  have e2 : (q ^ 2 - p ^ 2) / p ^ 2 - (q - p) ^ 2 / p ^ 2 = 2 * (q / p - 1) := by
    field_simp
    ring
  push_cast
  linarith

/-- For a fraction `0 ≤ K < 1` and a return `-1 ≤ x ≤ b - 1`, the wealth factor `1 + K x` lies in
`[1 - K, b]`. -/
lemma OMA.factor_bounds (K x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x) (hxb : x ≤ b - 1)
    (hb : 1 ≤ b) : 1 - K ≤ 1 + K * x ∧ 1 + K * x ≤ b := by
  constructor
  · nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ x + 1)]
  · nlinarith [mul_le_mul_of_nonneg_left hxb hK0,
      mul_nonneg (sub_nonneg.2 hK1.le) (sub_nonneg.2 hb)]

lemma OMA.one_period_pointwise (K Ks x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hs0 : 0 ≤ Ks)
    (hs1 : Ks < 1) (hx : -1 ≤ x) (hxb : x ≤ b - 1) (hb : 1 ≤ b) :
    Real.log (1 + K * x) ≤ Real.log (1 + Ks * x) + (K - Ks) * (x / (1 + Ks * x))
      - (K - Ks) ^ 2 * x ^ 2 / (4 * b ^ 2) := by
  obtain ⟨h1, h2⟩ := OMA.factor_bounds K x b hK0 hK1 hx hxb hb
  obtain ⟨h3, h4⟩ := OMA.factor_bounds Ks x b hs0 hs1 hx hxb hb
  have h := OMA.log_second_order (1 + Ks * x) (1 + K * x) b (by linarith) (by linarith) h4 h2
  have e : (1 + K * x) - (1 + Ks * x) = (K - Ks) * x := by ring
  rw [e] at h
  have e2 : (K - Ks) * x / (1 + Ks * x) = (K - Ks) * (x / (1 + Ks * x)) := by ring
  have e3 : ((K - Ks) * x) ^ 2 = (K - Ks) ^ 2 * x ^ 2 := by ring
  rw [e2, e3] at h
  exact h

/-- The fraction of wealth at risk after one period of buy and hold. -/
noncomputable def OMA.kap (K x : ℝ) : ℝ := K * (1 + x) / (1 + K * x)

lemma OMA.kap_bounds (K x : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x) :
    0 ≤ OMA.kap K x ∧ OMA.kap K x < 1 := by
  have h : 0 < 1 + K * x := by nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ x + 1)]
  unfold OMA.kap
  constructor
  · exact div_nonneg (mul_nonneg hK0 (by linarith)) h.le
  · rw [div_lt_one h]
    nlinarith

lemma OMA.two_period_factor (K x0 x1 : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx0 : -1 ≤ x0) :
    1 + K * ((1 + x0) * (1 + x1) - 1) = (1 + K * x0) * (1 + OMA.kap K x0 * x1) := by
  have h : 0 < 1 + K * x0 := by nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ x0 + 1)]
  unfold OMA.kap
  field_simp
  ring

lemma OMA.two_period_pointwise (K Ks x0 x1 b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hs0 : 0 ≤ Ks)
    (hs1 : Ks < 1) (hx0 : -1 ≤ x0) (hx0b : x0 ≤ b - 1) (hx1 : -1 ≤ x1) (hx1b : x1 ≤ b - 1)
    (hb : 1 ≤ b) :
    Real.log (1 + K * ((1 + x0) * (1 + x1) - 1)) ≤
      Real.log (1 + Ks * x0) + Real.log (1 + Ks * x1)
        + (K - Ks) * (x0 / (1 + Ks * x0)) + (OMA.kap K x0 - Ks) * (x1 / (1 + Ks * x1))
        - ((K - Ks) ^ 2 * x0 ^ 2 + (OMA.kap K x0 - Ks) ^ 2 * x1 ^ 2) / (4 * b ^ 2) := by
  obtain ⟨hk0, hk1⟩ := OMA.kap_bounds K x0 hK0 hK1 hx0
  have hA := OMA.one_period_pointwise K Ks x0 b hK0 hK1 hs0 hs1 hx0 hx0b hb
  have hB := OMA.one_period_pointwise (OMA.kap K x0) Ks x1 b hk0 hk1 hs0 hs1 hx1 hx1b hb
  obtain ⟨h1, -⟩ := OMA.factor_bounds K x0 b hK0 hK1 hx0 hx0b hb
  obtain ⟨h2, -⟩ := OMA.factor_bounds (OMA.kap K x0) x1 b hk0 hk1 hx1 hx1b hb
  rw [OMA.two_period_factor K x0 x1 hK0 hK1 hx0,
    Real.log_mul (by linarith) (by linarith)]
  have e : ((K - Ks) ^ 2 * x0 ^ 2 + (OMA.kap K x0 - Ks) ^ 2 * x1 ^ 2) / (4 * b ^ 2)
      = (K - Ks) ^ 2 * x0 ^ 2 / (4 * b ^ 2) + (OMA.kap K x0 - Ks) ^ 2 * x1 ^ 2 / (4 * b ^ 2) := by
    ring
  rw [e]
  linarith

/-- Either the fraction `K` or the drifted fraction is away from `Ks`. -/
lemma OMA.bracket_pointwise (K Ks x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x)
    (hxb : x ≤ b - 1) (hb : 1 ≤ b) :
    K ^ 2 * (1 - K) ^ 2 * x ^ 2 / (2 * b ^ 2) ≤ (K - Ks) ^ 2 + (OMA.kap K x - Ks) ^ 2 := by
  obtain ⟨h1, h2⟩ := OMA.factor_bounds K x b hK0 hK1 hx hxb hb
  have hpos : 0 < 1 + K * x := by linarith
  have hb0 : 0 < b := by linarith
  have e : OMA.kap K x - K = K * (1 - K) * x / (1 + K * x) := by
    unfold OMA.kap
    field_simp
    ring
  have h3 : (OMA.kap K x - K) ^ 2 ≤ 2 * (K - Ks) ^ 2 + 2 * (OMA.kap K x - Ks) ^ 2 := by
    nlinarith [sq_nonneg (OMA.kap K x + K - 2 * Ks)]
  have h4 : K ^ 2 * (1 - K) ^ 2 * x ^ 2 / b ^ 2 ≤ (OMA.kap K x - K) ^ 2 := by
    rw [e, div_pow]
    have e5 : (K * (1 - K) * x) ^ 2 = K ^ 2 * (1 - K) ^ 2 * x ^ 2 := by ring
    rw [e5]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hpos.le h2 2
  have e6 : K ^ 2 * (1 - K) ^ 2 * x ^ 2 / (2 * b ^ 2) = K ^ 2 * (1 - K) ^ 2 * x ^ 2 / b ^ 2 / 2 := by
    field_simp
  rw [e6]
  linarith

/-- Bounded measurable functions are integrable for a finite measure. -/
lemma OMA.intble {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_mem_Icc (-C) C hf.aemeasurable (Filter.Eventually.of_forall fun ω => abs_le.1 (h ω))

/-- The marginal growth rate `x / (1 + K x)` is bounded. -/
lemma OMA.ratio_bound (K x b : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hx : -1 ≤ x) (hxb : x ≤ b - 1)
    (hb : 1 ≤ b) : |x / (1 + K * x)| ≤ b / (1 - K) := by
  obtain ⟨h1, -⟩ := OMA.factor_bounds K x b hK0 hK1 hx hxb hb
  have hpos : 0 < 1 + K * x := by linarith
  rw [abs_div, abs_of_pos hpos]
  exact div_le_div₀ (by linarith) (abs_le.2 ⟨by linarith, by linarith⟩) (by linarith) h1

/-- If the sufficient attractiveness inequality fails, the marginal growth rate is negative for
some fraction below one (Fatou's lemma). -/
lemma OMA.exists_K1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (hSA : 1 < ∫⁻ ω, (ENNReal.ofReal (1 + A ω))⁻¹ ∂P) :
    ∃ K1 : ℝ, 0 < K1 ∧ K1 < 1 ∧ ∫ ω, A ω / (1 + K1 * A ω) ∂P < 0 := by
  by_contra hcon
  push Not at hcon
  have hKm0 : ∀ m : ℕ, (0 : ℝ) < 1 - 1 / ((m : ℝ) + 2) := by
    intro m
    have h2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    rw [sub_pos, div_lt_one h2]
    linarith
  have hKm1 : ∀ m : ℕ, 1 - 1 / ((m : ℝ) + 2) < (1 : ℝ) := by
    intro m
    have h2 : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  have hlim : Filter.Tendsto (fun m : ℕ => 1 - 1 / ((m : ℝ) + 2)) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) Filter.atTop (nhds 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h3 := this.comp (Filter.tendsto_add_atTop_nat 1)
      refine h3.congr fun m => ?_
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    simpa using h1.const_sub 1
  have hle : ∀ m : ℕ, ∫⁻ ω, (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹ ∂P ≤ 1 := by
    intro m
    set K := 1 - 1 / ((m : ℝ) + 2) with hK
    have hpos : ∀ ω, 0 < 1 + K * A ω := fun ω => by
      have := (OMA.factor_bounds K (A ω) b (hKm0 m).le (hKm1 m) (hx ω).1 (hx ω).2 hb).1
      linarith [hKm1 m]
    have h1 : ∀ ω, (ENNReal.ofReal (1 + K * A ω))⁻¹ = ENNReal.ofReal (1 - K * (A ω / (1 + K * A ω))) := by
      intro ω
      rw [← ENNReal.ofReal_inv_of_pos (hpos ω)]
      congr 1
      have := (hpos ω).ne'
      field_simp
      ring
    simp_rw [h1]
    have hint : Integrable (fun ω => A ω / (1 + K * A ω)) P :=
      OMA.intble P _ (by fun_prop) (b / (1 - K))
        (fun ω => OMA.ratio_bound K (A ω) b (hKm0 m).le (hKm1 m) (hx ω).1 (hx ω).2 hb)
    have hnn : ∀ ω, 0 ≤ 1 - K * (A ω / (1 + K * A ω)) := by
      intro ω
      have e : 1 - K * (A ω / (1 + K * A ω)) = 1 / (1 + K * A ω) := by
        have := (hpos ω).ne'
        field_simp
        ring
      rw [e]
      exact (one_div_pos.2 (hpos ω)).le
    have hint2 : Integrable (fun ω => 1 - K * (A ω / (1 + K * A ω))) P :=
      (integrable_const 1).sub (hint.const_mul K)
    rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall hnn)]
    rw [ENNReal.ofReal_le_one, integral_sub (integrable_const 1) (hint.const_mul K),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    nlinarith [hcon K (hKm0 m) (hKm1 m), hKm0 m]
  have hF := lintegral_liminf_le (μ := P)
    (f := fun (m : ℕ) ω => (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹)
    (u := Filter.atTop) (fun m => by fun_prop)
  have hpt : ∀ ω, Filter.liminf
      (fun m : ℕ => (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹) Filter.atTop
      = (ENNReal.ofReal (1 + A ω))⁻¹ := by
    intro ω
    apply Filter.Tendsto.liminf_eq
    have h2 : Filter.Tendsto (fun m : ℕ => 1 + (1 - 1 / ((m : ℝ) + 2)) * A ω) Filter.atTop
        (nhds (1 + 1 * A ω)) := (hlim.mul_const _).const_add 1
    rw [one_mul] at h2
    exact tendsto_inv_iff.2 (ENNReal.tendsto_ofReal h2)
  simp_rw [hpt] at hF
  have hlim1 : Filter.liminf
      (fun m : ℕ => ∫⁻ ω, (ENNReal.ofReal (1 + (1 - 1 / ((m : ℝ) + 2)) * A ω))⁻¹ ∂P) Filter.atTop
      ≤ 1 := by
    refine Filter.liminf_le_of_le (h := fun c hc => ?_)
    obtain ⟨m, hm⟩ := hc.exists
    exact hm.trans (hle m)
  exact absurd (lt_of_lt_of_le hSA (hF.trans hlim1)) (lt_irrefl _)

/-- The marginal growth rate is continuous in the fraction, away from full investment. -/
lemma OMA.continuousOn_D {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (K1 : ℝ) (hK11 : K1 < 1) :
    ContinuousOn (fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) (Set.Icc 0 K1) := by
  apply continuousOn_of_dominated (bound := fun _ => b / (1 - K1))
  · intro K _
    exact (by fun_prop : Measurable fun ω => A ω / (1 + K * A ω)).aestronglyMeasurable
  · intro K hK
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have h1 := OMA.ratio_bound K (A ω) b hK.1 (lt_of_le_of_lt hK.2 hK11) (hx ω).1 (hx ω).2 hb
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hK.2])
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun ω => ?_
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro K hK
    have := (OMA.factor_bounds K (A ω) b hK.1 (lt_of_le_of_lt hK.2 hK11) (hx ω).1 (hx ω).2 hb).1
    have h2 : K < 1 := lt_of_le_of_lt hK.2 hK11
    linarith

/-- A fraction `0 < Ks < 1` at which the marginal growth rate vanishes (intermediate values). -/
lemma OMA.exists_Ks {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (hEX : 0 < ∫ ω, A ω ∂P) (hSA : 1 < ∫⁻ ω, (ENNReal.ofReal (1 + A ω))⁻¹ ∂P) :
    ∃ Ks : ℝ, 0 < Ks ∧ Ks < 1 ∧ ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0 := by
  obtain ⟨K1, hK10, hK11, hneg⟩ := OMA.exists_K1 P A hA b hb hx hSA
  have hcont := OMA.continuousOn_D P A hA b hb hx K1 hK11
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) K1)
      ((fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) 0) := by
    constructor
    · exact hneg.le
    · simpa using hEX.le
  obtain ⟨Ks, hKs, hDs⟩ := intermediate_value_Icc' hK10.le hcont hmem
  refine ⟨Ks, ?_, lt_of_le_of_lt hKs.2 hK11, hDs⟩
  rcases hKs.1.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hDs
    simp only [zero_mul, add_zero, div_one] at hDs
    linarith

lemma OMA.log_abs_le (y lo hi : ℝ) (hlo : 0 < lo) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    |Real.log y| ≤ |Real.log lo| + |Real.log hi| := by
  have ha := Real.log_le_log hlo h1
  have hb := Real.log_le_log (lt_of_lt_of_le hlo h1) h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log lo), abs_nonneg (Real.log hi)]
  · linarith [le_abs_self (Real.log hi), abs_nonneg (Real.log lo)]

lemma OMA.sq_bound (x b : ℝ) (hx : -1 ≤ x) (hxb : x ≤ b - 1) (hb : 1 ≤ b) : x ^ 2 ≤ b ^ 2 := by
  nlinarith

lemma OMA.drift_bound (K Ks x : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1)
    (hx : -1 ≤ x) : |OMA.kap K x - Ks| ≤ 1 := by
  obtain ⟨h0, h1⟩ := OMA.kap_bounds K x hK0 hK1 hx
  rw [abs_le]
  constructor <;> linarith

lemma OMA.integrable_log {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) : Integrable (fun ω => Real.log (1 + K * A ω)) P := by
  refine OMA.intble P _ (by fun_prop) (|Real.log (1 - K)| + |Real.log b|) (fun ω => ?_)
  obtain ⟨h1, h2⟩ := OMA.factor_bounds K (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb
  exact OMA.log_abs_le _ _ _ (by linarith) h1 h2

lemma OMA.integrable_ratio {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) : Integrable (fun ω => A ω / (1 + K * A ω)) P :=
  OMA.intble P _ (by fun_prop) (b / (1 - K))
    (fun ω => OMA.ratio_bound K (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb)

lemma OMA.integrable_sq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) :
    Integrable (fun ω => A ω ^ 2) P := by
  refine OMA.intble P _ (by fun_prop) (b ^ 2) (fun ω => ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact OMA.sq_bound _ _ (hx ω).1 (hx ω).2 hb

/-- One period: no fraction beats `Ks`. -/
lemma OMA.one_period_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b)
    (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) (Ks : ℝ) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1)
    (hD : ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0) (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∫ ω, Real.log (1 + K * A ω) ∂P ≤ ∫ ω, Real.log (1 + Ks * A ω) ∂P := by
  have hiLK := OMA.integrable_log P A hA b hb hx K hK0 hK1
  have hiLA := OMA.integrable_log P A hA b hb hx Ks hs0 hs1
  have hiRA := OMA.integrable_ratio P A hA b hb hx Ks hs0 hs1
  have hi : Integrable (fun ω => Real.log (1 + Ks * A ω) + (K - Ks) * (A ω / (1 + Ks * A ω))) P :=
    hiLA.add (hiRA.const_mul _)
  have hmono := integral_mono hiLK hi (fun ω => by
    have h := OMA.one_period_pointwise K Ks (A ω) b hK0 hK1 hs0 hs1 (hx ω).1 (hx ω).2 hb
    have h2 : 0 ≤ (K - Ks) ^ 2 * A ω ^ 2 / (4 * b ^ 2) := by positivity
    simp only
    linarith)
  rw [integral_add hiLA (hiRA.const_mul _), integral_const_mul, hD] at hmono
  linarith

lemma OMA.second_moment_pos {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b)
    (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) (hEX : 0 < ∫ ω, A ω ∂P) : 0 < ∫ ω, A ω ^ 2 ∂P := by
  have hiA : Integrable A P := OMA.intble P A hA b (fun ω => abs_le.2 ⟨by linarith [(hx ω).1], by linarith [(hx ω).2]⟩)
  have hiQ := OMA.integrable_sq P A hA b hb hx
  set t := ∫ ω, A ω ∂P with ht
  have hi2 : Integrable (fun ω => A ω ^ 2 + t ^ 2) P := hiQ.add (integrable_const _)
  have hmono := integral_mono (hiA.const_mul (2 * t)) hi2 (fun ω => by
    simp only
    nlinarith [sq_nonneg (A ω - t)])
  rw [integral_const_mul, integral_add hiQ (integrable_const _), integral_const] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  nlinarith

/-- Two periods of buy and hold: the expected log-growth falls short of twice the one-period optimum
by a multiple of the squared distances of the initial and the drifted fraction from `Ks`. -/
lemma OMA.two_period_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hind : IndepFun A B P) (hid : IdentDistrib B A P P) (b : ℝ) (hb : 1 ≤ b)
    (hxA : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1) (hxB : ∀ ω, -1 ≤ B ω ∧ B ω ≤ b - 1)
    (Ks : ℝ) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1) (hD : ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∫ ω, Real.log (1 + K * ((1 + A ω) * (1 + B ω) - 1)) ∂P ≤
      2 * ∫ ω, Real.log (1 + Ks * A ω) ∂P
        - (∫ ω, A ω ^ 2 ∂P) / (4 * b ^ 2)
          * ((K - Ks) ^ 2 + ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) := by
  have hb0 : 0 < b := by linarith
  have hkm : Measurable (fun x : ℝ => OMA.kap K x - Ks) := by
    unfold OMA.kap
    fun_prop
  -- integrability of the pieces
  have hiLA := OMA.integrable_log P A hA b hb hxA Ks hs0 hs1
  have hiLB := OMA.integrable_log P B hB b hb hxB Ks hs0 hs1
  have hiRA := OMA.integrable_ratio P A hA b hb hxA Ks hs0 hs1
  have hiQA := OMA.integrable_sq P A hA b hb hxA
  have hiSRB : Integrable (fun ω => (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω))) P := by
    refine OMA.intble P _ ((hkm.comp hA).mul (by fun_prop)) (1 * (b / (1 - Ks))) (fun ω => ?_)
    rw [abs_mul]
    exact mul_le_mul (OMA.drift_bound K Ks (A ω) hK0 hK1 hs0 hs1 (hxA ω).1)
      (OMA.ratio_bound Ks (B ω) b hs0 hs1 (hxB ω).1 (hxB ω).2 hb) (abs_nonneg _) zero_le_one
  have hiTQB : Integrable (fun ω => (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) P := by
    refine OMA.intble P _ (((hkm.comp hA).pow_const 2).mul (by fun_prop)) (1 * b ^ 2) (fun ω => ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    have h1 := OMA.drift_bound K Ks (A ω) hK0 hK1 hs0 hs1 (hxA ω).1
    have h2 : (OMA.kap K (A ω) - Ks) ^ 2 ≤ 1 := by
      have := abs_le.1 h1
      nlinarith
    exact mul_le_mul h2 (OMA.sq_bound _ _ (hxB ω).1 (hxB ω).2 hb) (sq_nonneg _) zero_le_one
  have hiL : Integrable (fun ω => Real.log (1 + K * ((1 + A ω) * (1 + B ω) - 1))) P := by
    refine OMA.intble P _ (by fun_prop) (|Real.log (1 - K)| + |Real.log (b ^ 2)|) (fun ω => ?_)
    have hA0 : 0 ≤ 1 + A ω := by linarith [(hxA ω).1]
    have hB0 : 0 ≤ 1 + B ω := by linarith [(hxB ω).1]
    have hprod : (1 + A ω) * (1 + B ω) ≤ b ^ 2 := by
      have := mul_le_mul (by linarith [(hxA ω).2] : 1 + A ω ≤ b)
        (by linarith [(hxB ω).2] : 1 + B ω ≤ b) hB0 hb0.le
      nlinarith
    refine OMA.log_abs_le _ _ _ (by linarith) ?_ ?_
    · nlinarith [mul_nonneg hK0 (mul_nonneg hA0 hB0)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hK1.le) (by nlinarith : (0 : ℝ) ≤ b ^ 2 - 1),
        mul_nonneg hK0 (sub_nonneg.2 hprod)]
  -- the pointwise bound, integrated
  have hi12 : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)) P :=
    hiLA.add hiLB
  have hi123 : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)
      + (K - Ks) * (A ω / (1 + Ks * A ω))) P := hi12.add (hiRA.const_mul _)
  have hi1234 : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)
      + (K - Ks) * (A ω / (1 + Ks * A ω))
      + (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω))) P := hi123.add hiSRB
  have hiQ : Integrable (fun ω => (K - Ks) ^ 2 * A ω ^ 2
      + (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) P := (hiQA.const_mul _).add hiTQB
  have hiQd : Integrable (fun ω => ((K - Ks) ^ 2 * A ω ^ 2
      + (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) / (4 * b ^ 2)) P := hiQ.div_const _
  have hiR : Integrable (fun ω => Real.log (1 + Ks * A ω) + Real.log (1 + Ks * B ω)
      + (K - Ks) * (A ω / (1 + Ks * A ω))
      + (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω))
      - ((K - Ks) ^ 2 * A ω ^ 2 + (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2) / (4 * b ^ 2)) P :=
    hi1234.sub hiQd
  have hmono := integral_mono hiL hiR (fun ω =>
    OMA.two_period_pointwise K Ks (A ω) (B ω) b hK0 hK1 hs0 hs1 (hxA ω).1 (hxA ω).2
      (hxB ω).1 (hxB ω).2 hb)
  rw [integral_sub hi1234 hiQd, integral_add hi123 hiSRB, integral_add hi12 (hiRA.const_mul _),
    integral_add hiLA hiLB, integral_const_mul, integral_div,
    integral_add (hiQA.const_mul _) hiTQB, integral_const_mul] at hmono
  -- identical distribution and independence
  have e1 : ∫ ω, Real.log (1 + Ks * B ω) ∂P = ∫ ω, Real.log (1 + Ks * A ω) ∂P :=
    (hid.comp (u := fun x : ℝ => Real.log (1 + Ks * x)) (by fun_prop)).integral_eq
  have e2 : ∫ ω, B ω / (1 + Ks * B ω) ∂P = ∫ ω, A ω / (1 + Ks * A ω) ∂P :=
    (hid.comp (u := fun x : ℝ => x / (1 + Ks * x)) (by fun_prop)).integral_eq
  have e3 : ∫ ω, B ω ^ 2 ∂P = ∫ ω, A ω ^ 2 ∂P :=
    (hid.comp (u := fun x : ℝ => x ^ 2) (by fun_prop)).integral_eq
  have e4 : ∫ ω, (OMA.kap K (A ω) - Ks) * (B ω / (1 + Ks * B ω)) ∂P
      = (∫ ω, (OMA.kap K (A ω) - Ks) ∂P) * ∫ ω, B ω / (1 + Ks * B ω) ∂P :=
    hind.integral_fun_comp_mul_comp (f := fun x : ℝ => OMA.kap K x - Ks)
      (g := fun y : ℝ => y / (1 + Ks * y)) hA.aemeasurable hB.aemeasurable
      hkm.aestronglyMeasurable (by fun_prop : Measurable fun y : ℝ => y / (1 + Ks * y)).aestronglyMeasurable
  have e5 : ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 * B ω ^ 2 ∂P
      = (∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) * ∫ ω, B ω ^ 2 ∂P :=
    hind.integral_fun_comp_mul_comp (f := fun x : ℝ => (OMA.kap K x - Ks) ^ 2)
      (g := fun y : ℝ => y ^ 2) hA.aemeasurable hB.aemeasurable
      (hkm.pow_const 2).aestronglyMeasurable (by fun_prop : Measurable fun y : ℝ => y ^ 2).aestronglyMeasurable
  rw [e4, e5, e1, e2, e3, hD] at hmono
  have e6 : ∫ ω, Real.log (1 + Ks * A ω) ∂P + ∫ ω, Real.log (1 + Ks * A ω) ∂P + (K - Ks) * 0
      + (∫ ω, (OMA.kap K (A ω) - Ks) ∂P) * 0
      - ((K - Ks) ^ 2 * ∫ ω, A ω ^ 2 ∂P
        + (∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) * ∫ ω, A ω ^ 2 ∂P) / (4 * b ^ 2)
      = 2 * ∫ ω, Real.log (1 + Ks * A ω) ∂P
        - (∫ ω, A ω ^ 2 ∂P) / (4 * b ^ 2)
          * ((K - Ks) ^ 2 + ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P) := by
    ring
  rw [e6] at hmono
  exact hmono

/-- Averaged form of `OMA.bracket_pointwise`. -/
lemma OMA.bracket_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (Ks : ℝ) (hs0 : 0 ≤ Ks) (hs1 : Ks < 1) (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    K ^ 2 * (1 - K) ^ 2 * (∫ ω, A ω ^ 2 ∂P) / (2 * b ^ 2)
      ≤ (K - Ks) ^ 2 + ∫ ω, (OMA.kap K (A ω) - Ks) ^ 2 ∂P := by
  have hkm : Measurable (fun x : ℝ => OMA.kap K x - Ks) := by
    unfold OMA.kap
    fun_prop
  have hiQA := OMA.integrable_sq P A hA b hb hx
  have hiT : Integrable (fun ω => (OMA.kap K (A ω) - Ks) ^ 2) P := by
    refine OMA.intble P _ ((hkm.comp hA).pow_const 2) 1 (fun ω => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    have := abs_le.1 (OMA.drift_bound K Ks (A ω) hK0 hK1 hs0 hs1 (hx ω).1)
    nlinarith
  have hi1 : Integrable (fun ω => K ^ 2 * (1 - K) ^ 2 * A ω ^ 2 / (2 * b ^ 2)) P :=
    (hiQA.const_mul _).div_const _
  have hi2 : Integrable (fun ω => (K - Ks) ^ 2 + (OMA.kap K (A ω) - Ks) ^ 2) P :=
    (integrable_const _).add hiT
  have hmono := integral_mono hi1 hi2 (fun ω =>
    OMA.bracket_pointwise K Ks (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb)
  rw [integral_div, integral_const_mul, integral_add (integrable_const _) hiT,
    integral_const] at hmono
  simpa using hmono

/-- Loomis–Whitney for product probability measures, in marginal form: if `g i` does not depend on
the `i`-th coordinate and the exponents `p` add up to one over all but one index, then integrating
`∏ i, g i ^ p` over any set of coordinates is at most the product of the integrated `g i ^ p`. -/
lemma OMA.lw_marginal {ι : Type} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (g : ι → (ι → ℝ) → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hdep : ∀ i x t, g i (Function.update x i t) = g i x) (p : ℝ) (hp0 : 0 ≤ p)
    (hp : ((Fintype.card ι : ℝ) - 1) * p = 1) (s : Finset ι) :
    ∀ x, (∫⋯∫⁻_s, (fun x => ∏ i, g i x ^ p) ∂μ) x ≤ ∏ i, ((∫⋯∫⁻_s, g i ∂μ) x) ^ p := by
  have hF : Measurable (fun x => ∏ i, g i x ^ p) :=
    Finset.measurable_prod _ fun i _ => (hg i).pow_const p
  induction s using Finset.induction_on with
  | empty =>
    intro x
    simp
  | insert k s hk ih =>
    intro x
    have hG : ∀ i, Measurable (∫⋯∫⁻_s, g i ∂μ) := fun i => (hg i).lmarginal μ
    -- the k-th integrated function does not depend on the k-th coordinate
    have hGk : ∀ t, (∫⋯∫⁻_s, g k ∂μ) (Function.update x k t) = (∫⋯∫⁻_s, g k ∂μ) x := by
      intro t
      rw [lmarginal_update_of_notMem (hg k) hk x t]
      congr 1
      funext z
      exact hdep k z t
    have hcard : ∑ i ∈ Finset.univ.erase k, p = 1 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
        nsmul_eq_mul]
      have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨k⟩
      rw [Nat.cast_sub h1]
      simpa using hp
    calc (∫⋯∫⁻_insert k s, (fun x => ∏ i, g i x ^ p) ∂μ) x
        = ∫⁻ t, (∫⋯∫⁻_s, (fun x => ∏ i, g i x ^ p) ∂μ) (Function.update x k t) ∂μ k :=
          lmarginal_insert _ hF hk x
      _ ≤ ∫⁻ t, ∏ i, ((∫⋯∫⁻_s, g i ∂μ) (Function.update x k t)) ^ p ∂μ k :=
          lintegral_mono fun t => ih _
      _ = ∫⁻ t, ((∫⋯∫⁻_s, g k ∂μ) x) ^ p
            * ∏ i ∈ Finset.univ.erase k, ((∫⋯∫⁻_s, g i ∂μ) (Function.update x k t)) ^ p ∂μ k := by
          congr 1
          funext t
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hGk t]
      _ = ((∫⋯∫⁻_s, g k ∂μ) x) ^ p
            * ∫⁻ t, ∏ i ∈ Finset.univ.erase k,
                ((∫⋯∫⁻_s, g i ∂μ) (Function.update x k t)) ^ p ∂μ k := by
          rw [lintegral_const_mul]
          exact Finset.measurable_prod _ fun i _ =>
            ((hG i).comp (measurable_update x)).pow_const p
      _ ≤ ((∫⋯∫⁻_s, g k ∂μ) x) ^ p
            * ∏ i ∈ Finset.univ.erase k,
                (∫⁻ t, (∫⋯∫⁻_s, g i ∂μ) (Function.update x k t) ∂μ k) ^ p := by
          gcongr
          exact ENNReal.lintegral_prod_norm_pow_le _
            (fun i _ => ((hG i).comp (measurable_update x)).aemeasurable) hcard (fun _ _ => hp0)
      _ = ∏ i, ((∫⋯∫⁻_insert k s, g i ∂μ) x) ^ p := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
          congr 1
          · rw [lmarginal_insert _ (hg k) hk x]
            simp [hGk]
          · refine Finset.prod_congr rfl fun i _ => ?_
            rw [lmarginal_insert _ (hg i) hk x]

/-- Loomis–Whitney for product probability measures. -/
lemma OMA.lw {ι : Type} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (g : ι → (ι → ℝ) → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hdep : ∀ i x t, g i (Function.update x i t) = g i x) (p : ℝ) (hp0 : 0 ≤ p)
    (hp : ((Fintype.card ι : ℝ) - 1) * p = 1) :
    ∫⁻ x, ∏ i, g i x ^ p ∂Measure.pi μ ≤ ∏ i, (∫⁻ x, g i x ∂Measure.pi μ) ^ p := by
  have h := OMA.lw_marginal μ g hg hdep p hp0 hp Finset.univ (fun _ => 0)
  simpa using h

/-- Returns clamped to `[-1, b - 1]`; on the support of the returns this is the identity. -/
noncomputable def OMA.clamp (b t : ℝ) : ℝ := max (-1) (min t (b - 1))

lemma OMA.clamp_bounds (b t : ℝ) (hb : 1 ≤ b) : -1 ≤ OMA.clamp b t ∧ OMA.clamp b t ≤ b - 1 := by
  unfold OMA.clamp
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma OMA.clamp_eq (b t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ b - 1) : OMA.clamp b t = t := by
  unfold OMA.clamp
  rw [min_eq_left h2, max_eq_right h1]

lemma OMA.measurable_clamp (b : ℝ) : Measurable (OMA.clamp b) := by
  unfold OMA.clamp
  exact measurable_const.max (measurable_id.min measurable_const)

/-- The total return of a tuple of (clamped) one-period returns. -/
noncomputable def OMA.tot (b : ℝ) {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  (∏ i, (1 + OMA.clamp b (z i))) - 1

lemma OMA.measurable_tot (b : ℝ) (m : ℕ) : Measurable (OMA.tot b : (Fin m → ℝ) → ℝ) := by
  unfold OMA.tot
  refine (Finset.measurable_prod _ fun i _ => ?_).sub_const 1
  exact measurable_const.add ((OMA.measurable_clamp b).comp (measurable_pi_apply i))

lemma OMA.tot_bounds (b : ℝ) (hb : 1 ≤ b) {m : ℕ} (z : Fin m → ℝ) :
    -1 ≤ OMA.tot b z ∧ OMA.tot b z ≤ b ^ m - 1 := by
  unfold OMA.tot
  have h0 : ∀ i, 0 ≤ 1 + OMA.clamp b (z i) := fun i => by
    linarith [(OMA.clamp_bounds b (z i) hb).1]
  have h1 : ∀ i, 1 + OMA.clamp b (z i) ≤ b := fun i => by
    linarith [(OMA.clamp_bounds b (z i) hb).2]
  constructor
  · linarith [Finset.prod_nonneg (s := Finset.univ) fun i _ => h0 i]
  · have h := Finset.prod_le_prod (s := Finset.univ) (fun i _ => h0 i) (fun i _ => h1 i)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    linarith

/-- Dropping one coordinate maps the `(n+1)`-fold product measure to the `n`-fold one. -/
lemma OMA.integral_remove (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (j : Fin (n + 1))
    (Φ : (Fin n → ℝ) → ℝ) (hΦ : Measurable Φ) :
    ∫ x, Φ (fun i => x (j.succAbove i)) ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫ z, Φ z ∂(Measure.pi fun _ : Fin n => μ) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j
  have hmeas : Measurable (fun x : Fin (n + 1) → ℝ => (fun i : Fin n => x (j.succAbove i))) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have h2 : Measure.map (fun x : Fin (n + 1) → ℝ => (fun i : Fin n => x (j.succAbove i)))
      (Measure.pi fun _ : Fin (n + 1) => μ) = Measure.pi fun _ : Fin n => μ := by
    have h3 : (fun x : Fin (n + 1) → ℝ => (fun i : Fin n => x (j.succAbove i)))
        = Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j) := by
      funext x
      rfl
    rw [h3, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _), h1.map_eq,
      Measure.map_snd_prod]
    simp
  rw [← h2, integral_map hmeas.aemeasurable hΦ.aestronglyMeasurable]

/-- The joint law of the first `m` returns is the `m`-fold product of the law of one return. -/
lemma OMA.integral_iid {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P) (m : ℕ) (Φ : (Fin m → ℝ) → ℝ)
    (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun i : Fin m => X i ω) ∂P = ∫ z, Φ z ∂(Measure.pi fun _ : Fin m => P.map (X 0)) := by
  have h1 : iIndepFun (fun i : Fin m => X i) P := hindep.precomp Fin.val_injective
  have h2 := (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin m => (hm i).aemeasurable)).1 h1
  have h3 : (fun i : Fin m => P.map (X i)) = fun _ => P.map (X 0) := by
    funext i
    exact (hident i).map_eq
  rw [h3] at h2
  have hmeas : Measurable (fun ω => (fun i : Fin m => X i ω)) :=
    measurable_pi_iff.2 fun i => hm i
  rw [← h2, integral_map hmeas.aemeasurable hΦ.aestronglyMeasurable]

/-- The product of all the leave-one-out products is the `n`-th power of the full product. -/
lemma OMA.prod_leave_one_out (n : ℕ) (y : Fin (n + 1) → ℝ) :
    ∏ j : Fin (n + 1), ∏ i : Fin n, y (j.succAbove i) = (∏ j, y j) ^ n := by
  have h1 : ∀ j : Fin (n + 1), ∏ i : Fin n, y (j.succAbove i) = ∏ i ∈ Finset.univ.erase j, y i := by
    intro j
    rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
      Finset.prod_image (fun a _ b _ h => Fin.succAbove_right_injective h)]
  simp_rw [h1]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.erase i)]
  · simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
    rw [Finset.prod_pow]
  · intro j i
    simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, true_and, and_true]
    exact ⟨fun h => fun h' => h h'.symm, fun h => fun h' => h h'.symm⟩

/-- Loomis–Whitney in real form, for bounded nonnegative functions with integral at most one. -/
lemma OMA.lw_real (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (hn : 1 ≤ n)
    (u : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hu : ∀ j, Measurable (u j))
    (hu0 : ∀ j x, 0 ≤ u j x) (C : ℝ) (huC : ∀ j x, u j x ≤ C)
    (hdep : ∀ j x t, u j (Function.update x j t) = u j x)
    (hint : ∀ j, ∫ x, u j x ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤ 1) :
    Integrable (fun x => ∏ j, (u j x) ^ ((n : ℝ)⁻¹)) (Measure.pi fun _ : Fin (n + 1) => μ)
      ∧ ∫ x, ∏ j, (u j x) ^ ((n : ℝ)⁻¹) ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 hn0.le
  have hC0 : 0 ≤ C := le_trans (hu0 0 fun _ => 0) (huC 0 fun _ => 0)
  have hiu : ∀ j, Integrable (u j) (Measure.pi fun _ : Fin (n + 1) => μ) := fun j =>
    Integrable.of_mem_Icc 0 C (hu j).aemeasurable
      (Filter.Eventually.of_forall fun x => ⟨hu0 j x, huC j x⟩)
  have hFm : Measurable (fun x => ∏ j, (u j x) ^ ((n : ℝ)⁻¹)) :=
    Finset.measurable_prod _ fun j _ => (hu j).pow_const _
  have hF0 : ∀ x, 0 ≤ ∏ j, (u j x) ^ ((n : ℝ)⁻¹) := fun x =>
    Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hu0 j x) _
  have hFC : ∀ x, ∏ j, (u j x) ^ ((n : ℝ)⁻¹) ≤ ∏ _j : Fin (n + 1), C ^ ((n : ℝ)⁻¹) := fun x =>
    Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (hu0 j x) _)
      (fun j _ => Real.rpow_le_rpow (hu0 j x) (huC j x) hp0)
  have hiF : Integrable (fun x => ∏ j, (u j x) ^ ((n : ℝ)⁻¹))
      (Measure.pi fun _ : Fin (n + 1) => μ) :=
    Integrable.of_mem_Icc 0 _ hFm.aemeasurable
      (Filter.Eventually.of_forall fun x => ⟨hF0 x, hFC x⟩)
  have hcard : ((Fintype.card (Fin (n + 1)) : ℝ) - 1) * (n : ℝ)⁻¹ = 1 := by
    rw [Fintype.card_fin]
    push_cast
    rw [add_sub_cancel_right]
    exact mul_inv_cancel₀ hn0.ne'
  have hlw := OMA.lw (fun _ : Fin (n + 1) => μ) (fun j x => ENNReal.ofReal (u j x))
    (fun j => ENNReal.measurable_ofReal.comp (hu j))
    (fun j x t => by rw [hdep j x t]) ((n : ℝ)⁻¹) hp0 hcard
  have hrhs : ∏ j : Fin (n + 1), (∫⁻ x, ENNReal.ofReal (u j x)
      ∂(Measure.pi fun _ : Fin (n + 1) => μ)) ^ ((n : ℝ)⁻¹) ≤ 1 := by
    refine Finset.prod_le_one' fun j _ => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hiu j) (Filter.Eventually.of_forall (hu0 j))]
    exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (hint j)) hp0
  have hlhs : ∀ x, ENNReal.ofReal (∏ j, (u j x) ^ ((n : ℝ)⁻¹))
      = ∏ j, (ENNReal.ofReal (u j x)) ^ ((n : ℝ)⁻¹) := by
    intro x
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ => Real.rpow_nonneg (hu0 j x) _]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (hu0 j x) hp0]
  refine ⟨hiF, ?_⟩
  rw [← ENNReal.ofReal_le_one, ofReal_integral_eq_lintegral_ofReal hiF
    (Filter.Eventually.of_forall hF0)]
  simp_rw [hlhs]
  exact hlw.trans hrhs

/-- The logarithm of a positive number is controlled by any positive "pricing kernel"
`∏ j, (1 / c j) ^ p`. -/
lemma OMA.log_le_cert (n : ℕ) (W : ℝ) (hW : 0 < W) (c : Fin (n + 1) → ℝ) (hc : ∀ j, 0 < c j)
    (p : ℝ) :
    Real.log W ≤ W * ∏ j, (1 / c j) ^ p - 1 + p * ∑ j, Real.log (c j) := by
  have hF : 0 < ∏ j, (1 / c j) ^ p :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (one_div_pos.2 (hc j)) p
  have h1 := Real.log_le_sub_one_of_pos (mul_pos hW hF)
  rw [Real.log_mul hW.ne' hF.ne', Real.log_prod (fun j _ =>
    (Real.rpow_pos_of_pos (one_div_pos.2 (hc j)) p).ne')] at h1
  have h2 : ∑ j, Real.log ((1 / c j) ^ p) = -(p * ∑ j, Real.log (c j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.log_rpow (one_div_pos.2 (hc j)), one_div, Real.log_inv]
    ring
  rw [h2] at h1
  linarith

/-- The total return over the periods other than `j`. -/
noncomputable def OMA.totj (b : ℝ) {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ℝ :=
  OMA.tot b (fun i => x (j.succAbove i))

lemma OMA.measurable_totj (b : ℝ) {n : ℕ} (j : Fin (n + 1)) : Measurable (OMA.totj b j) :=
  (OMA.measurable_tot b n).comp (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

lemma OMA.totj_bounds (b : ℝ) (hb : 1 ≤ b) {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    -1 ≤ OMA.totj b j x ∧ OMA.totj b j x ≤ b ^ n - 1 :=
  OMA.tot_bounds b hb _

lemma OMA.totj_update (b : ℝ) {n : ℕ} (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    OMA.totj b j (Function.update x j t) = OMA.totj b j x := by
  unfold OMA.totj
  congr 1
  funext i
  exact Function.update_of_ne (Fin.succAbove_ne j i) _ _

lemma OMA.prod_totj (b : ℝ) {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∏ j : Fin (n + 1), (1 + OMA.totj b j x) = (1 + OMA.tot b x) ^ n := by
  have h := OMA.prod_leave_one_out n (fun i => 1 + OMA.clamp b (x i))
  unfold OMA.totj OMA.tot
  simpa using h

/-- Integrating the pointwise bound: two kernels of integral at most one and `m` logarithmic
terms with the same integral. -/
lemma OMA.core_integrate {α : Type} [MeasurableSpace α] (π : Measure α) [IsProbabilityMeasure π]
    (m : ℕ) (L F G : α → ℝ) (Lj : Fin m → α → ℝ) (K' c p ℓ : ℝ) (hK'0 : 0 ≤ K') (hK'1 : K' ≤ 1)
    (hiL : Integrable L π) (hiF : Integrable F π) (hiG : Integrable G π)
    (hiLj : ∀ j, Integrable (Lj j) π) (hF : ∫ x, F x ∂π ≤ 1) (hG : ∫ x, G x ∂π ≤ 1)
    (hLj : ∀ j, ∫ x, Lj j x ∂π = ℓ)
    (key : ∀ x, L x ≤ (1 - K') * F x + K' * G x - 1 + p * ∑ j, (c + Lj j x)) :
    ∫ x, L x ∂π ≤ p * ((m : ℝ) * (c + ℓ)) := by
  have hic : ∀ j : Fin m, Integrable (fun x => c + Lj j x) π := fun j =>
    (integrable_const c).add (hiLj j)
  have hiS : Integrable (fun x => ∑ j, (c + Lj j x)) π :=
    integrable_finsetSum _ fun j _ => hic j
  have hS : ∫ x, ∑ j, (c + Lj j x) ∂π = (m : ℝ) * (c + ℓ) := by
    rw [integral_finsetSum _ fun j _ => hic j]
    have h : ∀ j : Fin m, ∫ x, (c + Lj j x) ∂π = c + ℓ := by
      intro j
      rw [integral_add (integrable_const c) (hiLj j), integral_const, probReal_univ, one_smul,
        hLj j]
    simp_rw [h]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hi1 : Integrable (fun x => (1 - K') * F x) π := hiF.const_mul _
  have hi2 : Integrable (fun x => K' * G x) π := hiG.const_mul _
  have hi3 : Integrable (fun x => (1 - K') * F x + K' * G x) π := hi1.add hi2
  have hi4 : Integrable (fun x => (1 - K') * F x + K' * G x - 1) π :=
    hi3.sub (integrable_const 1)
  have hi5 : Integrable (fun x => p * ∑ j, (c + Lj j x)) π := hiS.const_mul _
  have hmono : ∫ x, L x ∂π
      ≤ ∫ x, ((1 - K') * F x + K' * G x - 1 + p * ∑ j, (c + Lj j x)) ∂π :=
    integral_mono hiL (hi4.add hi5) key
  rw [integral_add hi4 hi5, integral_sub hi3 (integrable_const 1), integral_add hi1 hi2,
    integral_const_mul, integral_const_mul, integral_const_mul, hS, integral_const, probReal_univ,
    one_smul] at hmono
  have h1 := mul_le_mul_of_nonneg_left hF (sub_nonneg.2 hK'1)
  have h2 := mul_le_mul_of_nonneg_left hG hK'0
  linarith

/-- The main inequality behind Conjecture 1, on product measures: a fraction `K` for `n` periods
whose reciprocal wealth prices cash and the `n`-period bet at most `1 + ε` bounds the growth of
every fraction `K'` held for `n + 1` periods. -/
lemma OMA.core (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) (hb : 1 ≤ b) (n : ℕ) (hn : 1 ≤ n)
    (K K' ε : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hK'0 : 0 ≤ K') (hK'1 : K' < 1) (hε : 0 ≤ ε)
    (h1 : ∫ z, 1 / (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ) ≤ 1 + ε)
    (h2 : ∫ z, (1 + OMA.tot b z) / (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ)
      ≤ 1 + ε) :
    ∫ x, Real.log (1 + K' * OMA.tot b x) ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      ≤ ((n : ℝ) + 1) / n
        * (∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ)
          + Real.log (1 + ε)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : n ≠ 0 := by omega
  have hp0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 hn0.le
  have hB : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb
  have hB1 : (1 : ℝ) ≤ b ^ (n + 1) := one_le_pow₀ hb
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hmt : Measurable (OMA.tot b : (Fin n → ℝ) → ℝ) := OMA.measurable_tot b n
  have hmt1 : Measurable (OMA.tot b : (Fin (n + 1) → ℝ) → ℝ) := OMA.measurable_tot b (n + 1)
  have hmj : ∀ j : Fin (n + 1), Measurable (OMA.totj b j) := fun j => OMA.measurable_totj b j
  have hT : ∀ (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      -1 ≤ OMA.totj b j x ∧ OMA.totj b j x ≤ b ^ n - 1 := fun j x => OMA.totj_bounds b hb j x
  have hW : ∀ (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      1 - K ≤ 1 + K * OMA.totj b j x ∧ 1 + K * OMA.totj b j x ≤ b ^ n := fun j x =>
    OMA.factor_bounds K _ (b ^ n) hK0 hK1 (hT j x).1 (hT j x).2 hB
  have hc : ∀ (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      0 < (1 + ε) * (1 + K * OMA.totj b j x) := fun j x =>
    mul_pos hε1 (by linarith [(hW j x).1])
  have hcge : ∀ (j : Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      1 - K ≤ (1 + ε) * (1 + K * OMA.totj b j x) := fun j x => by
    nlinarith [(hW j x).1, mul_nonneg hε (by linarith [(hW j x).1] :
      (0 : ℝ) ≤ 1 + K * OMA.totj b j x)]
  -- each leave-one-out certificate has integral at most one
  have hu1 : ∀ j : Fin (n + 1), ∫ x, 1 / ((1 + ε) * (1 + K * OMA.totj b j x))
      ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤ 1 := by
    intro j
    calc ∫ x, 1 / ((1 + ε) * (1 + K * OMA.totj b j x)) ∂(Measure.pi fun _ : Fin (n + 1) => μ)
        = ∫ z, 1 / ((1 + ε) * (1 + K * OMA.tot b z)) ∂(Measure.pi fun _ : Fin n => μ) :=
          OMA.integral_remove μ n j (fun z => 1 / ((1 + ε) * (1 + K * OMA.tot b z)))
            (by fun_prop)
      _ = (1 + ε)⁻¹ * ∫ z, 1 / (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ) := by
          rw [← integral_const_mul]
          congr 1
          funext z
          rw [one_div, mul_inv, one_div]
      _ ≤ 1 := by
          rw [inv_mul_le_iff₀ hε1]
          linarith
  have hv1 : ∀ j : Fin (n + 1), ∫ x, (1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x))
      ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤ 1 := by
    intro j
    calc ∫ x, (1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x))
          ∂(Measure.pi fun _ : Fin (n + 1) => μ)
        = ∫ z, (1 + OMA.tot b z) / ((1 + ε) * (1 + K * OMA.tot b z))
            ∂(Measure.pi fun _ : Fin n => μ) :=
          OMA.integral_remove μ n j
            (fun z => (1 + OMA.tot b z) / ((1 + ε) * (1 + K * OMA.tot b z))) (by fun_prop)
      _ = (1 + ε)⁻¹ * ∫ z, (1 + OMA.tot b z) / (1 + K * OMA.tot b z)
            ∂(Measure.pi fun _ : Fin n => μ) := by
          rw [← integral_const_mul]
          congr 1
          funext z
          rw [div_mul_eq_div_div_swap, div_eq_inv_mul]
      _ ≤ 1 := by
          rw [inv_mul_le_iff₀ hε1]
          linarith
  -- Loomis–Whitney for the two families
  obtain ⟨hiF, hF⟩ := OMA.lw_real μ n hn (fun j x => 1 / ((1 + ε) * (1 + K * OMA.totj b j x)))
    (fun j => by have := hmj j; fun_prop)
    (fun j x => (one_div_pos.2 (hc j x)).le) (1 / (1 - K))
    (fun j x => one_div_le_one_div_of_le (by linarith) (hcge j x))
    (fun j x t => by rw [OMA.totj_update]) hu1
  obtain ⟨hiG, hG⟩ := OMA.lw_real μ n hn
    (fun j x => (1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x)))
    (fun j => by have := hmj j; fun_prop)
    (fun j x => div_nonneg (by linarith [(hT j x).1]) (hc j x).le) (b ^ n / (1 - K))
    (fun j x => div_le_div₀ (by linarith) (by linarith [(hT j x).2]) (by linarith) (hcge j x))
    (fun j x t => by rw [OMA.totj_update]) hv1
  -- the second kernel is the first one times the total gross return
  have hGF : ∀ x : Fin (n + 1) → ℝ,
      ∏ j, ((1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹)
        = (1 + OMA.tot b x) * ∏ j, (1 / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹) := by
    intro x
    have h0 : 0 ≤ 1 + OMA.tot b x := by linarith [(OMA.tot_bounds b hb x).1]
    have e1 : ∀ j : Fin (n + 1),
        ((1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹)
          = (1 + OMA.totj b j x) ^ ((n : ℝ)⁻¹)
            * (1 / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹) := by
      intro j
      rw [div_eq_mul_one_div, Real.mul_rpow (by linarith [(hT j x).1])
        (one_div_pos.2 (hc j x)).le]
    simp_rw [e1]
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun j _ => by linarith [(hT j x).1]),
      OMA.prod_totj, Real.pow_rpow_inv_natCast h0 hnne]
  -- pointwise bound for the logarithm of the (n+1)-period wealth
  have key : ∀ x : Fin (n + 1) → ℝ, Real.log (1 + K' * OMA.tot b x)
      ≤ (1 - K') * ∏ j, (1 / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹)
        + K' * ∏ j, ((1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹)
        - 1
        + (n : ℝ)⁻¹ * ∑ j : Fin (n + 1), (Real.log (1 + ε) + Real.log (1 + K * OMA.totj b j x)) := by
    intro x
    have hWx := OMA.factor_bounds K' (OMA.tot b x) (b ^ (n + 1)) hK'0 hK'1
      (OMA.tot_bounds b hb x).1 (OMA.tot_bounds b hb x).2 hB1
    have h := OMA.log_le_cert n (1 + K' * OMA.tot b x) (by linarith [hWx.1])
      (fun j => (1 + ε) * (1 + K * OMA.totj b j x)) (fun j => hc j x) ((n : ℝ)⁻¹)
    have e2 : ∑ j : Fin (n + 1), Real.log ((1 + ε) * (1 + K * OMA.totj b j x))
        = ∑ j : Fin (n + 1), (Real.log (1 + ε) + Real.log (1 + K * OMA.totj b j x)) :=
      Finset.sum_congr rfl fun j _ =>
        Real.log_mul hε1.ne' (by linarith [(hW j x).1] : (1 + K * OMA.totj b j x) ≠ 0)
    rw [e2] at h
    rw [hGF x]
    linarith
  have hiL' : Integrable (fun x : Fin (n + 1) → ℝ => Real.log (1 + K' * OMA.tot b x))
      (Measure.pi fun _ : Fin (n + 1) => μ) :=
    OMA.integrable_log _ _ hmt1 (b ^ (n + 1)) hB1 (fun x => OMA.tot_bounds b hb x) K' hK'0 hK'1
  have hiLj : ∀ j : Fin (n + 1), Integrable (fun x : Fin (n + 1) → ℝ =>
      Real.log (1 + K * OMA.totj b j x)) (Measure.pi fun _ : Fin (n + 1) => μ) := fun j =>
    OMA.integrable_log _ _ (hmj j) (b ^ n) hB (fun x => hT j x) K hK0 hK1
  have hLj : ∀ j : Fin (n + 1), ∫ x, Real.log (1 + K * OMA.totj b j x)
      ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ) := fun j =>
    OMA.integral_remove μ n j (fun z => Real.log (1 + K * OMA.tot b z)) (by fun_prop)
  have hfin := OMA.core_integrate (Measure.pi fun _ : Fin (n + 1) => μ) (n + 1)
    (fun x => Real.log (1 + K' * OMA.tot b x))
    (fun x => ∏ j, (1 / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹))
    (fun x => ∏ j, ((1 + OMA.totj b j x) / ((1 + ε) * (1 + K * OMA.totj b j x))) ^ ((n : ℝ)⁻¹))
    (fun j x => Real.log (1 + K * OMA.totj b j x)) K' (Real.log (1 + ε)) ((n : ℝ)⁻¹)
    (∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ))
    hK'0 hK'1.le hiL' hiF hiG hiLj hF hG hLj key
  refine hfin.trans (le_of_eq ?_)
  push_cast
  ring

/-- Reciprocal wealth and discounted gross return in terms of the marginal growth rate. -/
lemma OMA.cert_pointwise (K x : ℝ) (hw : 1 + K * x ≠ 0) :
    1 / (1 + K * x) = 1 - K * (x / (1 + K * x))
      ∧ (1 + x) / (1 + K * x) = 1 + (1 - K) * (x / (1 + K * x)) := by
  have hq : x / (1 + K * x) * (1 + K * x) = x := div_mul_cancel₀ x hw
  constructor
  · rw [eq_sub_iff_add_eq, ← mul_div_assoc, ← add_div]
    exact div_self hw
  · rw [div_eq_iff hw]
    linear_combination (-(1 - K)) * hq

/-- The two certificate integrals in terms of the marginal growth rate. -/
lemma OMA.cert_integrals {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∫ ω, 1 / (1 + K * A ω) ∂P = 1 - K * ∫ ω, A ω / (1 + K * A ω) ∂P
      ∧ ∫ ω, (1 + A ω) / (1 + K * A ω) ∂P = 1 + (1 - K) * ∫ ω, A ω / (1 + K * A ω) ∂P := by
  have hi := OMA.integrable_ratio P A hA b hb hx K hK0 hK1
  have hpos : ∀ ω, 0 < 1 + K * A ω := fun ω => by
    have := (OMA.factor_bounds K (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb).1
    linarith
  constructor
  · have e : ∀ ω, 1 / (1 + K * A ω) = 1 - K * (A ω / (1 + K * A ω)) := fun ω =>
      (OMA.cert_pointwise K (A ω) (hpos ω).ne').1
    simp_rw [e]
    rw [integral_sub (integrable_const 1) (hi.const_mul K), integral_const_mul, integral_const,
      probReal_univ, one_smul]
  · have e : ∀ ω, (1 + A ω) / (1 + K * A ω) = 1 + (1 - K) * (A ω / (1 + K * A ω)) := fun ω =>
      (OMA.cert_pointwise K (A ω) (hpos ω).ne').2
    simp_rw [e]
    rw [integral_add (integrable_const 1) (hi.const_mul (1 - K)), integral_const_mul,
      integral_const, probReal_univ, one_smul]

/-- For every `ε > 0` some fraction in `[0, 1)` has a reciprocal wealth that prices both cash and
the bet at no more than `1 + ε`. -/
lemma OMA.exists_cert {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (b : ℝ) (hb : 1 ≤ b) (hx : ∀ ω, -1 ≤ A ω ∧ A ω ≤ b - 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧ ∫ ω, 1 / (1 + K * A ω) ∂P ≤ 1 + ε
      ∧ ∫ ω, (1 + A ω) / (1 + K * A ω) ∂P ≤ 1 + ε := by
  by_cases h : ∃ K1 : ℝ, 0 ≤ K1 ∧ K1 < 1 ∧ ∫ ω, A ω / (1 + K1 * A ω) ∂P ≤ 0
  · obtain ⟨K1, hK10, hK11, hD1⟩ := h
    by_cases h0 : ∫ ω, A ω / (1 + 0 * A ω) ∂P ≤ 0
    · obtain ⟨e1, e2⟩ := OMA.cert_integrals P A hA b hb hx 0 le_rfl zero_lt_one
      refine ⟨0, le_rfl, zero_lt_one, ?_, ?_⟩
      · rw [e1]
        linarith
      · rw [e2]
        linarith
    · have hcont := OMA.continuousOn_D P A hA b hb hx K1 hK11
      have hmem : (0 : ℝ) ∈ Set.Icc ((fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) K1)
          ((fun K : ℝ => ∫ ω, A ω / (1 + K * A ω) ∂P) 0) := ⟨hD1, (not_le.1 h0).le⟩
      obtain ⟨Ks, hKs, hDs⟩ := intermediate_value_Icc' hK10 hcont hmem
      have hDs' : ∫ ω, A ω / (1 + Ks * A ω) ∂P = 0 := hDs
      obtain ⟨e1, e2⟩ := OMA.cert_integrals P A hA b hb hx Ks hKs.1 (lt_of_le_of_lt hKs.2 hK11)
      refine ⟨Ks, hKs.1, lt_of_le_of_lt hKs.2 hK11, ?_, ?_⟩
      · rw [e1, hDs']
        linarith
      · rw [e2, hDs']
        linarith
  · push Not at h
    have hb0 : 0 < b := by linarith
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max (1 / 2) (1 - ε / b) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact le_trans (by norm_num) (le_max_left _ _)
    have hK1 : K < 1 := by
      rw [hKdef]
      exact max_lt (by norm_num) (by linarith [div_pos hε hb0])
    have hKε : 1 - K ≤ ε / b := by
      rw [hKdef]
      linarith [le_max_right (1 / 2 : ℝ) (1 - ε / b)]
    obtain ⟨e1, e2⟩ := OMA.cert_integrals P A hA b hb hx K hK0 hK1
    have hD0 := h K hK0 hK1
    have hDb : ∫ ω, A ω / (1 + K * A ω) ∂P ≤ b - 1 := by
      have hle : ∀ ω, A ω / (1 + K * A ω) ≤ b - 1 := fun ω => by
        have hw := (OMA.factor_bounds K (A ω) b hK0 hK1 (hx ω).1 (hx ω).2 hb).1
        have hw0 : 0 < 1 + K * A ω := by linarith
        rw [div_le_iff₀ hw0]
        rcases le_or_gt 0 (A ω) with h' | h'
        · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hK0) h', (hx ω).2]
        · nlinarith [mul_nonneg (sub_nonneg.2 hb) hw0.le]
      have h3 := integral_mono (OMA.integrable_ratio P A hA b hb hx K hK0 hK1)
        (integrable_const (b - 1)) hle
      rwa [integral_const, probReal_univ, one_smul] at h3
    refine ⟨K, hK0, hK1, ?_, ?_⟩
    · rw [e1]
      linarith [mul_nonneg hK0 hD0.le]
    · rw [e2]
      have h2 : (1 - K) * ∫ ω, A ω / (1 + K * A ω) ∂P ≤ ε / b * (b - 1) :=
        mul_le_mul hKε hDb hD0.le (div_pos hε hb0).le
      have h3 : ε / b * (b - 1) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
        nlinarith
      linarith

/-- Conjecture 1 on product measures, up to `ε`: every fraction for `n + 1` periods is matched
by a fraction for `n` periods. -/
lemma OMA.core_sup (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) (hb : 1 ≤ b) (n : ℕ)
    (hn : 1 ≤ n) (K' : ℝ) (hK'0 : 0 ≤ K') (hK'1 : K' < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧
      1 / ((n : ℝ) + 1) * ∫ x, Real.log (1 + K' * OMA.tot b x)
          ∂(Measure.pi fun _ : Fin (n + 1) => μ)
        ≤ 1 / (n : ℝ) * ∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ)
          + ε := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hpos' : (n : ℝ) + 1 ≠ 0 := hpos.ne'
  obtain ⟨K, hK0, hK1, h1, h2⟩ := OMA.exists_cert (Measure.pi fun _ : Fin n => μ) (OMA.tot b)
    (OMA.measurable_tot b n) (b ^ n) (one_le_pow₀ hb) (fun z => OMA.tot_bounds b hb z) ε hε
  refine ⟨K, hK0, hK1, ?_⟩
  have hc := OMA.core μ b hb n hn K K' ε hK0 hK1 hK'0 hK'1 hε.le h1 h2
  have hlog : Real.log (1 + ε) ≤ ε := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ε)
    linarith
  have h3 : 1 / (n : ℝ) * Real.log (1 + ε) ≤ 1 * ε := by
    refine mul_le_mul ?_ hlog (Real.log_nonneg (by linarith)) zero_le_one
    rw [div_le_one hn0]
    exact hn1
  calc 1 / ((n : ℝ) + 1) * ∫ x, Real.log (1 + K' * OMA.tot b x)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      ≤ 1 / ((n : ℝ) + 1) * (((n : ℝ) + 1) / n
          * (∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ)
            + Real.log (1 + ε))) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 1 / (n : ℝ) * ∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ)
          + 1 / (n : ℝ) * Real.log (1 + ε) := by
        field_simp
    _ ≤ 1 / (n : ℝ) * ∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => μ)
          + ε := by
        linarith

/-- The total return of the statement is the product-space total return of the sample. -/
lemma OMA.totalReturn_eq_tot {Ω : Type} (X : ℕ → Ω → ℝ) (b : ℝ)
    (hXb : ∀ k ω, -1 ≤ X k ω ∧ X k ω ≤ b - 1) (m : ℕ) (ω : Ω) :
    OMA.S_arxiv_1801_06737.totalReturn X m ω = OMA.tot b (fun i : Fin m => X i ω) := by
  unfold OMA.S_arxiv_1801_06737.totalReturn OMA.tot
  rw [← Fin.prod_univ_eq_prod_range (fun k => 1 + X k ω) m]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [OMA.clamp_eq b _ (hXb i ω).1 (hXb i ω).2]

/-- Expectations of functions of the `m`-period total return, computed on the product space. -/
lemma OMA.transfer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P) (b : ℝ)
    (hXb : ∀ k ω, -1 ≤ X k ω ∧ X k ω ≤ b - 1) (m : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫ ω, φ (OMA.S_arxiv_1801_06737.totalReturn X m ω) ∂P
      = ∫ z, φ (OMA.tot b z) ∂(Measure.pi fun _ : Fin m => P.map (X 0)) := by
  simp_rw [OMA.totalReturn_eq_tot X b hXb m]
  exact OMA.integral_iid P X hm hindep hident m (fun z => φ (OMA.tot b z))
    (hφ.comp (OMA.measurable_tot b m))

/-- Conjecture 1 of the paper: the optimal expected logarithmic growth does not increase when the
fraction is rebalanced less often. -/
lemma OMA.conj1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P) (b : ℝ) (hb : 1 ≤ b)
    (hXb : ∀ k ω, -1 ≤ X k ω ∧ X k ω ≤ b - 1) (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_arxiv_1801_06737.gStar P X (n + 1) ≤ OMA.S_arxiv_1801_06737.gStar P X n := by
  have hμ : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hm 0).aemeasurable
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb
  have hg : ∀ (m : ℕ) (K : ℝ), OMA.S_arxiv_1801_06737.g P X m K
      = 1 / (m : ℝ) * ∫ z, Real.log (1 + K * OMA.tot b z)
          ∂(Measure.pi fun _ : Fin m => P.map (X 0)) := by
    intro m K
    unfold OMA.S_arxiv_1801_06737.g
    rw [OMA.transfer P X hm hindep hident b hXb m (fun t => Real.log (1 + K * t)) (by fun_prop)]
  have hbdd : BddAbove (Set.range fun K : Set.Ico (0 : ℝ) 1 =>
      OMA.S_arxiv_1801_06737.g P X n K) := by
    refine ⟨1 / (n : ℝ) * Real.log (b ^ n), ?_⟩
    rintro _ ⟨⟨K, hK0, hK1⟩, rfl⟩
    show OMA.S_arxiv_1801_06737.g P X n K ≤ 1 / (n : ℝ) * Real.log (b ^ n)
    rw [hg]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∫ z, Real.log (1 + K * OMA.tot b z) ∂(Measure.pi fun _ : Fin n => P.map (X 0))
        ≤ ∫ _z, Real.log (b ^ n) ∂(Measure.pi fun _ : Fin n => P.map (X 0)) :=
          integral_mono (OMA.integrable_log _ _ (OMA.measurable_tot b n) (b ^ n) hB
            (fun z => OMA.tot_bounds b hb z) K hK0 hK1) (integrable_const _) (fun z => by
              obtain ⟨h1, h2⟩ := OMA.factor_bounds K (OMA.tot b z) (b ^ n) hK0 hK1
                (OMA.tot_bounds b hb z).1 (OMA.tot_bounds b hb z).2 hB
              exact Real.log_le_log (by linarith) h2)
      _ = Real.log (b ^ n) := by rw [integral_const, probReal_univ, one_smul]
  unfold OMA.S_arxiv_1801_06737.gStar
  have hne : Nonempty (Set.Ico (0 : ℝ) 1) := ⟨⟨0, Set.left_mem_Ico.2 zero_lt_one⟩⟩
  refine ciSup_le fun K' => ?_
  obtain ⟨K', hK'0, hK'1⟩ := K'
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨K, hK0, hK1, h⟩ := OMA.core_sup (P.map (X 0)) b hb n hn K' hK'0 hK'1 ε hε
  have h1 : OMA.S_arxiv_1801_06737.g P X (n + 1) K' ≤ OMA.S_arxiv_1801_06737.g P X n K + ε := by
    rw [hg, hg, Nat.cast_add_one]
    exact h
  have h2 : OMA.S_arxiv_1801_06737.g P X n K
      ≤ ⨆ K : Set.Ico (0 : ℝ) 1, OMA.S_arxiv_1801_06737.g P X n K :=
    le_ciSup hbdd ⟨K, hK0, hK1⟩
  exact h1.trans (by linarith)

theorem OMA.solution : type_of% @OMA.S_arxiv_1801_06737.main := by
  intro Ω _ P _ X Xmin Xmax hm hindep hident hmin1 hmin0 hmax0 hbd hsmin hsmax hEX
  have hb : (1 : ℝ) ≤ 1 + Xmax := by linarith
  refine ⟨fun n hn => OMA.conj1 P X hm hindep hident (1 + Xmax) hb
    (fun k ω => ⟨by linarith [(hbd k ω).1], by linarith [(hbd k ω).2]⟩) n hn, ?_⟩
  intro hall
  by_contra hSA
  rw [not_le] at hSA
  have hb0 : (0 : ℝ) < 1 + Xmax := by linarith
  have hxA : ∀ ω, -1 ≤ X 0 ω ∧ X 0 ω ≤ (1 + Xmax) - 1 := fun ω =>
    ⟨by linarith [(hbd 0 ω).1], by linarith [(hbd 0 ω).2]⟩
  have hxB : ∀ ω, -1 ≤ X 1 ω ∧ X 1 ω ≤ (1 + Xmax) - 1 := fun ω =>
    ⟨by linarith [(hbd 1 ω).1], by linarith [(hbd 1 ω).2]⟩
  obtain ⟨Ks, hs0, hs1, hD⟩ := OMA.exists_Ks P (X 0) (hm 0) (1 + Xmax) hb hxA hEX hSA
  have hind : IndepFun (X 0) (X 1) P := hindep.indepFun (by norm_num)
  have hid : IdentDistrib (X 1) (X 0) P P := hident 1
  have hv := OMA.second_moment_pos P (X 0) (hm 0) (1 + Xmax) hb hxA hEX
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = ∫ ω, X 0 ω ^ 2 ∂P := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = ∫ ω, Real.log (1 + Ks * X 0 ω) ∂P := ⟨_, rfl⟩
  rw [← hvdef] at hv
  -- the uniform gap
  have hmin : 0 < min Ks (1 - Ks) := lt_min hs0 (by linarith)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min Ks (1 - Ks) / 2 := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact half_pos hmin
  have hdK : 2 * d ≤ Ks := by rw [hd]; linarith [min_le_left Ks (1 - Ks)]
  have hdK' : 2 * d ≤ 1 - Ks := by rw [hd]; linarith [min_le_right Ks (1 - Ks)]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (d ^ 2) (d ^ 4 * v / (2 * (1 + Xmax) ^ 2)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) (by positivity)
  have hc : 0 ≤ v / (4 * (1 + Xmax) ^ 2) := by positivity
  have h2 : ∀ K : ℝ, 0 ≤ K → K < 1 →
      ∫ ω, Real.log (1 + K * ((1 + X 0 ω) * (1 + X 1 ω) - 1)) ∂P
        ≤ 2 * l - v / (4 * (1 + Xmax) ^ 2) * δ := by
    intro K hK0 hK1
    have h := OMA.two_period_integral P (X 0) (X 1) (hm 0) (hm 1) hind hid (1 + Xmax) hb hxA hxB
      Ks hs0.le hs1 hD K hK0 hK1
    have hbr := OMA.bracket_integral P (X 0) (hm 0) (1 + Xmax) hb hxA Ks hs0.le hs1 K hK0 hK1
    rw [← hvdef, ← hldef] at h
    rw [← hvdef] at hbr
    have hT0 : 0 ≤ ∫ ω, (OMA.kap K (X 0 ω) - Ks) ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
    have hδle : δ ≤ (K - Ks) ^ 2 + ∫ ω, (OMA.kap K (X 0 ω) - Ks) ^ 2 ∂P := by
      by_cases hcase : d ≤ |K - Ks|
      · have h3 : d ^ 2 ≤ (K - Ks) ^ 2 := by
          rw [← sq_abs (K - Ks)]
          exact pow_le_pow_left₀ hd0.le hcase 2
        have h4 : δ ≤ d ^ 2 := by rw [hδ]; exact min_le_left _ _
        linarith
      · rw [not_le] at hcase
        have habs := abs_lt.1 hcase
        have hKd : d ≤ K := by linarith
        have hKd' : d ≤ 1 - K := by linarith
        have hprod : d ^ 2 ≤ K * (1 - K) := by
          have := mul_le_mul hKd hKd' hd0.le (by linarith)
          nlinarith
        have h5 : d ^ 4 ≤ K ^ 2 * (1 - K) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hprod 2
          nlinarith
        have h6 : d ^ 4 * v / (2 * (1 + Xmax) ^ 2)
            ≤ K ^ 2 * (1 - K) ^ 2 * v / (2 * (1 + Xmax) ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h5 hv.le) (by positivity)
        have h4 : δ ≤ d ^ 4 * v / (2 * (1 + Xmax) ^ 2) := by rw [hδ]; exact min_le_right _ _
        linarith
    have := mul_le_mul_of_nonneg_left hδle hc
    linarith
  -- the two optimal growth rates
  have hg1 : ∀ K : ℝ, OMA.S_arxiv_1801_06737.g P X 1 K = ∫ ω, Real.log (1 + K * X 0 ω) ∂P := by
    intro K
    simp [OMA.S_arxiv_1801_06737.g, OMA.S_arxiv_1801_06737.totalReturn]
  have hg2 : ∀ K : ℝ, OMA.S_arxiv_1801_06737.g P X 2 K
      = (1 / 2) * ∫ ω, Real.log (1 + K * ((1 + X 0 ω) * (1 + X 1 ω) - 1)) ∂P := by
    intro K
    simp [OMA.S_arxiv_1801_06737.g, OMA.S_arxiv_1801_06737.totalReturn, Finset.prod_range_succ]
  have hS1 : l ≤ OMA.S_arxiv_1801_06737.gStar P X 1 := by
    unfold OMA.S_arxiv_1801_06737.gStar
    have hbdd : BddAbove (Set.range fun K : Set.Ico (0 : ℝ) 1 =>
        OMA.S_arxiv_1801_06737.g P X 1 K) := by
      refine ⟨l, ?_⟩
      rintro _ ⟨K, rfl⟩
      show OMA.S_arxiv_1801_06737.g P X 1 K ≤ l
      rw [hg1, hldef]
      exact OMA.one_period_integral P (X 0) (hm 0) (1 + Xmax) hb hxA Ks hs0.le hs1 hD K K.2.1 K.2.2
    calc l = OMA.S_arxiv_1801_06737.g P X 1 Ks := by rw [hg1, hldef]
      _ ≤ _ := le_ciSup hbdd ⟨Ks, hs0.le, hs1⟩
  have hS2 : OMA.S_arxiv_1801_06737.gStar P X 2 ≤ l - v / (4 * (1 + Xmax) ^ 2) * δ / 2 := by
    unfold OMA.S_arxiv_1801_06737.gStar
    have hne : Nonempty (Set.Ico (0 : ℝ) 1) := ⟨⟨0, le_refl _, zero_lt_one⟩⟩
    apply ciSup_le
    intro K
    rw [hg2]
    have := h2 K K.2.1 K.2.2
    linarith
  have hgap : 0 < v / (4 * (1 + Xmax) ^ 2) * δ := by positivity
  have := hall 2 (by norm_num)
  linarith
