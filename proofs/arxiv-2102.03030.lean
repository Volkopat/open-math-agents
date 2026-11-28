import OMAStatements.S_arxiv_2102_03030

/-!
Proof of `OMA.S_arxiv_2102_03030.main`: `E[G_n] / √n → √(π/2)`.

By Abel summation `E[G_n] = ∑_{m<n} P_m` with `P_m = ∏_{j=1}^m (1 - j/n)`. From `1 - x ≤ e^{-x}`,
`P_m ≤ exp(-m(m+1)/2n)`, and from `e^{-x/(1-x)} ≤ 1 - x`, `P_m ≥ exp(-m(m+1)/(2(n-M)))` for
`m ≤ M < n`. Comparing the Gaussian sums with `∫₀^∞ e^{-x²/2n} = √(πn/2)` (sum–integral comparison
for antitone functions, plus the tail bound `∫_A^∞ e^{-cx²} ≤ 1/(cA)`) gives, with `t = n^{1/4}` and
`M = ⌊t³⌋`, the squeeze `√(π/2)√(1-1/t) - 1/t² - 2/t ≤ E[G_n]/√n ≤ 1/t² + √(π/2)`.
-/

namespace OMA.P_arxiv_2102_03030

open Filter Topology OMA.S_arxiv_2102_03030 Finset

/-- `P n m = ∏_{j=1}^{m} (1 - j/n)`, the probability that the game lasts beyond step `m`. -/
noncomputable def P (n m : ℕ) : ℝ := ∏ j ∈ range m, (1 - ((j : ℝ) + 1) / n)

lemma P_succ (n m : ℕ) : P n (m + 1) = P n m * (1 - ((m : ℝ) + 1) / n) := by
  simp [P, prod_range_succ]

lemma pG_eq (n k : ℕ) (hk : 1 ≤ k) : pG n k = P n (k - 1) * ((k : ℝ) / n) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [pG, P, Nat.add_sub_cancel]
  congr 1
  rw [prod_Ico_eq_prod_range]
  refine prod_congr (by simp) fun j _ => ?_
  push_cast; ring

/-- Abel summation: `∑_{k=1}^N k (P_{k-1} - P_k) = ∑_{m<N} P_m - N P_N`. -/
lemma abel (n N : ℕ) :
    ∑ k ∈ Icc 1 N, (k : ℝ) * (P n (k - 1) * ((k : ℝ) / n)) =
      ∑ m ∈ range N, P n m - N * P n N := by
  induction N with
  | zero => simp [P]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ, P_succ]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

lemma P_n (n : ℕ) (hn : 1 ≤ n) : P n n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [P_succ]
  have : ((m : ℝ) + 1) / ((m + 1 : ℕ) : ℝ) = 1 := by push_cast; field_simp
  rw [this]; ring

lemma EG_eq (n : ℕ) (hn : 1 ≤ n) : EG n = ∑ m ∈ range n, P n m := by
  rw [EG, sum_congr rfl fun k hk => by rw [pG_eq n k (mem_Icc.mp hk).1], abel, P_n n hn]
  ring

/-- `∑_{j<m} (j + 1) = m (m + 1) / 2`. -/
lemma sum_succ (m : ℕ) : ∑ j ∈ range m, ((j : ℝ) + 1) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

lemma P_nonneg (n m : ℕ) (hm : m ≤ n) : 0 ≤ P n m := by
  apply prod_nonneg
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ n := by
    have := mem_range.mp hj; exact_mod_cast (by omega : j + 1 ≤ n)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have : ((j : ℝ) + 1) / n ≤ 1 := (div_le_one (by exact_mod_cast h)).mpr hj'
    linarith

lemma P_le (n m : ℕ) (hm : m ≤ n) : P n m ≤ Real.exp (-((m : ℝ) * (m + 1) / (2 * n))) := by
  have h : P n m ≤ ∏ j ∈ range m, Real.exp (-(((j : ℝ) + 1) / n)) := by
    apply Finset.prod_le_prod
    · intro j hj
      have hj' : j + 1 ≤ n := by have := mem_range.mp hj; omega
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : ((j : ℝ) + 1) / n ≤ 1 :=
          (div_le_one (by exact_mod_cast h)).mpr (by exact_mod_cast hj')
        linarith
    · intro j _; exact Real.one_sub_le_exp_neg _
  refine h.trans (le_of_eq ?_)
  rw [← Real.exp_sum]; congr 1
  rw [sum_neg_distrib, ← sum_div, sum_succ]; ring

/-- `exp (-x/(1-x)) ≤ 1 - x` for `0 ≤ x < 1`. -/
lemma exp_le_one_sub (x : ℝ) (_h0 : 0 ≤ x) (h1 : x < 1) : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have ht := Real.add_one_le_exp (x / (1 - x))
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hpos]
  calc (1 - x)⁻¹ = x / (1 - x) + 1 := by field_simp; ring
    _ ≤ Real.exp (x / (1 - x)) := ht

lemma le_P (n m M : ℕ) (hmM : m ≤ M) (hMn : M < n) :
    Real.exp (-((m : ℝ) * (m + 1) / (2 * ((n : ℝ) - M)))) ≤ P n m := by
  have hnM : (0 : ℝ) < (n : ℝ) - M := sub_pos.mpr (by exact_mod_cast hMn)
  have h : ∏ j ∈ range m, Real.exp (-(((j : ℝ) + 1) / ((n : ℝ) - M))) ≤ P n m := by
    apply Finset.prod_le_prod
    · intro j _; exact (Real.exp_pos _).le
    · intro j hj
      have hjm : j + 1 ≤ M := by have := mem_range.mp hj; omega
      have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hx0 : 0 ≤ ((j : ℝ) + 1) / n := by positivity
      have hjn : ((j : ℝ) + 1) < n := by exact_mod_cast (show j + 1 < n by omega)
      have hx1 : ((j : ℝ) + 1) / n < 1 := (div_lt_one hn).mpr hjn
      refine le_trans ?_ (exp_le_one_sub _ hx0 hx1)
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hjM : ((j : ℝ) + 1) ≤ M := by exact_mod_cast hjm
      have hne : (n : ℝ) ≠ 0 := hn.ne'
      have hne2 : (n : ℝ) - ((j : ℝ) + 1) ≠ 0 := by linarith
      have e : ((j : ℝ) + 1) / n / (1 - ((j : ℝ) + 1) / n) = ((j : ℝ) + 1) / ((n : ℝ) - ((j : ℝ) + 1)) := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) hnM (by linarith)
  refine le_trans (le_of_eq ?_) h
  rw [← Real.exp_sum]; congr 1
  rw [sum_neg_distrib, ← sum_div, sum_succ]
  have : (n : ℝ) - M ≠ 0 := hnM.ne'
  field_simp


section Gauss

open MeasureTheory Set

variable {c : ℝ}

lemma antitoneOn_gauss (hc : 0 < c) (a b : ℝ) (ha : 0 ≤ a) :
    AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Icc a b) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hx0 : 0 ≤ x := le_trans ha hx.1
  nlinarith [mul_le_mul hxy hxy hx0 (le_trans hx0 hxy)]

lemma gauss_le_one (hc : 0 < c) (x : ℝ) : Real.exp (-c * x ^ 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg x]

lemma integrableOn_gauss (hc : 0 < c) (s : Set ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-c * x ^ 2)) s :=
  (integrable_exp_neg_mul_sq hc).integrableOn

lemma interval_le_Ioi (hc : 0 < c) (a b : ℝ) :
    ∫ x in a..b, Real.exp (-c * x ^ 2) ≤ ∫ x in Ioi a, Real.exp (-c * x ^ 2) := by
  rw [← intervalIntegral.integral_interval_add_Ioi (integrableOn_gauss hc _)
    (integrableOn_gauss hc _)]
  have : 0 ≤ ∫ x in Ioi b, Real.exp (-c * x ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => (Real.exp_pos _).le
  linarith

/-- The sum of a Gaussian over `0, …, N-1` is at most `1 + ∫₀^∞`. -/
lemma sum_gauss_le (hc : 0 < c) (N : ℕ) :
    ∑ m ∈ range N, Real.exp (-c * (m : ℝ) ^ 2) ≤ 1 + Real.sqrt (Real.pi / c) / 2 := by
  have hI : 0 ≤ Real.sqrt (Real.pi / c) / 2 := by positivity
  rcases N with _ | K
  · simp; linarith
  rw [sum_range_succ']
  have hs := (antitoneOn_gauss hc 0 (0 + K) le_rfl).sum_le_integral
  have h2 := interval_le_Ioi hc 0 (0 + K)
  rw [integral_gaussian_Ioi] at h2
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hs h2
  push_cast
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero]
  linarith

/-- Gaussian tail: `∫_A^∞ e^{-c x²} ≤ 1 / (c A)` for `A > 0`. -/
lemma gauss_tail (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∫ x in Ioi A, Real.exp (-c * x ^ 2) ≤ 1 / (c * A) := by
  have hb : 0 < c * A := mul_pos hc hA
  have hle : ∫ x in Ioi A, Real.exp (-c * x ^ 2) ≤ ∫ x in Ioi A, Real.exp ((-(c * A)) * x) := by
    apply setIntegral_mono_on (integrableOn_gauss hc _) _ measurableSet_Ioi
    · intro x hx
      apply Real.exp_le_exp.mpr
      have hx' : A < x := hx
      nlinarith [mul_le_mul_of_nonneg_left hx'.le (le_of_lt (lt_trans hA hx'))]
    · simpa [neg_mul] using exp_neg_integrableOn_Ioi A hb
  rw [integral_exp_mul_Ioi (by linarith) A] at hle
  refine hle.trans ?_
  rw [neg_div_neg_eq, div_le_div_iff_of_pos_right hb]
  rw [Real.exp_le_one_iff]; nlinarith

/-- Lower bound for the shifted Gaussian sum. -/
lemma sum_gauss_ge (hc : 0 < c) (a : ℕ) :
    Real.sqrt (Real.pi / c) / 2 - 1 - 1 / (c * (1 + a)) ≤
      ∑ i ∈ range a, Real.exp (-c * (1 + (i : ℝ)) ^ 2) := by
  have hsum := (antitoneOn_gauss hc 1 (1 + a) zero_le_one).integral_le_sum
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := (1 : ℝ)) (b := 1 + a)
    (integrableOn_gauss hc _) (integrableOn_gauss hc _)
  have hsplit0 := intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := 1)
    (integrableOn_gauss hc _) (integrableOn_gauss hc _)
  rw [integral_gaussian_Ioi] at hsplit0
  have h01 : ∫ x in (0 : ℝ)..1, Real.exp (-c * x ^ 2) ≤ 1 := by
    have := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (integrable_exp_neg_mul_sq hc).intervalIntegrable intervalIntegrable_const (fun x _ => gauss_le_one hc x)
    simpa using this
  have htail := gauss_tail hc (1 + a) (by positivity)
  linarith

end Gauss

section Limit

open MeasureTheory Set

lemma sqrt_gauss (y : ℝ) (hy : 0 < y) :
    Real.sqrt (Real.pi / (1 / (2 * y))) / 2 = Real.sqrt (Real.pi / 2) * Real.sqrt y := by
  have h : Real.pi / (1 / (2 * y)) = (Real.pi / 2) * (2 ^ 2 * y) := by field_simp
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]
  ring

lemma upper_bound (n : ℕ) (hn : 1 ≤ n) :
    EG n ≤ 1 + Real.sqrt (Real.pi / 2) * Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < 1 / (2 * n) := by positivity
  rw [EG_eq n hn]
  calc ∑ m ∈ range n, P n m
      ≤ ∑ m ∈ range n, Real.exp (-(1 / (2 * (n : ℝ))) * (m : ℝ) ^ 2) := by
        apply sum_le_sum; intro m hm
        refine (P_le n m (mem_range.mp hm).le).trans (Real.exp_le_exp.mpr ?_)
        have : (m : ℝ) ^ 2 / (2 * n) ≤ (m : ℝ) * (m + 1) / (2 * n) :=
          div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) (by positivity)
        rw [show -(1 / (2 * (n : ℝ))) * (m : ℝ) ^ 2 = -((m : ℝ) ^ 2 / (2 * n)) by ring]
        linarith
    _ ≤ 1 + Real.sqrt (Real.pi / (1 / (2 * n))) / 2 := sum_gauss_le hc n
    _ = 1 + Real.sqrt (Real.pi / 2) * Real.sqrt n := by rw [sqrt_gauss n hn']

lemma lower_bound (n M : ℕ) (hM : M + 1 ≤ n) :
    Real.sqrt (Real.pi / 2) * Real.sqrt ((n : ℝ) - M) - 1 - 2 * ((n : ℝ) - M) / ((M : ℝ) + 2)
      ≤ EG n := by
  have hMn : M < n := by omega
  have hy : (0 : ℝ) < (n : ℝ) - M := sub_pos.mpr (by exact_mod_cast hMn)
  have hc : (0 : ℝ) < 1 / (2 * ((n : ℝ) - M)) := by positivity
  have key := sum_gauss_ge hc (M + 1)
  rw [sqrt_gauss _ hy] at key
  have e : 1 / (1 / (2 * ((n : ℝ) - M)) * (1 + ((M + 1 : ℕ) : ℝ))) =
      2 * ((n : ℝ) - M) / ((M : ℝ) + 2) := by
    push_cast; field_simp; ring
  rw [e] at key
  refine key.trans ?_
  rw [EG_eq n (by omega)]
  calc ∑ i ∈ range (M + 1), Real.exp (-(1 / (2 * ((n : ℝ) - M))) * (1 + (i : ℝ)) ^ 2)
      ≤ ∑ m ∈ range (M + 1), P n m := by
        apply sum_le_sum; intro m hm
        have hmM : m ≤ M := by have := mem_range.mp hm; omega
        refine le_trans (Real.exp_le_exp.mpr ?_) (le_P n m M hmM hMn)
        have : (m : ℝ) * (m + 1) / (2 * ((n : ℝ) - M)) ≤ (1 + (m : ℝ)) ^ 2 / (2 * ((n : ℝ) - M)) :=
          div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) (by positivity)
        rw [show -(1 / (2 * ((n : ℝ) - M))) * (1 + (m : ℝ)) ^ 2 =
          -((1 + (m : ℝ)) ^ 2 / (2 * ((n : ℝ) - M))) by ring]
        linarith
    _ ≤ ∑ m ∈ range n, P n m :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hM)
          fun m hm _ => P_nonneg n m (mem_range.mp hm).le

/-- `t n = n^{1/4}`. -/
noncomputable def t (n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4)

lemma t_nonneg (n : ℕ) : 0 ≤ t n := Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma t_pow_four (n : ℕ) : t n ^ 4 = n := by
  rw [t, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

lemma sqrt_eq_t (n : ℕ) : Real.sqrt n = t n ^ 2 := by
  rw [← t_pow_four, show t n ^ 4 = (t n ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

lemma tendsto_t : Tendsto t atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop

/-- The explicit lower barrier `ℓ(T) = √(π/2) √(1 - 1/T) - 1/T² - 2/T`. -/
noncomputable def ℓ (T : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 2) * Real.sqrt (1 - 1 / T) - 1 / T ^ 2 - 2 * (1 / T)

lemma tendsto_ℓ : Tendsto ℓ atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have h1 : Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero
  have h2 : Tendsto (fun T : ℝ => 1 / T ^ 2) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0))
    simpa [Function.comp_def] using this
  have h1' : Tendsto (fun T : ℝ => 1 - 1 / T) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  have h3 : Tendsto (fun T : ℝ => Real.sqrt (1 - 1 / T)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 1).comp h1'
  have key := (((tendsto_const_nhds (x := Real.sqrt (Real.pi / 2))).mul h3).sub h2).sub
    (h1.const_mul 2)
  rw [mul_one, sub_zero, mul_zero, sub_zero] at key
  exact key

lemma lower_t (n : ℕ) (hn : 16 ≤ n) : ℓ (t n) ≤ EG n / Real.sqrt n := by
  set T := t n with hT
  have hT4 : T ^ 4 = n := t_pow_four n
  have hT0 : 0 ≤ T := t_nonneg n
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hT2 : 2 ≤ T := by
    by_contra h; push Not at h
    have : T ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hT0 (by norm_num)
    linarith
  set M := ⌊T ^ 3⌋₊ with hMdef
  have hM1 : (M : ℝ) ≤ T ^ 3 := Nat.floor_le (by positivity)
  have hM2 : T ^ 3 < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMhalf : (M : ℝ) + 1 ≤ n := by nlinarith
  have hMn : M + 1 ≤ n := by exact_mod_cast hMhalf
  have hlow := lower_bound n M hMn
  have hsq : Real.sqrt n = T ^ 2 := sqrt_eq_t n
  have hTpos : 0 < T := by linarith
  have hT2pos : 0 < T ^ 2 := by positivity
  rw [hsq, le_div_iff₀ hT2pos]
  -- the main term
  have hm1 : T ^ 2 * Real.sqrt (1 - 1 / T) ≤ Real.sqrt ((n : ℝ) - M) := by
    have hx : 0 ≤ 1 - 1 / T := by
      rw [sub_nonneg, div_le_one hTpos]; linarith
    rw [← Real.sqrt_sq hT2pos.le, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have : (T ^ 2) ^ 2 * (1 - 1 / T) = T ^ 4 - T ^ 3 := by field_simp
    rw [this, hT4]; linarith
  -- the error term
  have hm2 : 2 * ((n : ℝ) - M) / ((M : ℝ) + 2) ≤ 2 / T * T ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 / T * T ^ 2 * ((M : ℝ) + 2) ≥ 2 / T * T ^ 2 * T ^ 3 := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : 2 / T * T ^ 2 * T ^ 3 = 2 * T ^ 4 := by field_simp
    nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hpi : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have e : ℓ T * T ^ 2 = Real.sqrt (Real.pi / 2) * (T ^ 2 * Real.sqrt (1 - 1 / T)) - 1 - 2 / T * T ^ 2 := by
    simp only [ℓ]; field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hm1 hpi]

theorem solution :
    Tendsto (fun n : ℕ => EG n / Real.sqrt n) atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have hlow : Tendsto (fun n => ℓ (t n)) atTop (𝓝 (Real.sqrt (Real.pi / 2))) :=
    tendsto_ℓ.comp tendsto_t
  have hup : Tendsto (fun n : ℕ => 1 / t n ^ 2 + Real.sqrt (Real.pi / 2)) atTop
      (𝓝 (Real.sqrt (Real.pi / 2))) := by
    have : Tendsto (fun n : ℕ => 1 / t n ^ 2) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_t)
      simpa [Function.comp_def] using this
    simpa using this.add_const (Real.sqrt (Real.pi / 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 16] with n hn
    exact lower_t n hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hsq : Real.sqrt n = t n ^ 2 := sqrt_eq_t n
    have hpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [div_le_iff₀ hpos]
    have := upper_bound n hn
    rw [← hsq]
    calc EG n ≤ 1 + Real.sqrt (Real.pi / 2) * Real.sqrt n := this
      _ = (1 / Real.sqrt n + Real.sqrt (Real.pi / 2)) * Real.sqrt n := by field_simp

end Limit

end OMA.P_arxiv_2102_03030

theorem OMA.solution : type_of% @OMA.S_arxiv_2102_03030.main := OMA.P_arxiv_2102_03030.solution
