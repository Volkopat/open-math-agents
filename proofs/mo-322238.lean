import OMAStatements.S_mo_322238

-- Problem: Distribution of weighted sum of non-central chi-squared random variables: log-concave?
-- Source: MathOverflow question 322238. Target: OMA.S_mo_322238.main, the NEGATIVE answer
-- (the law of the weighted sum need not have a log-concave density).
-- Witness: n = 2, both variables central (delta = 0), weights (1, 10^-16), on the product of two
-- standard Gaussians. Idea: a log-concave density f of X = Z1^2 + 10^-16 * Z2^2 would exceed 25600
-- somewhere in [0, 2 * 10^-16] and 1/1600 somewhere in [1, 5] (crude Gaussian box bounds), hence
-- f >= 4 on an interval of length at least 3/8, so the total mass would exceed 1.

open MeasureTheory ProbabilityTheory

namespace OMA.P28

/-- The standard Gaussian density is at least `1/27` on `[-2, 2]`. -/
lemma pdf_lb (x : ℝ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : (1 / 27 : ℝ) ≤ gaussianPDFReal 0 1 x := by
  have hpi : Real.sqrt (2 * Real.pi) ≤ 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.pi_le_four]
  have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hinv : (1 / 3 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hpos hpi
  have he2 : Real.exp 2 ≤ 9 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hexp : (1 / 9 : ℝ) ≤ Real.exp (-x ^ 2 / 2) := by
    have h3 : Real.exp (-2) ≤ Real.exp (-x ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h4 : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 2) he2
    linarith
  have hval : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    simp [gaussianPDFReal]
  rw [hval]
  calc (1 / 27 : ℝ) = 1 / 3 * (1 / 9) := by norm_num
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) :=
        mul_le_mul hinv hexp (by norm_num) (inv_nonneg.mpr hpos.le)

/-- Lower bound for the standard Gaussian mass of an interval inside `[-2, 2]`. -/
lemma gauss_Icc_lb (a b : ℝ) (ha : -2 ≤ a) (hb : b ≤ 2) :
    ENNReal.ofReal ((b - a) / 27) ≤ gaussianReal 0 1 (Set.Icc a b) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  calc ENNReal.ofReal ((b - a) / 27) = ENNReal.ofReal (1 / 27) * volume (Set.Icc a b) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
    _ = ∫⁻ _ in Set.Icc a b, ENNReal.ofReal (1 / 27) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Set.Icc a b, gaussianPDF 0 1 x :=
        setLIntegral_mono' measurableSet_Icc (fun x hx =>
          ENNReal.ofReal_le_ofReal (pdf_lb x (le_trans ha hx.1) (le_trans hx.2 hb)))

/-- A probability law with a log-concave density cannot have average density above `25600` on a
short interval `[0, η]` and average density above `1/1600` on `[1, 5]`: the density would be at
least `4` on an interval of length at least `3/8`. -/
lemma no_lc (ν : Measure ℝ) (hν : ν Set.univ ≤ 1) (η : ℝ) (hη : η ≤ 1 / 4)
    (hA : ENNReal.ofReal (25600 * η) < ν (Set.Icc 0 η))
    (hB : ENNReal.ofReal (1 / 400) < ν (Set.Icc 1 5)) :
    ¬ OMA.S_mo_322238.HasLogConcaveDensity ν := by
  rintro ⟨f, hf0, rfl, hlc⟩
  obtain ⟨a, haA, hfa⟩ : ∃ a ∈ Set.Icc (0 : ℝ) η, 25600 < f a := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    apply absurd hA
    rw [not_lt, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ x in Set.Icc 0 η, ENNReal.ofReal (f x)
        ≤ ∫⁻ _ in Set.Icc 0 η, ENNReal.ofReal 25600 :=
          setLIntegral_mono' measurableSet_Icc (fun x hx => ENNReal.ofReal_le_ofReal (hcon x hx))
      _ = ENNReal.ofReal 25600 * volume (Set.Icc 0 η) := setLIntegral_const _ _
      _ = ENNReal.ofReal (25600 * η) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
          simp
  obtain ⟨c, hcB, hfc⟩ : ∃ c ∈ Set.Icc (1 : ℝ) 5, 1 / 1600 < f c := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    apply absurd hB
    rw [not_lt, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ x in Set.Icc 1 5, ENNReal.ofReal (f x)
        ≤ ∫⁻ _ in Set.Icc 1 5, ENNReal.ofReal (1 / 1600) :=
          setLIntegral_mono' measurableSet_Icc (fun x hx => ENNReal.ofReal_le_ofReal (hcon x hx))
      _ = ENNReal.ofReal (1 / 1600) * volume (Set.Icc 1 5) := setLIntegral_const _ _
      _ = ENNReal.ofReal (1 / 400) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hmid : 4 ≤ f ((a + c) / 2) := by
    have h := hlc a c (1 / 2) (by norm_num) (by norm_num)
    have e1 : (1 / 2 : ℝ) * a + (1 - 1 / 2) * c = (a + c) / 2 := by ring
    have e2 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [e1, e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
    have h1 : (160 : ℝ) ≤ Real.sqrt (f a) := by
      rw [Real.le_sqrt' (by norm_num)]
      linarith
    have h2 : (1 / 40 : ℝ) ≤ Real.sqrt (f c) := by
      rw [Real.le_sqrt' (by norm_num)]
      linarith
    calc (4 : ℝ) = 160 * (1 / 40) := by norm_num
      _ ≤ Real.sqrt (f a) * Real.sqrt (f c) := mul_le_mul h1 h2 (by norm_num) (Real.sqrt_nonneg _)
      _ ≤ f ((a + c) / 2) := h
  have hac : a < (a + c) / 2 := by linarith [haA.2, hcB.1]
  have hfour : ∀ x ∈ Set.Icc a ((a + c) / 2), 4 ≤ f x := by
    intro x hx
    have hd : 0 < (a + c) / 2 - a := by linarith
    have ht0 : 0 ≤ ((a + c) / 2 - x) / ((a + c) / 2 - a) := div_nonneg (by linarith [hx.2]) hd.le
    have ht1 : ((a + c) / 2 - x) / ((a + c) / 2 - a) ≤ 1 := by
      rw [div_le_one hd]
      linarith [hx.1]
    have h := hlc a ((a + c) / 2) (((a + c) / 2 - x) / ((a + c) / 2 - a)) ht0 ht1
    have e : ((a + c) / 2 - x) / ((a + c) / 2 - a) * a
        + (1 - ((a + c) / 2 - x) / ((a + c) / 2 - a)) * ((a + c) / 2) = x := by
      have hθ : ((a + c) / 2 - x) / ((a + c) / 2 - a) * ((a + c) / 2 - a) = (a + c) / 2 - x :=
        div_mul_cancel₀ _ hd.ne.symm
      linear_combination (-1 : ℝ) * hθ
    rw [e] at h
    have h1 : (4 : ℝ) ^ (((a + c) / 2 - x) / ((a + c) / 2 - a))
        ≤ f a ^ (((a + c) / 2 - x) / ((a + c) / 2 - a)) :=
      Real.rpow_le_rpow (by norm_num) (by linarith) ht0
    have h2 : (4 : ℝ) ^ (1 - ((a + c) / 2 - x) / ((a + c) / 2 - a))
        ≤ f ((a + c) / 2) ^ (1 - ((a + c) / 2 - x) / ((a + c) / 2 - a)) :=
      Real.rpow_le_rpow (by norm_num) hmid (by linarith)
    have h3 : (4 : ℝ) ^ (((a + c) / 2 - x) / ((a + c) / 2 - a))
        * (4 : ℝ) ^ (1 - ((a + c) / 2 - x) / ((a + c) / 2 - a)) = 4 := by
      rw [← Real.rpow_add (by norm_num)]
      simp
    calc (4 : ℝ) = (4 : ℝ) ^ (((a + c) / 2 - x) / ((a + c) / 2 - a))
        * (4 : ℝ) ^ (1 - ((a + c) / 2 - x) / ((a + c) / 2 - a)) := h3.symm
      _ ≤ f a ^ (((a + c) / 2 - x) / ((a + c) / 2 - a))
        * f ((a + c) / 2) ^ (1 - ((a + c) / 2 - x) / ((a + c) / 2 - a)) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hf0 a) _)
      _ ≤ f x := h
  have hbig : ENNReal.ofReal (3 / 2)
      ≤ (volume.withDensity fun x => ENNReal.ofReal (f x)) (Set.Icc a ((a + c) / 2)) := by
    rw [withDensity_apply _ measurableSet_Icc]
    calc ENNReal.ofReal (3 / 2) ≤ ENNReal.ofReal (4 * ((a + c) / 2 - a)) :=
          ENNReal.ofReal_le_ofReal (by linarith [haA.2, hcB.1])
      _ = ENNReal.ofReal 4 * volume (Set.Icc a ((a + c) / 2)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
      _ = ∫⁻ _ in Set.Icc a ((a + c) / 2), ENNReal.ofReal 4 := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Set.Icc a ((a + c) / 2), ENNReal.ofReal (f x) :=
          setLIntegral_mono' measurableSet_Icc (fun x hx => ENNReal.ofReal_le_ofReal (hfour x hx))
  have hle : ENNReal.ofReal (3 / 2) ≤ 1 :=
    le_trans hbig (le_trans (measure_mono (Set.subset_univ _)) hν)
  rw [ENNReal.ofReal_le_one] at hle
  norm_num at hle

end OMA.P28

theorem OMA.solution : type_of% @OMA.S_mo_322238.main := by
  intro h
  have hmeas : ∀ i : Fin 2, Measurable (fun ω : Fin 2 → ℝ => ω i ^ 2) :=
    fun i => (measurable_pi_apply i).pow_const 2
  have hw : ∀ i : Fin 2, (0 : ℝ) < (![1, 1 / 10 ^ 16] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  have hindep : iIndepFun (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i ^ 2)
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    iIndepFun_pi (X := fun (_ : Fin 2) (z : ℝ) => z ^ 2)
      (fun _ => (measurable_id.pow_const 2).aemeasurable)
  have hlaw : ∀ i : Fin 2, (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map
      (fun ω : Fin 2 → ℝ => ω i ^ 2) = OMA.S_mo_322238.chiSq ((fun _ : Fin 2 => (0 : ℝ)) i) := by
    intro i
    have h1 : (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map (fun ω : Fin 2 → ℝ => ω i)
        = gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).map_eq
    have h2 : (fun ω : Fin 2 → ℝ => ω i ^ 2)
        = (fun z : ℝ => z ^ 2) ∘ (fun ω : Fin 2 → ℝ => ω i) := rfl
    have h3 := Measure.map_map (μ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      (g := fun z : ℝ => z ^ 2) (f := fun ω : Fin 2 → ℝ => ω i)
      (measurable_id.pow_const 2) (measurable_pi_apply i)
    rw [h2, ← h3, h1]
    simp [OMA.S_mo_322238.chiSq]
  have key := h 2 (fun _ => 0) ![1, 1 / 10 ^ 16] le_rfl (fun _ => le_rfl) hw (Fin 2 → ℝ)
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) (fun i ω => ω i ^ 2) hmeas hindep hlaw
  have hsum : Measurable (fun ω : Fin 2 → ℝ =>
      ∑ i : Fin 2, (![1, 1 / 10 ^ 16] : Fin 2 → ℝ) i * ω i ^ 2) :=
    Finset.measurable_sum _ (fun i _ => (hmeas i).const_mul _)
  refine OMA.P28.no_lc _ ?_ (2 / 10 ^ 16) (by norm_num) ?_ ?_ key
  · rw [Measure.map_apply hsum MeasurableSet.univ]
    exact prob_le_one
  · rw [Measure.map_apply hsum measurableSet_Icc]
    have hsub : (Set.univ : Set (Fin 2)).pi
        ![Set.Icc (-(1 / 10 ^ 8 : ℝ)) (1 / 10 ^ 8), Set.Icc (-1 : ℝ) 1]
        ⊆ (fun ω : Fin 2 → ℝ => ∑ i : Fin 2, (![1, 1 / 10 ^ 16] : Fin 2 → ℝ) i * ω i ^ 2) ⁻¹'
          Set.Icc 0 (2 / 10 ^ 16) := by
      intro ω hω
      have h0 := hω 0 (Set.mem_univ _)
      have h1 := hω 1 (Set.mem_univ _)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc] at h0 h1
      simp only [Set.mem_preimage, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_Icc]
      constructor
      · positivity
      · nlinarith [h0.1, h0.2, h1.1, h1.2]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Measure.pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have g0 := OMA.P28.gauss_Icc_lb (-(1 / 10 ^ 8)) (1 / 10 ^ 8) (by norm_num) (by norm_num)
    have g1 := OMA.P28.gauss_Icc_lb (-1) 1 (by norm_num) (by norm_num)
    refine lt_of_lt_of_le ?_ (mul_le_mul' g0 g1)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  · rw [Measure.map_apply hsum measurableSet_Icc]
    have hsub : (Set.univ : Set (Fin 2)).pi ![Set.Icc (1 : ℝ) 2, Set.Icc (-1 : ℝ) 1]
        ⊆ (fun ω : Fin 2 → ℝ => ∑ i : Fin 2, (![1, 1 / 10 ^ 16] : Fin 2 → ℝ) i * ω i ^ 2) ⁻¹'
          Set.Icc 1 5 := by
      intro ω hω
      have h0 := hω 0 (Set.mem_univ _)
      have h1 := hω 1 (Set.mem_univ _)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc] at h0 h1
      simp only [Set.mem_preimage, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_Icc]
      constructor
      · nlinarith [h0.1, h0.2, h1.1, h1.2, sq_nonneg (ω 1)]
      · nlinarith [h0.1, h0.2, h1.1, h1.2]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Measure.pi_pi, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have g0 := OMA.P28.gauss_Icc_lb 1 2 (by norm_num) (by norm_num)
    have g1 := OMA.P28.gauss_Icc_lb (-1) 1 (by norm_num) (by norm_num)
    refine lt_of_lt_of_le ?_ (mul_le_mul' g0 g1)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
