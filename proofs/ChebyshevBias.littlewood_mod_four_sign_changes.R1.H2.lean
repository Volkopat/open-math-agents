import OMAReductions.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1
import Mathlib

/-!
Proof of ChebyshevBias.littlewood_mod_four_sign_changes.R1.H2:
infinitely many positive excursions J(n) > 4 * sqrt(n) / log(n) of the weighted
prime-power sum for the nontrivial Dirichlet character modulo 4.
-/

open Filter Finset Real Complex MeasureTheory Topology
open scoped Nat

namespace ChebyshevBiasR1H2Proof
/-- The nontrivial real Dirichlet character modulo 4 valued in complex numbers. -/
noncomputable def χ4 : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The Dirichlet L-function of χ4. -/
noncomputable def L4 : ℂ → ℂ :=
  DirichletCharacter.LFunction χ4

/-- The completed Dirichlet L-function of χ4. -/
noncomputable def xi4 : ℂ → ℂ :=
  DirichletCharacter.completedLFunction χ4

private lemma χ4_apply_nat (n : ℕ) :
    χ4 (n : ZMod 4) = ((ZMod.χ₄ (n : ZMod 4) : ℝ) : ℂ) := by
  simp [χ4, MulChar.ringHomComp_apply]

private lemma χ4_ne_one : χ4 ≠ 1 := by
  intro h
  have h3 := congrArg (fun f : DirichletCharacter ℂ 4 => f (3 : ZMod 4)) h
  have hval : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  have hunit : IsUnit (3 : ZMod 4) := by decide
  rw [χ4, MulChar.ringHomComp_apply, hval, MulChar.one_apply hunit] at h3
  norm_num at h3

private lemma χ4_odd : χ4.Odd := by
  change χ4 (-1 : ZMod 4) = -1
  have h1 : (-1 : ZMod 4) = (3 : ZMod 4) := by decide
  have hval : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [h1, χ4, MulChar.ringHomComp_apply, hval]
  norm_num

private lemma χ4_inv : χ4⁻¹ = χ4 := by
  rw [inv_eq_iff_mul_eq_one]
  apply DFunLike.ext
  intro a
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit a
  · rw [MulChar.one_apply hu]
    fin_cases a
    · change IsUnit (0 : ZMod 4) at hu
      exact absurd hu (by decide)
    · have hv : ZMod.χ₄ (1 : ZMod 4) = 1 := by decide
      change χ4 (1 : ZMod 4) * χ4 (1 : ZMod 4) = 1
      rw [χ4, MulChar.ringHomComp_apply, hv]; norm_num
    · change IsUnit (2 : ZMod 4) at hu
      exact absurd hu (by decide)
    · have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
      change χ4 (3 : ZMod 4) * χ4 (3 : ZMod 4) = 1
      rw [χ4, MulChar.ringHomComp_apply, hv]; norm_num
  · rw [MulChar.map_nonunit χ4 hu, MulChar.map_nonunit (1 : DirichletCharacter ℂ 4) hu, zero_mul]

private lemma χ4_isPrimitive : χ4.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : χ4.conductor ∣ 4 := DirichletCharacter.conductor_dvd_level χ4
  have hpos : 0 < χ4.conductor := Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ4)
  have hne1 : χ4.conductor ≠ 1 := by
    intro h1
    exact χ4_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1)
  have hne2 : χ4.conductor ≠ 2 := by
    intro h2
    obtain ⟨hd, χ₀, hχ₀⟩ := DirichletCharacter.factorsThrough_conductor χ4
    have htriv : χ₀ = 1 := by
      have hgen : ∀ (m : ℕ) (ψ : DirichletCharacter ℂ m), m = 2 → ψ = 1 := by
        rintro m ψ rfl
        apply DFunLike.ext
        intro x
        by_cases hu : IsUnit x
        · fin_cases x
          · change IsUnit (0 : ZMod 2) at hu
            exact absurd hu (by decide)
          · change ψ (1 : ZMod 2) = (1 : DirichletCharacter ℂ 2) (1 : ZMod 2)
            simp
        · rw [MulChar.map_nonunit ψ hu, MulChar.map_nonunit (1 : DirichletCharacter ℂ 2) hu]
      exact hgen χ4.conductor χ₀ h2
    rw [htriv, DirichletCharacter.changeLevel_one] at hχ₀
    exact χ4_ne_one hχ₀
  have hle : χ4.conductor ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hne3 : χ4.conductor ≠ 3 := by
    intro h3; rw [h3] at hdvd; norm_num at hdvd
  omega

private lemma L4_differentiable : Differentiable ℂ L4 :=
  DirichletCharacter.differentiable_LFunction χ4_ne_one

private lemma xi4_differentiable : Differentiable ℂ xi4 :=
  DirichletCharacter.differentiable_completedLFunction χ4_ne_one

private lemma L4_eq_xi4_div_gammaℝ (s : ℂ) :
    L4 s = xi4 s / Complex.Gammaℝ (s + 1) := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ4 s (Or.inr (by norm_num))
  rwa [χ4_odd.gammaFactor_def] at h

private lemma xi4_eq_L4_mul_gammaℝ {s : ℂ} (hs : -1 < s.re) :
    xi4 s = L4 s * Complex.Gammaℝ (s + 1) := by
  have hne : Complex.Gammaℝ (s + 1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [L4_eq_xi4_div_gammaℝ, div_mul_cancel₀ _ hne]

/- ### Step 1: Alternating series representation, positivity on (0, ∞), and polynomial bound -/

/-- The k-th grouped term of the alternating Dirichlet series for χ4. -/
noncomputable def altTerm (k : ℕ) (s : ℂ) : ℂ :=
  ((4 * k + 1 : ℕ) : ℂ) ^ (-s) - ((4 * k + 3 : ℕ) : ℂ) ^ (-s)

private lemma altTerm_eq_integral (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    altTerm k s = s * ∫ t in ((4 * k + 1 : ℕ) : ℝ)..((4 * k + 3 : ℕ) : ℝ),
      (t : ℂ) ^ (-(s + 1)) := by
  let a : ℝ := (4 * k + 1 : ℕ)
  let b : ℝ := (4 * k + 3 : ℕ)
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by dsimp [a, b]; norm_cast; omega
  have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => -((x : ℂ) ^ (-s))) (s * (t : ℂ) ^ (-(s + 1))) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have h1 := (hasDerivAt_ofReal_cpow_const htpos.ne' (neg_ne_zero.mpr hsne)).neg
    have heq : -(-s * (t : ℂ) ^ (-s - 1)) = s * (t : ℂ) ^ (-(s + 1)) := by
      rw [← neg_mul, neg_neg, show (-s - 1 : ℂ) = -(s + 1) by ring]
    exact h1.congr_deriv heq
  have hint : IntervalIntegrable (fun t : ℝ => s * (t : ℂ) ^ (-(s + 1))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    exact ((continuousAt_const).mul
      (Complex.continuousAt_ofReal_cpow_const t (-(s + 1)) (Or.inr htpos.ne'))).continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  dsimp only [altTerm]
  calc
    ((4 * k + 1 : ℕ) : ℂ) ^ (-s) - ((4 * k + 3 : ℕ) : ℂ) ^ (-s)
        = -((b : ℂ) ^ (-s)) - -((a : ℂ) ^ (-s)) := by
          dsimp [a, b]; push_cast; ring
    _ = s * ∫ t in a..b, (t : ℂ) ^ (-(s + 1)) := hftc.symm

private lemma norm_altTerm_le (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖altTerm k s‖ ≤ 2 * ‖s‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)) := by
  rw [altTerm_eq_integral k hs, norm_mul]
  let a : ℝ := (4 * k + 1 : ℕ)
  let b : ℝ := (4 * k + 3 : ℕ)
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by dsimp [a, b]; norm_cast; omega
  have hba : |b - a| = 2 := by
    dsimp [a, b]; push_cast; rw [show (4 * (k : ℝ) + 3) - (4 * (k : ℝ) + 1) = 2 by ring]; norm_num
  have hbound : ∀ t ∈ Set.uIoc a b,
      ‖(t : ℂ) ^ (-(s + 1))‖ ≤ a ^ (-(s.re + 1)) := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1.le
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos ha ht.1.le (by linarith)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hba] at hint
  calc
    ‖s‖ * ‖∫ t in a..b, (t : ℂ) ^ (-(s + 1))‖
        ≤ ‖s‖ * (a ^ (-(s.re + 1)) * 2) := mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ = 2 * ‖s‖ * a ^ (-(s.re + 1)) := by ring

private lemma summable_altTerm_bound {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun k : ℕ => ((4 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1))) := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ (δ + 1))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have hsub : Summable (fun k : ℕ => (((4 * k + 1 : ℕ) : ℝ) ^ (δ + 1))⁻¹) :=
    hsum.comp_injective (i := fun k : ℕ => 4 * k + 1) (fun a b h => by dsimp only at h; omega)
  refine hsub.congr fun k => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg (4 * k + 1))]

private lemma differentiableOn_altSum :
    DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ, altTerm k s) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀pos : 0 < s₀.re := hs₀
  set δ := s₀.re / 2 with hδ_def
  have hδ : 0 < δ := half_pos hs₀pos
  have hdiff_ball : DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ, altTerm k s) (Metric.ball s₀ δ) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k : ℕ => 2 * (‖s₀‖ + δ) * ((4 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)))
      ((summable_altTerm_bound hδ).mul_left _)
      (fun k => ?_) Metric.isOpen_ball (fun k w hw => ?_)
    · refine Differentiable.differentiableOn ?_
      have h1 : 0 < (((4 * k + 1 : ℕ) : ℂ)).re := by simp; positivity
      have h2 : 0 < (((4 * k + 3 : ℕ) : ℂ)).re := by simp; positivity
      intro z
      exact ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl h1)).sub
        ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl h2))
    · have hwre : δ ≤ w.re := by
        have h1 : |w.re - s₀.re| ≤ ‖w - s₀‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s₀)
        have h2 : ‖w - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
        linarith
      have hwnorm : ‖w‖ ≤ ‖s₀‖ + δ := by
        have h2 : ‖w - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        calc ‖w‖ = ‖(w - s₀) + s₀‖ := by ring_nf
          _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
          _ ≤ ‖s₀‖ + δ := by linarith
      have h1 := norm_altTerm_le k (lt_of_lt_of_le hδ hwre)
      have hpow : ((4 * k + 1 : ℕ) : ℝ) ^ (-(w.re + 1)) ≤
          ((4 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)
      calc
        ‖altTerm k w‖ ≤ 2 * ‖w‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(w.re + 1)) := h1
        _ ≤ 2 * (‖s₀‖ + δ) * ((4 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by
          exact mul_le_mul (by linarith) hpow (by positivity) (by positivity)
  exact (hdiff_ball.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))).differentiableWithinAt

private lemma L4_eq_altSum_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    L4 s = ∑' k : ℕ, altTerm k s := by
  rw [L4, DirichletCharacter.LFunction_eq_LSeries χ4 hs]
  have hsumL : LSeriesSummable (fun n : ℕ => χ4 (n : ZMod 4)) s :=
    ZMod.LSeriesSummable_of_one_lt_re χ4 hs
  have hsumAlt : Summable (fun k : ℕ => altTerm k s) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => 2 * ‖s‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)))
      ((summable_altTerm_bound (by linarith)).mul_left _) (fun k => norm_altTerm_le k (by linarith))
  have hpart : ∀ K : ℕ,
      ∑ n ∈ Finset.range (4 * K), LSeries.term (fun n : ℕ => χ4 (n : ZMod 4)) s n =
      ∑ k ∈ Finset.range K, altTerm k s := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [show 4 * (K + 1) = 4 * K + 4 by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
      have h0 : χ4 ((4 * K : ℕ) : ZMod 4) = 0 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
        split_ifs <;> norm_num <;> omega
      have h1 : χ4 ((4 * K + 1 : ℕ) : ZMod 4) = 1 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
        split_ifs <;> norm_num <;> omega
      have h2 : χ4 ((4 * K + 2 : ℕ) : ZMod 4) = 0 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
        split_ifs <;> norm_num <;> omega
      have h3 : χ4 ((4 * K + 3 : ℕ) : ZMod 4) = -1 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
        split_ifs <;> norm_num <;> omega
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
      simp only [LSeries.term_of_ne_zero (show 4 * K + 1 ≠ 0 by omega),
        LSeries.term_of_ne_zero (show 4 * K + 2 ≠ 0 by omega),
        LSeries.term_of_ne_zero (show 4 * K + 3 ≠ 0 by omega)]
      have ht0 : LSeries.term (fun n : ℕ => χ4 (n : ZMod 4)) s (4 * K) = 0 := by
        by_cases hK : 4 * K = 0
        · simp [hK]
        · rw [LSeries.term_of_ne_zero hK, h0, zero_div]
      rw [ht0, h1, h2, h3]
      simp only [zero_add, altTerm, div_eq_mul_inv, cpow_neg]
      ring
  have ht1 : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range (4 * K),
      LSeries.term (fun n : ℕ => χ4 (n : ZMod 4)) s n) atTop (𝓝 (LSeries (fun n : ℕ => χ4 (n : ZMod 4)) s)) :=
    hsumL.hasSum.tendsto_sum_nat.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
  have ht2 : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, altTerm k s) atTop
      (𝓝 (∑' k : ℕ, altTerm k s)) :=
    hsumAlt.hasSum.tendsto_sum_nat
  simp_rw [hpart] at ht1
  exact tendsto_nhds_unique ht1 ht2

private lemma L4_eq_altSum {s : ℂ} (hs : 0 < s.re) :
    L4 s = ∑' k : ℕ, altTerm k s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0
  have han1 : AnalyticOnNhd ℂ L4 {z : ℂ | 0 < z.re} :=
    L4_differentiable.differentiableOn.analyticOnNhd hopen
  have han2 : AnalyticOnNhd ℂ (fun z => ∑' k : ℕ, altTerm k z) {z : ℂ | 0 < z.re} :=
    differentiableOn_altSum.analyticOnNhd hopen
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hev : L4 =ᶠ[𝓝 (2 : ℂ)] (fun z => ∑' k : ℕ, altTerm k z) := by
    refine Filter.eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)) ?_
    intro z hz
    exact L4_eq_altSum_of_one_lt_re hz
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2 hconv.isPreconnected h2 hev hs

private lemma L4_real_pos {σ : ℝ} (hσ : 0 < σ) :
    ∃ x : ℝ, 0 < x ∧ L4 (σ : ℂ) = (x : ℂ) ∧
      ((1 : ℝ) - (3 : ℝ) ^ (-σ) ≤ x) := by
  rw [L4_eq_altSum (by simpa using hσ)]
  have hterm : ∀ k : ℕ, altTerm k (σ : ℂ) =
      (((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ) : ℝ) := by
    intro k
    dsimp [altTerm]
    rw [Complex.ofReal_sub, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast, Complex.ofReal_natCast,
      Complex.ofReal_neg]
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum]
  have hsum : Summable (fun k : ℕ => ((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ)) := by
    have hC : Summable (fun k : ℕ => altTerm k (σ : ℂ)) :=
      Summable.of_norm_bounded
        (g := fun k : ℕ => 2 * ‖(σ : ℂ)‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(σ + 1)))
        ((summable_altTerm_bound hσ).mul_left _)
        (fun k => by simpa using norm_altTerm_le k (s := (σ : ℂ)) (by simpa using hσ))
    have hre := Complex.reCLM.summable hC
    refine hre.congr fun k => ?_
    simp [hterm k]
  have hnn : ∀ k : ℕ, 0 ≤ ((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ) := by
    intro k
    have hlt : ((4 * k + 3 : ℕ) : ℝ) ^ (-σ) < ((4 * k + 1 : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_lt_rpow_of_neg (by positivity) (by norm_cast; omega) (by linarith)
    linarith
  have h0pos : 0 < ((4 * 0 + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * 0 + 3 : ℕ) : ℝ) ^ (-σ) := by
    have hlt : ((4 * 0 + 3 : ℕ) : ℝ) ^ (-σ) < ((4 * 0 + 1 : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_lt_rpow_of_neg (by positivity) (by norm_cast) (by linarith)
    linarith
  refine ⟨∑' k : ℕ, (((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ)),
    hsum.tsum_pos hnn 0 h0pos, rfl, ?_⟩
  have hle := hsum.le_tsum 0 (fun k _ => hnn k)
  simpa using hle

private lemma L4_real_ne_zero {σ : ℝ} (hσ : 0 < σ) : L4 (σ : ℂ) ≠ 0 := by
  obtain ⟨x, hxpos, hxeq, _⟩ := L4_real_pos hσ
  rw [hxeq, ne_eq, Complex.ofReal_eq_zero]
  exact hxpos.ne'

private lemma norm_L4_le_of_half_le_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → ‖L4 s‖ ≤ C * ‖s‖ := by
  have hsum : Summable (fun k : ℕ => ((4 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + 1 : ℝ))) :=
    summable_altTerm_bound (by norm_num : (0 : ℝ) < 1 / 2)
  let S := ∑' k : ℕ, ((4 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + 1 : ℝ))
  have hSpos : 0 < S := hsum.tsum_pos (fun k => by positivity) 0 (by positivity)
  refine ⟨2 * S, by positivity, fun s hs => ?_⟩
  rw [L4_eq_altSum (by linarith)]
  have hnorm_sum : Summable (fun k : ℕ => 2 * ‖s‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + 1 : ℝ))) :=
    hsum.mul_left _
  have hle : ∀ k : ℕ, ‖altTerm k s‖ ≤ 2 * ‖s‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + 1 : ℝ)) := by
    intro k
    refine (norm_altTerm_le k (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)) (by positivity)
  have h1 := norm_tsum_le_tsum_norm (Summable.of_norm_bounded hnorm_sum hle).norm
  have h2 := Summable.tsum_le_tsum hle (Summable.of_norm_bounded hnorm_sum hle).norm hnorm_sum
  calc
    ‖∑' k : ℕ, altTerm k s‖ ≤ ∑' k : ℕ, ‖altTerm k s‖ := h1
    _ ≤ ∑' k : ℕ, 2 * ‖s‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(1 / 2 + 1 : ℝ)) := h2
    _ = 2 * ‖s‖ * S := tsum_mul_left
    _ = (2 * S) * ‖s‖ := by ring

private lemma differentiableAt_conj_comp {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (starRingEnd ℂ z)) :
    DifferentiableAt ℂ (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) z := by
  have h1 := hf.hasDerivAt
  have h2 : HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w)))
      (starRingEnd ℂ (deriv f (starRingEnd ℂ z))) z := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at h1 ⊢
    have hconj0 : Tendsto (fun t : ℂ => starRingEnd ℂ t) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
          exact (map_ne_zero (starRingEnd ℂ)).mpr ht
    have hcomp := (Complex.continuous_conj.tendsto _).comp (h1.comp hconj0)
    refine hcomp.congr fun t => ?_
    simp only [Function.comp_apply, smul_eq_mul, map_mul, map_inv₀, map_sub, map_add,
      Complex.conj_conj]
  exact h2.differentiableAt

private lemma L4_conj (s : ℂ) : L4 (starRingEnd ℂ s) = starRingEnd ℂ (L4 s) := by
  have hopen : IsOpen (Set.univ : Set ℂ) := isOpen_univ
  have hconj_diff : Differentiable ℂ (fun z => starRingEnd ℂ (L4 (starRingEnd ℂ z))) :=
    fun z => differentiableAt_conj_comp (L4_differentiable (starRingEnd ℂ z))
  have han1 : AnalyticOnNhd ℂ L4 Set.univ := L4_differentiable.differentiableOn.analyticOnNhd hopen
  have han2 : AnalyticOnNhd ℂ (fun z => starRingEnd ℂ (L4 (starRingEnd ℂ z))) Set.univ :=
    hconj_diff.differentiableOn.analyticOnNhd hopen
  have hev : L4 =ᶠ[𝓝 (2 : ℂ)] (fun z => starRingEnd ℂ (L4 (starRingEnd ℂ z))) := by
    refine Filter.eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 0 < (2 : ℂ).re)) ?_
    intro z hz
    dsimp only
    have hzc : 0 < (starRingEnd ℂ z).re := by simpa using hz
    rw [L4_eq_altSum hz, L4_eq_altSum hzc]
    have hsum : Summable (fun k : ℕ => altTerm k (starRingEnd ℂ z)) :=
      Summable.of_norm_bounded
        (g := fun k : ℕ => 2 * ‖starRingEnd ℂ z‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-((starRingEnd ℂ z).re + 1)))
        ((summable_altTerm_bound hzc).mul_left _) (fun k => norm_altTerm_le k hzc)
    have hconj_tsum : ∑' k : ℕ, starRingEnd ℂ (altTerm k (starRingEnd ℂ z)) =
        starRingEnd ℂ (∑' k : ℕ, altTerm k (starRingEnd ℂ z)) :=
      (hsum.hasSum.map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj).tsum_eq
    rw [← hconj_tsum]
    refine tsum_congr fun k => ?_
    dsimp [altTerm]
    have hnat_conj : ∀ m : ℕ, ((m : ℂ) ^ (-z)) = starRingEnd ℂ ((m : ℂ) ^ (-(starRingEnd ℂ z))) := by
      intro m
      have harg : Complex.arg ((m : ℝ) : ℂ) ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg m)]; exact Real.pi_pos.ne
      have h1 := Complex.cpow_conj ((m : ℝ) : ℂ) (-(starRingEnd ℂ z)) harg
      simp only [Complex.ofReal_natCast, map_natCast, map_neg, Complex.conj_conj] at h1
      exact h1
    rw [map_sub, hnat_conj (4 * k + 1), hnat_conj (4 * k + 3)]
  have heq := han1.eqOn_of_preconnected_of_eventuallyEq han2 isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev (Set.mem_univ (starRingEnd ℂ s))
  simpa using heq

private lemma xi4_functional_eq (s : ℂ) :
    xi4 (1 - s) = (4 : ℂ) ^ (s - 1 / 2) * xi4 s := by
  have hfe := χ4_isPrimitive.completedLFunction_one_sub s
  rw [χ4_inv] at hfe
  have hhalf_ne : xi4 (1 / 2 : ℂ) ≠ 0 := by
    rw [xi4_eq_L4_mul_gammaℝ (by norm_num)]
    have hL : L4 (1 / 2 : ℂ) ≠ 0 := by
      simpa using L4_real_ne_zero (by norm_num : (0 : ℝ) < 1 / 2)
    have hG : Complex.Gammaℝ ((1 / 2 : ℂ) + 1) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
    exact mul_ne_zero hL hG
  have hroot : DirichletCharacter.rootNumber χ4 = 1 := by
    have h0 := χ4_isPrimitive.completedLFunction_one_sub (1 / 2 : ℂ)
    rw [χ4_inv] at h0
    have h1 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
    have h2 : (1 / 2 : ℂ) - 1 / 2 = 0 := by norm_num
    rw [h1, h2, Complex.cpow_zero, one_mul] at h0
    have h3 : (DirichletCharacter.rootNumber χ4 - 1) * xi4 (1 / 2 : ℂ) = 0 := by
      dsimp [xi4] at hhalf_ne ⊢
      linear_combination -h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hhalf_ne)
  dsimp [xi4] at hfe ⊢
  rw [hfe, hroot, mul_one]

private lemma xi4_conj (s : ℂ) : xi4 (starRingEnd ℂ s) = starRingEnd ℂ (xi4 s) := by
  have hconj_diff : Differentiable ℂ (fun z => starRingEnd ℂ (xi4 (starRingEnd ℂ z))) :=
    fun z => differentiableAt_conj_comp (xi4_differentiable (starRingEnd ℂ z))
  have han1 : AnalyticOnNhd ℂ xi4 Set.univ := xi4_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have han2 : AnalyticOnNhd ℂ (fun z => starRingEnd ℂ (xi4 (starRingEnd ℂ z))) Set.univ :=
    hconj_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hev : xi4 =ᶠ[𝓝 (2 : ℂ)] (fun z => starRingEnd ℂ (xi4 (starRingEnd ℂ z))) := by
    refine Filter.eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 0 < (2 : ℂ).re)) ?_
    intro z hz
    dsimp only
    have hzre : 0 < z.re := hz
    have hzc : 0 < (starRingEnd ℂ z).re := by simpa using hzre
    rw [xi4_eq_L4_mul_gammaℝ (by linarith), xi4_eq_L4_mul_gammaℝ (by linarith), map_mul,
      L4_conj, Complex.conj_conj]
    congr 1
    simp only [Complex.Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
    have harg : Complex.arg (Real.pi : ℂ) ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
    have hpi_conj : (Real.pi : ℂ) ^ (-(z + 1) / 2) =
        starRingEnd ℂ ((Real.pi : ℂ) ^ (-((starRingEnd ℂ z) + 1) / 2)) := by
      have h1 := Complex.cpow_conj (Real.pi : ℂ) (-((starRingEnd ℂ z) + 1) / 2) harg
      simp only [Complex.conj_ofReal, map_div₀, map_neg, map_add, map_one, map_ofNat,
        Complex.conj_conj] at h1
      exact h1
    rw [hpi_conj]
    simp [map_div₀, map_add, map_one, map_ofNat]
  have heq := han1.eqOn_of_preconnected_of_eventuallyEq han2 isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev (Set.mem_univ (starRingEnd ℂ s))
  simpa using heq


/-- Real-valued prime-power coefficient underlying log L(s, χ4). -/
noncomputable def aCoeff (n : ℕ) : ℝ :=
  (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / Real.log n

/-- The weighted prime-power sum appearing in the hypothesis. -/
noncomputable def JVal (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 n),
    ∑ p ∈ (Nat.primesLE n).filter (fun p => p ^ (j + 1) ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ (j + 1) / (j + 1 : ℕ)

private lemma L4_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : L4 s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ4 (Or.inl χ4_ne_one) hs
private lemma aCoeff_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    aCoeff (p ^ m) = (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ m / (m : ℝ) := by
  dsimp [aCoeff]
  rw [Nat.cast_pow, map_pow, Int.cast_pow, ArithmeticFunction.vonMangoldt_apply_pow hm.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  field_simp [hlog]

private lemma aCoeff_eq_zero_of_not_isPrimePow {k : ℕ} (hk : ¬ IsPrimePow k) :
    aCoeff k = 0 := by
  dsimp [aCoeff]
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hk, mul_zero, zero_div]

private lemma JVal_eq_sum_aCoeff (n : ℕ) :
    JVal n = ∑ k ∈ Finset.Icc 1 n, aCoeff k := by
  have h1 : ∑ k ∈ Finset.Icc 1 n, aCoeff k =
      ∑ k ∈ (Finset.Icc 1 n).filter IsPrimePow, aCoeff k := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro k hk hnot
    exact aCoeff_eq_zero_of_not_isPrimePow (by simpa [hk] using hnot)
  rw [h1]
  dsimp [JVal]
  rw [← Finset.sum_sigma (Finset.range (Nat.log 2 n))
    (fun j => (Nat.primesLE n).filter (fun p => p ^ (j + 1) ≤ n))
    (fun x : Σ _ : ℕ, ℕ => (ZMod.χ₄ (x.2 : ZMod 4) : ℝ) ^ (x.1 + 1) / (x.1 + 1 : ℕ))]
  refine Finset.sum_nbij (fun x => x.2 ^ (x.1 + 1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_primesLE,
      Finset.mem_Icc] at hx ⊢
    obtain ⟨_, ⟨⟨_, hp⟩, hpow⟩⟩ := hx
    refine ⟨⟨Nat.one_le_pow _ _ hp.pos, hpow⟩, hp.isPrimePow.pow (Nat.succ_ne_zero _)⟩
  · intro x hx y hy hxy
    dsimp only at hxy
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
      Nat.mem_primesLE] at hx hy
    have hpx : x.2.Prime := hx.2.1.2
    have hpy : y.2.Prime := hy.2.1.2
    have hpeq : x.2 = y.2 := by
      have hdvd : x.2 ∣ y.2 ^ (y.1 + 1) := hxy ▸ dvd_pow_self x.2 (Nat.succ_ne_zero _)
      exact (Nat.prime_dvd_prime_iff_eq hpx hpy).mp (hpx.dvd_of_dvd_pow hdvd)
    rw [hpeq] at hxy
    have hexp : x.1 + 1 = y.1 + 1 := Nat.pow_right_injective hpy.two_le hxy
    have hfst : x.1 = y.1 := Nat.succ.inj hexp
    cases x; cases y
    simp only [Sigma.mk.inj_iff, heq_eq_eq]
    exact ⟨hfst, hpeq⟩
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, hpp⟩ := hk
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, m, hp, hm, rfl⟩ := hpp
    have hpn : p ≤ n := le_trans (Nat.le_self_pow hm.ne' p) hkn
    have h2m : 2 ^ m ≤ n := le_trans (Nat.pow_le_pow_left hp.two_le m) hkn
    have hmlog : m ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) h2m
    refine ⟨⟨m - 1, p⟩, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
        Nat.mem_primesLE]
      refine ⟨by omega, ⟨⟨hpn, hp⟩, ?_⟩⟩
      rwa [Nat.sub_add_cancel hm]
    · simp [Nat.sub_add_cancel hm]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_primesLE] at hx
    exact (aCoeff_prime_pow hx.2.1.2 (Nat.succ_pos _)).symm

private lemma abs_aCoeff_le_one (n : ℕ) : |aCoeff n| ≤ 1 := by
  by_cases hn : n ≤ 1
  · have hpp : ¬ IsPrimePow n := by
      interval_cases n
      · exact not_isPrimePow_zero
      · exact not_isPrimePow_one
    rw [aCoeff_eq_zero_of_not_isPrimePow hpp, abs_zero]
    norm_num
  · push Not at hn
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hχ : |(ZMod.χ₄ (n : ZMod 4) : ℝ)| ≤ 1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> norm_num
    have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hvm1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    dsimp [aCoeff]
    rw [abs_div, abs_mul, abs_of_nonneg hvm0, abs_of_pos hlogpos, div_le_one hlogpos]
    calc
      |(ZMod.χ₄ (n : ZMod 4) : ℝ)| * ArithmeticFunction.vonMangoldt n
          ≤ 1 * Real.log (n : ℝ) := mul_le_mul hχ hvm1 hvm0 zero_le_one
      _ = Real.log (n : ℝ) := one_mul _

private lemma abs_JVal_le (n : ℕ) : |JVal n| ≤ (n : ℝ) := by
  rw [JVal_eq_sum_aCoeff]
  calc
    |∑ k ∈ Finset.Icc 1 n, aCoeff k| ≤ ∑ k ∈ Finset.Icc 1 n, |aCoeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun k _ => abs_aCoeff_le_one k
    _ = (n : ℝ) := by simp

private lemma L4_eq_exp_mul_integral {s : ℂ} (hs : 1 < s.re) :
    L4 s = Complex.exp (s * ∫ t in Set.Ioi (1 : ℝ),
      (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  rw [L4, DirichletCharacter.LFunction_eq_LSeries χ4 hs,
    ← DirichletCharacter.LSeries_eq_exp_LSeries χ4 hs]
  congr 1
  have hcongr : (fun n : ℕ => χ4 (n : ZMod 4) * (ArithmeticFunction.vonMangoldt n : ℂ) /
      (Real.log n : ℂ)) = (fun n : ℕ => (aCoeff n : ℂ)) := by
    ext n; rw [χ4_apply_nat]; simp [aCoeff]
  rw [hcongr]
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(aCoeff k : ℂ)‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le atTop fun n => ?_
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _), Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg n)]
    calc
      ∑ k ∈ Finset.Icc 1 n, ‖(aCoeff k : ℂ)‖
          ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_aCoeff_le_one k
      _ = (n : ℝ) := by simp
  rw [LSeries_eq_mul_integral' (fun n => (aCoeff n : ℂ)) zero_le_one hs hO]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← Complex.ofReal_sum, JVal_eq_sum_aCoeff]

/- ### Step 2: Holomorphic antiderivative and logarithm on any open convex set -/

private lemma exists_holomorphic_antideriv_on_convex {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ U) {c : ℂ} (hc : c ∈ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ F : ℂ → ℂ, F c = 0 ∧ ∀ z ∈ U, HasDerivAt F (f z) z := by
  let F : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, f (c + (t : ℂ) * (z - c)) * (z - c)
  refine ⟨F, by simp [F], fun z0 hz0 => ?_⟩
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hball_half : Metric.closedBall z0 (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  let K : Set ℂ := (fun p : ℝ × ℂ => c + (p.1 : ℂ) * (p.2 - c)) ''
    (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z0 (r / 2))
  have hK_sub : K ⊆ U := by
    rintro _ ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    dsimp only
    have h1 : c + (t : ℂ) * (w - c) = (1 - t) • c + t • w := by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [h1]
    exact hconv hc (hball_half hw) (by linarith [ht.2]) ht.1 (by ring)
  have hK_comp : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall z0 (r / 2))).image (by fun_prop)
  have hfc_cont : ContinuousOn f K := (hf.continuousOn).mono hK_sub
  have hdf_diff : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
  have hdf_cont : ContinuousOn (deriv f) K := (hdf_diff.continuousOn).mono hK_sub
  obtain ⟨M1, hM1⟩ := hK_comp.exists_bound_of_continuousOn hfc_cont
  obtain ⟨M2, hM2⟩ := hK_comp.exists_bound_of_continuousOn hdf_cont
  let B : ℝ := max 0 M2 * (‖z0 - c‖ + r / 2) + max 0 M1
  let G : ℂ → ℝ → ℂ := fun z t => f (c + (t : ℂ) * (z - c)) * (z - c)
  let G' : ℂ → ℝ → ℂ := fun z t =>
    deriv f (c + (t : ℂ) * (z - c)) * (t : ℂ) * (z - c) + f (c + (t : ℂ) * (z - c))
  have hmemK : ∀ z ∈ Metric.ball z0 (r / 2), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c + (t : ℂ) * (z - c) ∈ K := fun z hz t ht =>
    ⟨(t, z), ⟨ht, Metric.ball_subset_closedBall hz⟩, rfl⟩
  have hG_deriv : ∀ z ∈ Metric.ball z0 (r / 2), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun w => G w t) (G' z t) z := by
    intro z hz t ht
    have hpt : c + (t : ℂ) * (z - c) ∈ U := hK_sub (hmemK z hz t ht)
    have hf_at : HasDerivAt f (deriv f (c + (t : ℂ) * (z - c))) (c + (t : ℂ) * (z - c)) :=
      (hf.differentiableAt (hU.mem_nhds hpt)).hasDerivAt
    have hin : HasDerivAt (fun w => c + (t : ℂ) * (w - c)) (t : ℂ) z := by
      have h1 := ((hasDerivAt_id z).sub_const c).const_mul (t : ℂ)
      simpa using h1.const_add c
    have hcomp := hf_at.comp z hin
    have hsub : HasDerivAt (fun w => w - c) 1 z := (hasDerivAt_id z).sub_const c
    have hmul := hcomp.mul hsub
    refine hmul.congr_deriv ?_
    dsimp [G']; ring
  have hG_bound : ∀ z ∈ Metric.ball z0 (r / 2), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖G' z t‖ ≤ B := by
    intro z hz t ht
    have hpt := hmemK z hz t ht
    have h1 : ‖deriv f (c + (t : ℂ) * (z - c))‖ ≤ max 0 M2 :=
      le_trans (hM2 _ hpt) (le_max_right _ _)
    have h2 : ‖f (c + (t : ℂ) * (z - c))‖ ≤ max 0 M1 :=
      le_trans (hM1 _ hpt) (le_max_right _ _)
    have h3 : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2
    have h4 : ‖z - c‖ ≤ ‖z0 - c‖ + r / 2 := by
      have hzdist : ‖z - z0‖ < r / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      calc ‖z - c‖ = ‖(z - z0) + (z0 - c)‖ := by ring_nf
        _ ≤ ‖z - z0‖ + ‖z0 - c‖ := norm_add_le _ _
        _ ≤ ‖z0 - c‖ + r / 2 := by linarith
    dsimp [G']
    calc
      ‖deriv f (c + (t : ℂ) * (z - c)) * (t : ℂ) * (z - c) + f (c + (t : ℂ) * (z - c))‖
          ≤ ‖deriv f (c + (t : ℂ) * (z - c)) * (t : ℂ) * (z - c)‖ +
              ‖f (c + (t : ℂ) * (z - c))‖ := norm_add_le _ _
      _ = ‖deriv f (c + (t : ℂ) * (z - c))‖ * ‖(t : ℂ)‖ * ‖z - c‖ +
              ‖f (c + (t : ℂ) * (z - c))‖ := by rw [norm_mul, norm_mul]
      _ ≤ (max 0 M2) * 1 * (‖z0 - c‖ + r / 2) + max 0 M1 := by
            have hmul1 : ‖deriv f (c + (t : ℂ) * (z - c))‖ * ‖(t : ℂ)‖ ≤ max 0 M2 * 1 :=
              mul_le_mul h1 h3 (norm_nonneg _) (le_max_left _ _)
            exact add_le_add (mul_le_mul hmul1 h4 (norm_nonneg _) (by positivity)) h2
      _ = B := by dsimp [B]; ring
  have hcont_G : ∀ z ∈ Metric.ball z0 (r / 2), ContinuousOn (G z) (Set.Icc 0 1) := fun z hz =>
    (hfc_cont.comp (by fun_prop) (fun t ht => hmemK z hz t ht)).mul continuousOn_const
  have hcont_G' : ContinuousOn (G' z0) (Set.Icc 0 1) := by
    have hz0m : z0 ∈ Metric.ball z0 (r / 2) := Metric.mem_ball_self (by positivity)
    exact (((hdf_cont.comp (by fun_prop) (fun t ht => hmemK z0 hz0m t ht)).mul
      (Complex.continuous_ofReal.continuousOn)).mul continuousOn_const).add
      (hfc_cont.comp (by fun_prop) (fun t ht => hmemK z0 hz0m t ht))
  have hz0m : z0 ∈ Metric.ball z0 (r / 2) := Metric.mem_ball_self (by positivity)
  have hciB : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 := intervalIntegrable_const
  have hdiff_int := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z0 (r / 2)) (bound := fun _ => B)
    (Metric.isOpen_ball.mem_nhds hz0m)
    (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz0m) fun z hz =>
      ((hcont_G z hz).mono (by rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self)).aestronglyMeasurable
        measurableSet_uIoc)
    ((hcont_G z0 hz0m).intervalIntegrable_of_Icc zero_le_one)
    ((hcont_G'.mono (by rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht z hz =>
      hG_bound z hz t (Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le zero_le_one] at ht)))
    hciB
    (Filter.Eventually.of_forall fun t ht z hz =>
      hG_deriv z hz t (Set.Ioc_subset_Icc_self (by rwa [Set.uIoc_of_le zero_le_one] at ht)))).2
  -- Evaluate ∫_0^1 G' z0 t dt = f z0 by FTC on t ↦ t * f (c + t * (z0 - c))
  have hftc_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (s : ℂ) * f (c + (s : ℂ) * (z0 - c))) (G' z0 t) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpt : c + (t : ℂ) * (z0 - c) ∈ U := hK_sub (hmemK z0 hz0m t ht)
    have hf_at : HasDerivAt f (deriv f (c + (t : ℂ) * (z0 - c))) (c + (t : ℂ) * (z0 - c)) :=
      (hf.differentiableAt (hU.mem_nhds hpt)).hasDerivAt
    have hin : HasDerivAt (fun s : ℝ => c + (s : ℂ) * (z0 - c)) (z0 - c) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h1 := (h0.mul_const (z0 - c)).const_add c
      simpa using h1
    have hcomp := hf_at.comp t hin
    have hmul := (Complex.ofRealCLM.hasDerivAt (x := t)).mul hcomp
    refine hmul.congr_deriv ?_
    dsimp [G']; ring
  have hint_ftc : IntervalIntegrable (G' z0) volume 0 1 :=
    hcont_G'.intervalIntegrable_of_Icc zero_le_one
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hftc_deriv hint_ftc
  have hval : ∫ t in (0 : ℝ)..1, G' z0 t = f z0 := by
    rw [heval]; simp
  exact hdiff_int.congr_deriv hval

private lemma exists_holomorphic_log_on_convex {U : Set ℂ} (hU : IsOpen U)
    (hconv : Convex ℝ U) {c : ℂ} (hc : c ∈ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) (v0 : ℂ) (hv0 : Complex.exp v0 = f c) :
    ∃ L : ℂ → ℂ, L c = v0 ∧ (∀ z ∈ U, HasDerivAt L (deriv f z / f z) z) ∧
      ∀ z ∈ U, Complex.exp (L z) = f z := by
  have hld : DifferentiableOn ℂ (fun z => deriv f z / f z) U :=
    (hf.deriv hU).div hf hne
  obtain ⟨F, hFc, hFderiv⟩ := exists_holomorphic_antideriv_on_convex hU hconv hc hld
  let L : ℂ → ℂ := fun z => v0 + F z
  have hLderiv : ∀ z ∈ U, HasDerivAt L (deriv f z / f z) z := fun z hz =>
    (hFderiv z hz).const_add v0
  have hconst : ∀ z ∈ U, f z * Complex.exp (-L z) = 1 := by
    have hQd : ∀ z ∈ U, HasDerivAt (fun w => f w * Complex.exp (-L w)) 0 z := by
      intro z hz
      have hf' := (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
      have hE' : HasDerivAt (fun w => Complex.exp (-L w))
          (Complex.exp (-L z) * -(deriv f z / f z)) z := ((hLderiv z hz).neg).cexp
      have hmul : HasDerivAt (fun w => f w * Complex.exp (-L w))
          (deriv f z * Complex.exp (-L z) + f z * (Complex.exp (-L z) * -(deriv f z / f z))) z :=
        hf'.mul hE'
      have hzero : deriv f z * Complex.exp (-L z) +
          f z * (Complex.exp (-L z) * -(deriv f z / f z)) = 0 := by
        have hfz := hne z hz
        field_simp [hfz]; ring
      exact hmul.congr_deriv hzero
    intro z hz
    have hQeq := hconv.is_const_of_fderivWithin_eq_zero
      (f := fun w => f w * Complex.exp (-L w))
      (fun w hw => (hQd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [fderivWithin_of_isOpen hU hw, (hQd w hw).hasFDerivAt.fderiv]; simp)
      hz hc
    rw [hQeq]
    simp [L, hFc, ← hv0, ← Complex.exp_add]
  refine ⟨L, by simp [L, hFc], hLderiv, fun z hz => ?_⟩
  have h1 := hconst z hz
  calc
    Complex.exp (L z) = 1 * Complex.exp (L z) := (one_mul _).symm
    _ = (f z * Complex.exp (-L z)) * Complex.exp (L z) := by rw [h1]
    _ = f z * (Complex.exp (-L z) * Complex.exp (L z)) := by ring
    _ = f z := by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]


private lemma exists_holomorphic_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hne : ∀ z ∈ Metric.ball c R, f z ≠ 0)
    (v0 : ℂ) (hv0 : Complex.exp v0 = f c) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball c R) ∧
      F c = v0 ∧ ∀ z ∈ Metric.ball c R, Complex.exp (F z) = f z := by
  obtain ⟨F, hFc, hFd, hFexp⟩ := exists_holomorphic_log_on_convex Metric.isOpen_ball
    (convex_ball c R) (Metric.mem_ball_self hR) hf hne v0 hv0
  exact ⟨F, fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt, hFc, hFexp⟩

/- ### Part A: Landau zero-free half-plane for upper bound on J -/

private lemma integrableOn_JVal_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have h1 : Measurable (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ)) :=
      (measurable_of_countable (fun n : ℕ => (JVal n : ℂ))).comp Nat.measurable_floor
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
      intro t ht
      exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
    exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hdom : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
  calc
    |JVal ⌊t⌋₊| * t ^ (-(s.re + 1))
        ≤ (⌊t⌋₊ : ℝ) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (abs_JVal_le _) (Real.rpow_nonneg htpos.le _)
    _ ≤ t * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le htpos.le) (Real.rpow_nonneg htpos.le _)
    _ = t ^ (-s.re) := by
          nth_rw 1 [← Real.rpow_one t]
          rw [← Real.rpow_add htpos]
          congr 1; ring

private lemma integral_Ioc_JVal_eq_sum (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    s * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      ∑ m ∈ Finset.Ico 1 N, (JVal m : ℂ) * (((m : ℂ) ^ (-s)) - (((m + 1 : ℕ) : ℂ) ^ (-s))) := by
  have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  induction N, hN using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hsplit : ∫ t in Set.Ioc (1 : ℝ) ((k + 1 : ℕ) : ℝ),
        (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (∫ t in Set.Ioc (1 : ℝ) (k : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        (∫ t in Set.Ioc (k : ℝ) ((k + 1 : ℕ) : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkk1 : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      have hint1 : IntegrableOn (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
          (Set.Ioc (1 : ℝ) ((k + 1 : ℕ) : ℝ)) := by
        have hmeas : AEStronglyMeasurable
            (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)))
            (volume.restrict (Set.Ioc (1 : ℝ) ((k + 1 : ℕ) : ℝ))) := by
          have hm1 : Measurable (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ)) :=
            (measurable_of_countable (fun n : ℕ => (JVal n : ℂ))).comp Nat.measurable_floor
          have hm2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1)))
              (Set.Ioc (1 : ℝ) ((k + 1 : ℕ) : ℝ)) := fun t ht =>
            (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (zero_lt_one.trans ht.1).ne')).continuousWithinAt
          exact hm1.aestronglyMeasurable.mul (hm2.aestronglyMeasurable measurableSet_Ioc)
        refine (integrableOn_const (C := ((k + 1 : ℕ) : ℝ))
          (hs := measure_Ioc_lt_top.ne)).mono' hmeas ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht1 : 1 < t := ht.1
        have htpos : 0 < t := zero_lt_one.trans ht1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
        have hpow : t ^ (-(s.re + 1)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
        calc
          |JVal ⌊t⌋₊| * t ^ (-(s.re + 1))
              ≤ (⌊t⌋₊ : ℝ) * 1 := mul_le_mul (abs_JVal_le _) hpow (Real.rpow_nonneg htpos.le _) (Nat.cast_nonneg _)
          _ ≤ t := by rw [mul_one]; exact Nat.floor_le htpos.le
          _ ≤ ((k + 1 : ℕ) : ℝ) := ht.2
      have hunion : Set.Ioc (1 : ℝ) (k : ℝ) ∪ Set.Ioc (k : ℝ) ((k + 1 : ℕ) : ℝ) =
          Set.Ioc (1 : ℝ) ((k + 1 : ℕ) : ℝ) := Set.Ioc_union_Ioc_eq_Ioc h1k hkk1
      rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hint1.mono_set (Set.Ioc_subset_Ioc_right hkk1))
        (hint1.mono_set (Set.Ioc_subset_Ioc_left h1k))]
    rw [hsplit, mul_add, ih, Finset.sum_Ico_succ_top hk]
    congr 1
    have hstep : ∫ t in Set.Ioc (k : ℝ) ((k + 1 : ℕ) : ℝ),
        (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (JVal k : ℂ) * ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), (t : ℂ) ^ (-(s + 1)) := by
      rw [integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le (by exact_mod_cast Nat.le_succ k),
        integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      have hfl : ⌊t⌋₊ = k := by
        rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) ht.1.le)]
        exact ⟨ht.1.le, by simpa using ht.2⟩
      rw [hfl]
    rw [hstep, ← mul_assoc, mul_comm s, mul_assoc]
    congr 1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    have hkk1 : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    have hderiv : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ),
        HasDerivAt (fun x : ℝ => -((x : ℂ) ^ (-s))) (s * (t : ℂ) ^ (-(s + 1))) t := by
      intro t ht
      rw [Set.uIcc_of_le hkk1] at ht
      have htpos : 0 < t := lt_of_lt_of_le hkpos ht.1
      have h1 := (hasDerivAt_ofReal_cpow_const htpos.ne' (neg_ne_zero.mpr hsne)).neg
      have heq : -(-s * (t : ℂ) ^ (-s - 1)) = s * (t : ℂ) ^ (-(s + 1)) := by
        rw [← neg_mul, neg_neg, show (-s - 1 : ℂ) = -(s + 1) by ring]
      exact h1.congr_deriv heq
    have hint : IntervalIntegrable (fun t : ℝ => s * (t : ℂ) ^ (-(s + 1))) volume
        (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hkk1]
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hkpos ht.1
      exact ((continuousAt_const).mul
        (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr htpos.ne'))).continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_const_mul] at hftc
    calc
      s * ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), (t : ℂ) ^ (-(s + 1))
          = -(((k + 1 : ℕ) : ℂ) ^ (-s)) - -((k : ℂ) ^ (-s)) := by
            simpa [Complex.ofReal_natCast] using hftc
      _ = (k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s) := by ring

private lemma integral_Ioi_sqrt_cpow {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ t in Set.Ioi (N : ℝ), (Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (N : ℂ) ^ ((1 / 2 : ℂ) - s) / (s - 1 / 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcongr : Set.EqOn (fun t : ℝ => (Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ => (t : ℂ) ^ ((1 / 2 : ℂ) - s - 1)) (Set.Ioi (N : ℝ)) := by
    intro t ht
    dsimp only
    have htpos : 0 < t := hNpos.trans ht
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow htpos.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr htpos.ne')]
    congr 1
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have hre : ((1 / 2 : ℂ) - s - 1).re < -1 := by
    simp only [sub_re, one_re, div_ofNat_re]
    linarith
  rw [integral_Ioi_cpow_of_lt hre hNpos]
  have h1 : (1 / 2 : ℂ) - s - 1 + 1 = (1 / 2 : ℂ) - s := by ring
  have h2 : -((N : ℂ) ^ ((1 / 2 : ℂ) - s)) / ((1 / 2 : ℂ) - s) =
      (N : ℂ) ^ ((1 / 2 : ℂ) - s) / (s - 1 / 2) := by
    rw [← neg_div_neg_eq, neg_neg, neg_sub]
  simpa [h1, Complex.ofReal_natCast] using h2


/-- Non-negative regularized integral kernel H(t) = 4 * sqrt(t) - J(floor(t)). -/
noncomputable def Hfun (t : ℝ) : ℝ := 4 * Real.sqrt t - JVal ⌊t⌋₊

private lemma measurable_Hfun : Measurable Hfun :=
  (measurable_const.mul Real.continuous_sqrt.measurable).sub
    ((measurable_of_countable JVal).comp Nat.measurable_floor)

private lemma Hfun_le_five_mul {t : ℝ} (ht : 1 ≤ t) : |Hfun t| ≤ 5 * t := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hsqrt : Real.sqrt t ≤ t := by
    have : Real.sqrt t ≤ Real.sqrt (t * t) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul_self ht0] at this
  calc
    |Hfun t| ≤ |4 * Real.sqrt t| + |JVal ⌊t⌋₊| := abs_sub _ _
    _ ≤ 4 * Real.sqrt t + (⌊t⌋₊ : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
      gcongr
      exact abs_JVal_le _
    _ ≤ 4 * t + t := add_le_add (by linarith) (Nat.floor_le ht0)
    _ = 5 * t := by ring
private lemma integrableOn_Hfun_log_pow {N : ℕ} (hN : 3 ≤ N) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1))) (Set.Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hδ : 0 < (σ - 1) / 2 := by linarith
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1)))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
    refine ((measurable_Hfun.abs.mul (Real.measurable_log.pow_const k)).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  have hlo := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).bound zero_lt_one
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hlo
  let T := max (N : ℝ) (max M 1)
  have hNT : (N : ℝ) ≤ T := le_max_left _ _
  have hTpos : 0 < T := lt_of_lt_of_le hNpos hNT
  have hT1 : 1 ≤ T := le_trans hN1 hNT
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hint_tail : IntegrableOn (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1)))
      (Set.Ioi T) := by
    have hdom : IntegrableOn (fun t : ℝ => 5 * t ^ (-1 - (σ - 1) / 2)) (Set.Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hTpos).const_mul 5
    refine hdom.mono' (hmeas.mono_set (Set.Ioi_subset_Ioi hNT)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt (le_trans (le_max_right M 1) (le_max_right _ _)) ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    have htM : M ≤ t := le_trans (le_trans (le_max_left M 1) (le_max_right _ _)) ht.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hb := hM t htM
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog0 k),
      Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), one_mul] at hb
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1))
          ≤ (5 * t) * t ^ ((σ - 1) / 2) * t ^ (-(σ + 1)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul (Hfun_le_five_mul ht1.le) hb (pow_nonneg hlog0 k) (by positivity))
              (Real.rpow_nonneg htpos.le _)
      _ = 5 * (t * t ^ ((σ - 1) / 2) * t ^ (-(σ + 1))) := by ring
      _ = 5 * t ^ (-1 - (σ - 1) / 2) := by
            congr 1
            nth_rw 1 [← Real.rpow_one t]
            rw [← Real.rpow_add htpos, ← Real.rpow_add htpos]
            congr 1; ring
  have hint_init : IntegrableOn (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1)))
      (Set.Ioc (N : ℝ) T) := by
    refine (integrableOn_const (C := 5 * T * (Real.log T) ^ k)
      (hs := measure_Ioc_lt_top.ne)).mono'
      (hmeas.mono_set Set.Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht.1
    have htpos : 0 < t := zero_lt_one.trans ht1
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hlogle : Real.log t ≤ Real.log T := Real.log_le_log htpos ht.2
    have hpow1 : t ^ (-(σ + 1)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1))
          ≤ (5 * t) * (Real.log T) ^ k * 1 := by
            refine mul_le_mul
              (mul_le_mul (Hfun_le_five_mul ht1.le) (pow_le_pow_left₀ hlog0 hlogle k)
                (pow_nonneg hlog0 k) (by positivity))
              hpow1 (Real.rpow_nonneg htpos.le _) (mul_nonneg (by positivity) (pow_nonneg hlogT0 k))
      _ ≤ 5 * T * (Real.log T) ^ k := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (pow_nonneg hlogT0 k)
  have hunion : Set.Ioc (N : ℝ) T ∪ Set.Ioi T = Set.Ioi (N : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hNT
  rw [← hunion]
  exact hint_init.union hint_tail

/-- The k-th formal derivative integral of g(s) = ∫_{N}^∞ H(t) t^{-(s+1)} dt. -/
noncomputable def gDeriv (N : ℕ) (k : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * ∫ t in Set.Ioi (N : ℝ),
    (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) * (t : ℂ) ^ (-(s + 1))

private lemma hasDerivAt_gDeriv {N : ℕ} (hN : 3 ≤ N) (k : ℕ) {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    HasDerivAt (gDeriv N k) (gDeriv N (k + 1) s₀) s₀ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  set δ := (s₀.re - 1) / 2 with hδ_def
  have hδ : 0 < δ := by linarith
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let F : ℂ → ℝ → ℂ := fun s t =>
    (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) * (t : ℂ) ^ (-(s + 1))
  let F' : ℂ → ℝ → ℂ := fun s t =>
    -(Hfun t : ℂ) * ((Real.log t : ℂ) ^ (k + 1)) * (t : ℂ) ^ (-(s + 1))
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ := fun s => by
    have h1 : Measurable (fun t : ℝ => (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k)) :=
      (Complex.continuous_ofReal.measurable.comp measurable_Hfun).mul
        ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).pow_const k)
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hmeas' : AEStronglyMeasurable (F' s₀) μ := by
    have h1 : Measurable (fun t : ℝ => -(Hfun t : ℂ) * ((Real.log t : ℂ) ^ (k + 1))) :=
      (Complex.continuous_ofReal.measurable.comp measurable_Hfun).neg.mul
        ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).pow_const (k + 1))
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s₀ + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hF_int : Integrable (F s₀) μ := by
    refine (integrableOn_Hfun_log_pow hN k hs₀).mono' (hmeas s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    dsimp [F]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.log_nonneg ht1.le),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
  have hbound_int : Integrable (fun t : ℝ => |Hfun t| * (Real.log t) ^ (k + 1) * t ^ (-(1 + δ + 1))) μ :=
    integrableOn_Hfun_log_pow hN (k + 1) (by linarith)
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ,
      ‖F' s t‖ ≤ |Hfun t| * (Real.log t) ^ (k + 1) * t ^ (-(1 + δ + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hsre : 1 + δ ≤ s.re := by
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_of_nonneg hlog0,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith))
      (mul_nonneg (abs_nonneg _) (pow_nonneg hlog0 (k + 1)))
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have htpos : 0 < t := hNpos.trans ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have h1 : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) s :=
      ((hasDerivAt_id s).add_const (1 : ℂ)).neg
    have hcpow : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (-(z + 1)))
        ((t : ℂ) ^ (-(s + 1)) * Complex.log (t : ℂ) * (-1)) s :=
      h1.const_cpow (Or.inl htne)
    rw [(Complex.ofReal_log htpos.le).symm] at hcpow
    have hmul := hcpow.const_mul ((Hfun t : ℂ) * ((Real.log t : ℂ) ^ k))
    have heq : (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) *
        ((t : ℂ) ^ (-(s + 1)) * (Real.log t : ℂ) * (-1)) = F' s t := by
      dsimp [F']; rw [pow_succ]; ring
    exact hmul.congr_deriv heq
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (Eventually.of_forall hmeas) hF_int hmeas' hbound hbound_int hdiff).2
  have hmul := hres.const_mul ((-1 : ℂ) ^ k)
  have hrew : (-1 : ℂ) ^ k * ∫ t, F' s₀ t ∂μ = gDeriv N (k + 1) s₀ := by
    dsimp [gDeriv, F', μ]
    have hneg : ∀ t : ℝ, -(Hfun t : ℂ) * ((Real.log t : ℂ) ^ (k + 1)) * (t : ℂ) ^ (-(s₀ + 1)) =
        (-1 : ℂ) * ((Hfun t : ℂ) * ((Real.log t : ℂ) ^ (k + 1)) * (t : ℂ) ^ (-(s₀ + 1))) := by
      intro t; ring
    simp_rw [hneg, integral_const_mul]
    rw [pow_succ]
    ring
  exact hmul.congr_deriv hrew

private lemma iteratedDeriv_gDeriv_zero {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    ∀ s : ℂ, 1 < s.re → iteratedDeriv k (gDeriv N 0) s = gDeriv N k s := by
  induction k with
  | zero =>
    intro s _
    simp [iteratedDeriv_zero]
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (gDeriv N 0) =ᶠ[𝓝 s] gDeriv N k := by
      refine Filter.eventually_of_mem
        ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs) ?_
      intro z hz
      exact ih z hz
    rw [hev.deriv_eq]
    exact (hasDerivAt_gDeriv hN k hs).deriv

private lemma differentiableOn_g0_of_integrableOn {N : ℕ} (hN : 3 ≤ N) {σ₁ : ℝ}
    (hH_nonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ Hfun t)
    (hInt : IntegrableOn (fun t : ℝ => Hfun t * t ^ (-σ₁ - 1)) (Set.Ioi (N : ℝ))) :
    DifferentiableOn ℂ (gDeriv N 0) {s : ℂ | σ₁ < s.re} := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  intro s₀ hs₀
  have hs₀gt : σ₁ < s₀.re := hs₀
  set δ := (s₀.re - σ₁) / 2 with hδ_def
  have hδ : 0 < δ := by linarith
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let F : ℂ → ℝ → ℂ := fun s t => (Hfun t : ℂ) * (t : ℂ) ^ (-(s + 1))
  let F' : ℂ → ℝ → ℂ := fun s t => -(Hfun t : ℂ) * (Real.log t : ℂ) * (t : ℂ) ^ (-(s + 1))
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (F s) μ := fun s => by
    have h1 : Measurable (fun t : ℝ => (Hfun t : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp measurable_Hfun
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hmeas' : AEStronglyMeasurable (F' s₀) μ := by
    have h1 : Measurable (fun t : ℝ => -(Hfun t : ℂ) * (Real.log t : ℂ)) :=
      (Complex.continuous_ofReal.measurable.comp measurable_Hfun).neg.mul
        (Complex.continuous_ofReal.measurable.comp Real.measurable_log)
    have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s₀ + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (hNpos.trans ht).ne')).continuousWithinAt
    exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
  have hF_int : Integrable (F s₀) μ := by
    refine hInt.mono' (hmeas s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hH_nonneg t ht),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)) (hH_nonneg t ht)
  have hbound_int : Integrable (fun t : ℝ => (1 / δ) * (Hfun t * t ^ (-σ₁ - 1))) μ :=
    hInt.const_mul (1 / δ)
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ,
      ‖F' s t‖ ≤ (1 / δ) * (Hfun t * t ^ (-σ₁ - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 < t := lt_of_le_of_lt hN1 ht
    have htpos : 0 < t := zero_lt_one.trans ht1
    have hH0 : 0 ≤ Hfun t := hH_nonneg t ht
    have hsre : σ₁ + δ ≤ s.re := by
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      linarith
    have hlog_le : Real.log t ≤ (1 / δ) * t ^ δ := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos δ)
      rw [Real.log_rpow htpos] at h1
      have h2 : δ * Real.log t ≤ t ^ δ := by linarith
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ]
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hH0, Real.norm_of_nonneg (Real.log_nonneg ht1.le),
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re]
    calc
      Hfun t * Real.log t * t ^ (-(s.re + 1))
          ≤ Hfun t * ((1 / δ) * t ^ δ) * t ^ (-(σ₁ + δ + 1)) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left hlog_le hH0)
              (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith))
              (Real.rpow_nonneg htpos.le _)
              (mul_nonneg hH0 (mul_nonneg (by positivity) (Real.rpow_nonneg htpos.le _)))
      _ = (1 / δ) * (Hfun t * (t ^ δ * t ^ (-(σ₁ + δ + 1)))) := by ring
      _ = (1 / δ) * (Hfun t * t ^ (-σ₁ - 1)) := by
            congr 2
            rw [← Real.rpow_add htpos]
            congr 1; ring
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have htpos : 0 < t := hNpos.trans ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have h1 : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) s :=
      ((hasDerivAt_id s).add_const (1 : ℂ)).neg
    have hcpow : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (-(z + 1)))
        ((t : ℂ) ^ (-(s + 1)) * Complex.log (t : ℂ) * (-1)) s :=
      h1.const_cpow (Or.inl htne)
    rw [(Complex.ofReal_log htpos.le).symm] at hcpow
    have hmul := hcpow.const_mul (Hfun t : ℂ)
    have heq : (Hfun t : ℂ) * ((t : ℂ) ^ (-(s + 1)) * (Real.log t : ℂ) * (-1)) = F' s t := by
      dsimp [F']; ring
    exact hmul.congr_deriv heq
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (Eventually.of_forall hmeas) hF_int hmeas' hbound hbound_int hdiff).2
  have hrew : (fun s : ℂ => ∫ t, F s t ∂μ) = gDeriv N 0 := by
    ext s; simp [gDeriv, F, μ]
  rw [hrew] at hres
  exact hres.differentiableAt.differentiableWithinAt

set_option maxHeartbeats 600000 in
private theorem landau_zero_free_upper
    (hJ : ∀ᶠ n : ℕ in atTop, JVal n ≤ 4 * (Real.sqrt n / Real.log n)) :
    ∀ s : ℂ, 1 / 2 < s.re → L4 s ≠ 0 := by
  by_contra hnot
  push Not at hnot
  obtain ⟨s_bad, hs_bad_re, hs_bad_zero⟩ := hnot
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hJ
  let N : ℕ := max N₀ 3
  have hN3 : 3 ≤ N := le_max_right _ _
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hH_nonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ Hfun t := by
    intro t ht
    have hfl_ge : N ≤ ⌊t⌋₊ := Nat.le_floor ht.le
    have hfl_N0 : N₀ ≤ ⌊t⌋₊ := le_trans (le_max_left _ _) hfl_ge
    have hfl_3 : 3 ≤ ⌊t⌋₊ := le_trans hN3 hfl_ge
    have hJle := hN₀ ⌊t⌋₊ hfl_N0
    have hlog_ge_one : 1 ≤ Real.log (⌊t⌋₊ : ℝ) := by
      have hexp : Real.exp 1 ≤ (⌊t⌋₊ : ℝ) := by
        have h1 := Real.exp_one_lt_d9
        have h2 : (3 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfl_3
        linarith
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
    have hsqrt_le : Real.sqrt (⌊t⌋₊ : ℝ) ≤ Real.sqrt t :=
      Real.sqrt_le_sqrt (Nat.floor_le (le_trans (by positivity) ht.le))
    have hdiv_le : Real.sqrt (⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ) ≤ Real.sqrt t := by
      calc
        Real.sqrt (⌊t⌋₊ : ℝ) / Real.log (⌊t⌋₊ : ℝ)
            ≤ Real.sqrt (⌊t⌋₊ : ℝ) / 1 :=
              div_le_div_of_nonneg_left (Real.sqrt_nonneg _) zero_lt_one hlog_ge_one
        _ = Real.sqrt (⌊t⌋₊ : ℝ) := div_one _
        _ ≤ Real.sqrt t := hsqrt_le
    dsimp [Hfun]
    linarith
  -- Finite polynomial part P(s)
  let P : ℂ → ℂ := fun s =>
    ∑ m ∈ Finset.Ico 1 N, (JVal m : ℂ) * (((m : ℂ) ^ (-s)) - (((m + 1 : ℕ) : ℂ) ^ (-s)))
  have hP_diff : Differentiable ℂ P := by
    intro z
    refine DifferentiableAt.fun_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmz : 0 < (m : ℂ).re := by simp; omega
    have hm1z : 0 < ((m + 1 : ℕ) : ℂ).re := by simp; positivity
    exact (differentiableAt_const _).mul
      (((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl hmz)).sub
        ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl hm1z)))
  -- Key identity on Re(s) > 1: L4 s = exp (-(s * g0 s) + P s + 4 * s * N^(1/2 - s) / (s - 1/2))
  let Ψ : ℂ → ℂ := fun s =>
    -(s * gDeriv N 0 s) + P s + 4 * s * ((N : ℂ) ^ ((1 / 2 : ℂ) - s) / (s - 1 / 2))
  have hL4_eq_exp_Ψ : ∀ s : ℂ, 1 < s.re → L4 s = Complex.exp (Ψ s) := by
    intro s hs
    rw [L4_eq_exp_mul_integral hs]
    congr 1
    have hint_J := integrableOn_JVal_cpow hs
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hunion : Set.Ioc (1 : ℝ) (N : ℝ) ∪ Set.Ioi (N : ℝ) = Set.Ioi (1 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi h1N
    have hsplit : ∫ t in Set.Ioi (1 : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) +
        (∫ t in Set.Ioi (N : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint_J.mono_set Set.Ioc_subset_Ioi_self)
        (hint_J.mono_set (Set.Ioi_subset_Ioi h1N))]
    have hH_int : IntegrableOn (fun t : ℝ => (Hfun t : ℂ) * (t : ℂ) ^ (-(s + 1)))
        (Set.Ioi (N : ℝ)) := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => (Hfun t : ℂ) * (t : ℂ) ^ (-(s + 1)))
          (volume.restrict (Set.Ioi (N : ℝ))) := by
        have h1 : Measurable (fun t : ℝ => (Hfun t : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp measurable_Hfun
        have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (N : ℝ)) := fun t ht =>
          (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr (lt_trans (by positivity) ht).ne')).continuousWithinAt
        exact h1.aestronglyMeasurable.mul (h2.aestronglyMeasurable measurableSet_Ioi)
      refine (integrableOn_Hfun_log_pow hN3 0 hs).mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans (by positivity) ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos htpos, neg_re, add_re, one_re, pow_zero, mul_one]
    have hsqrt_int : IntegrableOn (fun t : ℝ => (Real.sqrt t : ℂ) * (t : ℂ) ^ (-(s + 1)))
        (Set.Ioi (N : ℝ)) := by
      have hre : ((1 / 2 : ℂ) - s - 1).re < -1 := by
        simp only [sub_re, one_re, div_ofNat_re]; linarith
      have h1 := integrableOn_Ioi_cpow_of_lt hre (by positivity : (0 : ℝ) < (N : ℝ))
      refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have htpos : 0 < t := lt_trans (by positivity) ht
      dsimp only
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow htpos.le,
        ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr htpos.ne')]
      congr 1; push_cast; ring
    have hsub : ∫ t in Set.Ioi (N : ℝ), (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        4 * ((N : ℂ) ^ ((1 / 2 : ℂ) - s) / (s - 1 / 2)) - gDeriv N 0 s := by
      rw [← integral_Ioi_sqrt_cpow hNpos (by linarith), ← integral_const_mul]
      have hg0 : gDeriv N 0 s = ∫ t in Set.Ioi (N : ℝ), (Hfun t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        simp [gDeriv]
      rw [hg0, ← integral_sub (hsqrt_int.const_mul 4) hH_int]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      dsimp [Hfun]; push_cast; ring
    rw [hsplit, mul_add, integral_Ioc_JVal_eq_sum N hN1 (by linarith), hsub]
    dsimp [Ψ, P]
    ring
  -- Define σ₀ = sup of real parts of zeros of L4
  let S : Set ℝ := {σ : ℝ | ∃ t : ℝ, L4 ((σ : ℂ) + (t : ℂ) * Complex.I) = 0}
  have hS_nonempty : S.Nonempty := by
    refine ⟨s_bad.re, s_bad.im, ?_⟩
    simpa [Complex.re_add_im] using hs_bad_zero
  have hS_bdd : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro σ ⟨t, hzero⟩
    by_contra hgt
    push Not at hgt
    exact L4_ne_zero_of_one_le_re (by simp [hgt.le]) hzero
  set σ₀ := sSup S with hσ₀_def
  have hσ₀_gt : 1 / 2 < σ₀ :=
    lt_of_lt_of_le hs_bad_re (le_csSup hS_bdd ⟨s_bad.im, by simpa [Complex.re_add_im] using hs_bad_zero⟩)
  have hσ₀_le : σ₀ ≤ 1 := csSup_le hS_nonempty (fun σ hσ => by
    obtain ⟨t, hz⟩ := hσ
    by_contra hgt
    push Not at hgt
    exact L4_ne_zero_of_one_le_re (by simp [hgt.le]) hz)
  -- Since L4(σ₀) ≠ 0, L4 is nonzero on a ball around σ₀
  have hLσ₀ : L4 (σ₀ : ℂ) ≠ 0 := L4_real_ne_zero (by linarith)
  have hopen_nz : IsOpen {z : ℂ | L4 z ≠ 0} :=
    isOpen_ne_fun L4_differentiable.continuous continuous_const
  obtain ⟨r₀, hr₀pos, hr₀ball⟩ := Metric.isOpen_iff.mp hopen_nz (σ₀ : ℂ) hLσ₀
  let r : ℝ := min r₀ ((σ₀ - 1 / 2) / 2)
  have hrpos : 0 < r := lt_min hr₀pos (by linarith)
  have hr_sub : ∀ z ∈ Metric.ball (σ₀ : ℂ) r, L4 z ≠ 0 :=
    fun z hz => hr₀ball (Metric.ball_subset_ball (min_le_left _ _) hz)
  -- Choose ε > 0 small enough that B(2, 2 - σ₀ + ε) ⊆ {Re > σ₀} ∪ B(σ₀, r)
  let ε : ℝ := min (r / 2) (r ^ 2 / 8)
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_lt_r : ε < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hrpos)
  let R : ℝ := 2 - σ₀ + ε
  have hRpos : 0 < R := by linarith
  have hball_re : ∀ z ∈ Metric.ball (2 : ℂ) R, 1 / 2 < z.re := by
    intro z hz
    have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - 2)
    have h2 : ‖z - 2‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
    have hrle : r ≤ (σ₀ - 1 / 2) / 2 := min_le_right _ _
    linarith
  have hball_nz : ∀ z ∈ Metric.ball (2 : ℂ) R, L4 z ≠ 0 := by
    intro z hz
    by_cases hgt : σ₀ < z.re
    · intro hzero
      have hmem : z.re ∈ S := ⟨z.im, by simpa [Complex.re_add_im] using hzero⟩
      exact (not_le_of_gt hgt) (le_csSup hS_bdd hmem)
    · push Not at hgt
      refine hr_sub z ?_
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hre_gt : σ₀ - ε < z.re := by
        have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - 2)
        have h3 := abs_lt.mp (lt_of_le_of_lt h1 hz)
        linarith
      have hnorm2 : ‖z - 2‖ ^ 2 < R ^ 2 := by
        nlinarith [norm_nonneg (z - 2)]
      have hsq2 : ‖z - 2‖ ^ 2 = (z.re - 2) ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [sq]
      have hsqσ : ‖z - (σ₀ : ℂ)‖ ^ 2 = (z.re - σ₀) ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [sq]
      have hre_sq : (2 - σ₀) ^ 2 ≤ (z.re - 2) ^ 2 := by nlinarith
      have him_sq : z.im ^ 2 < 2 * ε * (2 - σ₀) + ε ^ 2 := by
        dsimp [R] at hnorm2
        nlinarith
      have hdiff_sq : (z.re - σ₀) ^ 2 < ε ^ 2 := by nlinarith
      have hε_le1 : ε ≤ r / 2 := min_le_left _ _
      have hε_le2 : ε ≤ r ^ 2 / 8 := min_le_right _ _
      have h2σ : 2 - σ₀ ≤ 3 / 2 := by linarith
      have htot : ‖z - (σ₀ : ℂ)‖ ^ 2 < r ^ 2 := by
        rw [hsqσ]
        have h3 : 2 * ε * (2 - σ₀) ≤ 3 * ε := by nlinarith
        have h4 : 2 * ε ^ 2 ≤ r ^ 2 / 2 := by nlinarith
        have h5 : 3 * ε ≤ 3 * r ^ 2 / 8 := by linarith
        nlinarith
      nlinarith [norm_nonneg (z - (σ₀ : ℂ))]
  -- Construct holomorphic log F of L4 on Metric.ball 2 R with F 2 = Ψ 2
  obtain ⟨F, hF_diff, hF_two, hF_exp⟩ :=
    exists_holomorphic_log_on_ball hRpos L4_differentiable.differentiableOn hball_nz
      (Ψ 2) (hL4_eq_exp_Ψ 2 (by simp)).symm
  -- Define analytic continuation g̃ of g0 on Metric.ball 2 R
  let gTilde : ℂ → ℂ := fun z => (P z - F z) / z + 4 * ((N : ℂ) ^ ((1 / 2 : ℂ) - z) / (z - 1 / 2))
  have hgTilde_diff : DifferentiableOn ℂ gTilde (Metric.ball (2 : ℂ) R) := by
    intro z hz
    have hzre : 1 / 2 < z.re := hball_re z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hzre; linarith
    have hzhalf : z - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [sub_re, div_ofNat_re, one_re, zero_re] at this
      linarith
    have hNz : 0 < (N : ℂ).re := by simp; positivity
    have h1 : DifferentiableWithinAt ℂ (fun w => (P w - F w) / w) (Metric.ball 2 R) z :=
      ((hP_diff z).differentiableWithinAt.sub (hF_diff z hz)).div differentiableWithinAt_id hz0
    have h2 : DifferentiableWithinAt ℂ (fun w => 4 * ((N : ℂ) ^ ((1 / 2 : ℂ) - w) / (w - 1 / 2)))
        (Metric.ball 2 R) z := by
      have hc : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - w)) z :=
        (differentiableAt_const _).cpow ((differentiableAt_const _).sub differentiableAt_id) (Or.inl hNz)
      exact ((differentiableAt_const (4 : ℂ)).mul (hc.div (differentiableAt_id.sub_const _) hzhalf)).differentiableWithinAt
    exact h1.add h2
  -- Show gTilde agrees with gDeriv N 0 on Metric.ball 2 (1/2)
  have hR_gt_half : (1 / 2 : ℝ) < R := by dsimp [R]; linarith
  have hΨ_diff_half : DifferentiableOn ℂ Ψ (Metric.ball (2 : ℂ) (1 / 2)) := by
    intro z hz
    have hzre : 1 < z.re := by
      have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - 2)
      have h2 : ‖z - 2‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      linarith
    have hzhalf : z - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [sub_re, div_ofNat_re, one_re, zero_re] at this
      linarith
    have hNz : 0 < (N : ℂ).re := by simp; positivity
    have hg0 : DifferentiableAt ℂ (gDeriv N 0) z := (hasDerivAt_gDeriv hN3 0 hzre).differentiableAt
    have hcp : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - w) / (w - 1 / 2)) z :=
      ((differentiableAt_const _).cpow ((differentiableAt_const _).sub differentiableAt_id)
        (Or.inl hNz)).div (differentiableAt_id.sub_const _) hzhalf
    exact ((((differentiableAt_id.mul hg0).neg).add (hP_diff z)).add
      (((differentiableAt_const (4 : ℂ)).mul differentiableAt_id).mul hcp)).differentiableWithinAt
  have hF_eq_Ψ : ∀ z ∈ Metric.ball (2 : ℂ) (1 / 2), F z = Ψ z := by
    have hsub : Metric.ball (2 : ℂ) (1 / 2) ⊆ Metric.ball (2 : ℂ) R :=
      Metric.ball_subset_ball hR_gt_half.le
    have hexp_eq : ∀ z ∈ Metric.ball (2 : ℂ) (1 / 2), Complex.exp (F z - Ψ z) = 1 := by
      intro z hz
      have hzre : 1 < z.re := by
        have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - 2)
        have h2 : ‖z - 2‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
        linarith
      rw [Complex.exp_sub, hF_exp z (hsub hz), ← hL4_eq_exp_Ψ z hzre, div_self (hball_nz z (hsub hz))]
    have hD : ∀ z ∈ Metric.ball (2 : ℂ) (1 / 2), deriv (fun w => F w - Ψ w) z = 0 := by
      intro z hz
      have hdiff_sub : DifferentiableAt ℂ (fun w => F w - Ψ w) z :=
        ((hF_diff.mono hsub).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).sub
          (hΨ_diff_half.differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      have h1 : HasDerivAt (fun w => Complex.exp (F w - Ψ w))
          (Complex.exp (F z - Ψ z) * deriv (fun w => F w - Ψ w) z) z :=
        hdiff_sub.hasDerivAt.cexp
      have h2 : HasDerivAt (fun w => Complex.exp (F w - Ψ w)) 0 z := by
        refine (hasDerivAt_const z (1 : ℂ)).congr_of_eventuallyEq ?_
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
        exact hexp_eq w hw
      have heq := h1.unique h2
      rw [hexp_eq z hz, one_mul] at heq
      exact heq
    intro z hz
    have h2mem : (2 : ℂ) ∈ Metric.ball (2 : ℂ) (1 / 2) := Metric.mem_ball_self (by norm_num)
    have h0 : F z - Ψ z = F 2 - Ψ 2 :=
      (convex_ball (2 : ℂ) (1 / 2)).is_const_of_fderivWithin_eq_zero
        (f := fun w => F w - Ψ w)
        ((hF_diff.mono hsub).sub hΨ_diff_half)
        (fun w hw => by
          have hdiff_sub : DifferentiableAt ℂ (fun u => F u - Ψ u) w :=
            ((hF_diff.mono hsub).differentiableAt (Metric.isOpen_ball.mem_nhds hw)).sub
              (hΨ_diff_half.differentiableAt (Metric.isOpen_ball.mem_nhds hw))
          rw [fderivWithin_of_isOpen Metric.isOpen_ball hw, hdiff_sub.hasDerivAt.hasFDerivAt.fderiv,
            hD w hw]
          simp)
        hz h2mem
    rw [hF_two, sub_self] at h0
    exact sub_eq_zero.mp h0
  have hgTilde_eq_g0 : gTilde =ᶠ[𝓝 (2 : ℂ)] gDeriv N 0 := by
    refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))) ?_
    intro z hz
    have hzre : 1 < z.re := by
      have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - 2)
      have h2 : ‖z - 2‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      linarith
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hzre; linarith
    dsimp [gTilde]
    rw [hF_eq_Ψ z hz]
    dsimp [Ψ]
    field_simp [hz0]
    ring
  -- Taylor series at σ₁ = σ₀ - ε / 2 ∈ Metric.ball 2 R
  let σ₁ : ℝ := σ₀ - ε / 2
  have hσ₁_mem : (σ₁ : ℂ) ∈ Metric.ball (2 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : ((σ₁ : ℂ) - 2) = ((σ₁ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by dsimp [σ₁]; linarith)]
    dsimp [σ₁, R]
    linarith
  have hTaylor := Complex.hasSum_taylorSeries_on_ball hgTilde_diff hσ₁_mem
  -- Identify the k-th Taylor term as a non-negative real integral
  let c : ℕ → ℝ := fun k =>
    ((2 - σ₁) ^ k / (k ! : ℝ)) * ∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)
  have hc_term : ∀ k : ℕ,
      (k ! : ℂ)⁻¹ • ((σ₁ : ℂ) - 2) ^ k • iteratedDeriv k gTilde 2 = (c k : ℂ) := by
    intro k
    rw [hgTilde_eq_g0.iteratedDeriv_eq k, iteratedDeriv_gDeriv_zero hN3 k 2 (by simp)]
    dsimp [gDeriv, c]
    have hsub : ((σ₁ : ℂ) - 2) ^ k = (-1 : ℂ) ^ k * ((2 - σ₁ : ℝ) : ℂ) ^ k := by
      rw [← mul_pow]; congr 1; push_cast; ring
    have hint_real : ∫ t in Set.Ioi (N : ℝ),
        (Hfun t : ℂ) * ((Real.log t : ℂ) ^ k) * (t : ℂ) ^ (-((2 : ℂ) + 1)) =
        ((∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ) : ℝ) : ℂ) := by
      have hof : ((∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ) : ℝ) : ℂ) =
          ∫ t in Set.Ioi (N : ℝ), ((Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ) : ℝ) : ℂ) :=
        (integral_ofReal (𝕜 := ℂ)).symm
      rw [hof]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have htpos : 0 < t := lt_trans (by positivity) ht
      have h3 : -((2 : ℂ) + 1) = ((-3 : ℝ) : ℂ) := by norm_num
      rw [h3, ← Complex.ofReal_cpow htpos.le]
      push_cast; ring
    have hneg1 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    rw [hsub, hint_real]
    push_cast
    calc
      (k ! : ℂ)⁻¹ * ((-1 : ℂ) ^ k * (2 - (σ₁ : ℂ)) ^ k *
          ((-1 : ℂ) ^ k * ↑(∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ))))
          = ((k ! : ℂ)⁻¹ * (2 - (σ₁ : ℂ)) ^ k *
              ↑(∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ))) *
              ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) := by ring
      _ = (2 - (σ₁ : ℂ)) ^ k / (k ! : ℂ) *
            ↑(∫ t in Set.Ioi (N : ℝ), Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)) := by
            rw [hneg1, mul_one, div_eq_mul_inv]; ring
  simp_rw [hc_term] at hTaylor
  have hc_summable : Summable c := by
    have hre := Complex.reCLM.summable hTaylor.summable
    refine hre.congr fun k => ?_
    simp
  have hc_nonneg : ∀ k : ℕ, 0 ≤ c k := fun k => by
    dsimp [c]
    refine mul_nonneg (div_nonneg (pow_nonneg (by dsimp [σ₁]; linarith) k) (by positivity)) ?_
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast hN1) ht
    exact mul_nonneg (mul_nonneg (hH_nonneg t ht) (pow_nonneg (Real.log_nonneg ht1.le) k))
      (Real.rpow_nonneg (zero_lt_one.trans ht1).le _)
  -- Tonelli (lintegral_tsum) gives integrability of H(t) * t^(-σ₁ - 1) on Ioi N
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let psi : ℕ → ℝ → ENNReal := fun k t =>
    ENNReal.ofReal (((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)))
  have hpsi_meas : ∀ k : ℕ, AEMeasurable (psi k) μ := fun k =>
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((measurable_Hfun.mul (Real.measurable_log.pow_const k)).mul
        (measurable_id.pow_const _)))).aemeasurable
  have hpsi_lint : ∀ k : ℕ, ∫⁻ t, psi k t ∂μ = ENNReal.ofReal (c k) := by
    intro k
    have hint_k : IntegrableOn (fun t : ℝ =>
        ((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ))) (Set.Ioi (N : ℝ)) := by
      have h1 : IntegrableOn (fun t : ℝ =>
          ((2 - σ₁) ^ k / (k ! : ℝ)) * (|Hfun t| * (Real.log t) ^ k * t ^ (-((2 : ℝ) + 1)))) (Set.Ioi (N : ℝ)) :=
        (integrableOn_Hfun_log_pow hN3 k (σ := 2) (by norm_num)).const_mul _
      refine IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
      rw [abs_of_nonneg (hH_nonneg t ht), show -((2 : ℝ) + 1) = (-3 : ℝ) by norm_num]
    have hnn : 0 ≤ᵐ[μ] fun t : ℝ =>
        ((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast hN1) ht
      exact mul_nonneg (div_nonneg (pow_nonneg (by dsimp [σ₁]; linarith) k) (by positivity))
        (mul_nonneg (mul_nonneg (hH_nonneg t ht) (pow_nonneg (Real.log_nonneg ht1.le) k))
          (Real.rpow_nonneg (zero_lt_one.trans ht1).le _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint_k hnn, integral_const_mul]
  have htonelli : ∫⁻ t, ENNReal.ofReal (Hfun t * t ^ (-σ₁ - 1)) ∂μ =
      ENNReal.ofReal (∑' k : ℕ, c k) := by
    have hpt : ∀ᵐ t ∂μ, ENNReal.ofReal (Hfun t * t ^ (-σ₁ - 1)) = ∑' k : ℕ, psi k t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := lt_of_le_of_lt (by exact_mod_cast hN1) ht
      have htpos : 0 < t := zero_lt_one.trans ht1
      have h2σ : 0 ≤ 2 - σ₁ := by dsimp [σ₁]; linarith
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hexp : HasSum (fun k : ℕ => ((2 - σ₁) * Real.log t) ^ k / (k ! : ℝ))
          (Real.exp ((2 - σ₁) * Real.log t)) := by
        simpa [Real.exp_eq_exp_ℝ] using
          NormedSpace.expSeries_div_hasSum_exp ((2 - σ₁) * Real.log t)
      have hmul : HasSum (fun k : ℕ =>
          ((2 - σ₁) ^ k / (k ! : ℝ)) * (Hfun t * (Real.log t) ^ k * t ^ (-3 : ℝ)))
          (Hfun t * t ^ (-σ₁ - 1)) := by
        have h1 := (hexp.mul_left (Hfun t)).mul_right (t ^ (-3 : ℝ))
        have hval : Hfun t * Real.exp ((2 - σ₁) * Real.log t) * t ^ (-3 : ℝ) =
            Hfun t * t ^ (-σ₁ - 1) := by
          rw [mul_comm (2 - σ₁), ← Real.rpow_def_of_pos htpos, mul_assoc, ← Real.rpow_add htpos]
          congr 2; ring
        rw [hval] at h1
        refine h1.congr_fun fun k => ?_
        rw [mul_pow]; ring
      rw [← hmul.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by
        exact mul_nonneg (div_nonneg (pow_nonneg h2σ k) (by positivity))
          (mul_nonneg (mul_nonneg (hH_nonneg t ht) (pow_nonneg hlog0 k))
            (Real.rpow_nonneg htpos.le _))) hmul.summable]
    rw [lintegral_congr_ae hpt, lintegral_tsum hpsi_meas]
    simp_rw [hpsi_lint]
    rw [ENNReal.ofReal_tsum_of_nonneg hc_nonneg hc_summable]
  have hInt_σ₁ : IntegrableOn (fun t : ℝ => Hfun t * t ^ (-σ₁ - 1)) (Set.Ioi (N : ℝ)) := by
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Hfun t * t ^ (-σ₁ - 1)) μ :=
      (measurable_Hfun.mul (measurable_id.pow_const _)).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    rw [HasFiniteIntegral]
    have heq : ∀ᵐ t ∂μ, ‖Hfun t * t ^ (-σ₁ - 1)‖ₑ = ENNReal.ofReal (Hfun t * t ^ (-σ₁ - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := lt_trans (by positivity) ht
      rw [Real.enorm_eq_ofReal (mul_nonneg (hH_nonneg t ht) (Real.rpow_nonneg htpos.le _))]
    rw [lintegral_congr_ae heq, htonelli]
    exact ENNReal.ofReal_lt_top
  -- Holomorphic extension of exp(Ψ(s)) to {s | σ₁ < s.re}
  have hg0_diff : DifferentiableOn ℂ (gDeriv N 0) {s : ℂ | σ₁ < s.re} :=
    differentiableOn_g0_of_integrableOn hN3 hH_nonneg hInt_σ₁
  have hσ₁_gt_half : 1 / 2 < σ₁ := by
    have hrle : r ≤ (σ₀ - 1 / 2) / 2 := min_le_right _ _
    dsimp [σ₁]; linarith
  have hΨ_diff : DifferentiableOn ℂ Ψ {s : ℂ | σ₁ < s.re} := by
    intro s hs
    have hsgt : 1 / 2 < s.re := lt_trans hσ₁_gt_half hs
    have hshalf : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [sub_re, div_ofNat_re, one_re, zero_re] at this
      linarith
    have hNz : 0 < (N : ℂ).re := by simp; positivity
    have hcp : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - w) / (w - 1 / 2)) s :=
      ((differentiableAt_const _).cpow ((differentiableAt_const _).sub differentiableAt_id)
        (Or.inl hNz)).div (differentiableAt_id.sub_const _) hshalf
    exact (((differentiableWithinAt_id.mul (hg0_diff s hs)).neg).add
      (hP_diff s).differentiableWithinAt).add
      (((differentiableWithinAt_const (4 : ℂ)).mul differentiableWithinAt_id).mul hcp.differentiableWithinAt)
  -- By the identity theorem, L4 s = exp(Ψ s) on {s | σ₁ < s.re}, hence L4 s ≠ 0 there
  have hL4_ext : ∀ s : ℂ, σ₁ < s.re → L4 s = Complex.exp (Ψ s) := by
    have hopen : IsOpen {z : ℂ | σ₁ < z.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    have hconv : Convex ℝ {z : ℂ | σ₁ < z.re} := convex_halfSpace_re_gt σ₁
    have han1 : AnalyticOnNhd ℂ L4 {z : ℂ | σ₁ < z.re} :=
      L4_differentiable.differentiableOn.analyticOnNhd hopen
    have han2 : AnalyticOnNhd ℂ (fun z => Complex.exp (Ψ z)) {z : ℂ | σ₁ < z.re} :=
      hΨ_diff.cexp.analyticOnNhd hopen
    have h2mem : (2 : ℂ) ∈ {z : ℂ | σ₁ < z.re} := by
      change σ₁ < (2 : ℂ).re
      simp only [re_ofNat]; dsimp [σ₁]; linarith
    have hev : L4 =ᶠ[𝓝 (2 : ℂ)] (fun z => Complex.exp (Ψ z)) := by
      refine Filter.eventually_of_mem
        ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)) ?_
      intro z hz
      exact hL4_eq_exp_Ψ z hz
    exact fun s hs => han1.eqOn_of_preconnected_of_eventuallyEq han2 hconv.isPreconnected h2mem hev hs
  have hS_le_σ₁ : σ₀ ≤ σ₁ := by
    refine csSup_le hS_nonempty ?_
    rintro σ ⟨t, hzero⟩
    by_contra hgt
    have hgt' : σ₁ < σ := lt_of_not_ge hgt
    have hre_gt : σ₁ < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
      rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]
      linarith
    have hne : L4 ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      rw [hL4_ext _ hre_gt]
      exact Complex.exp_ne_zero _
    exact hne hzero
  dsimp [σ₁] at hS_le_σ₁
  linarith


/- ### Part B1: Parameterized critical-line zero count -/

private lemma real_gamma_le_of_three_quarters_le {x : ℝ} (hx : 3 / 4 ≤ x) :
    Real.Gamma x ≤ 2 + (x + 1) ^ (⌈x⌉₊) := by
  have hxpos : 0 < x := by linarith
  rw [Real.Gamma_eq_integral hxpos]
  let n : ℕ := ⌈x⌉₊
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hn1 : 1 ≤ n := by
    have : 0 < n := Nat.ceil_pos.mpr hxpos
    omega
  have hint_x : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (x - 1)) (Set.Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun t : ℝ => ‖(Real.exp (-t) : ℂ) * (t : ℂ) ^ ((x : ℂ) - 1)‖) (Set.Ioi (0 : ℝ)) :=
      (Complex.GammaIntegral_convergent (s := (x : ℂ)) (by simpa using hxpos)).norm
    refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_cpow_eq_rpow_re_of_pos ht, sub_re, ofReal_re, one_re]
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1) =
      (∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (x - 1)) +
      (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1)) := by
    rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint_x.mono_set Set.Ioc_subset_Ioi_self)
      (hint_x.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  rw [hsplit]
  have hpart1 : ∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (x - 1) ≤ 2 := by
    have hdom : IntegrableOn (fun t : ℝ => t ^ (-1 / 4 : ℝ)) (Set.Ioc (0 : ℝ) 1) := by
      have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-1 / 4 : ℝ)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h1
    have hle1 : ∫ t in Set.Ioc (0 : ℝ) 1, Real.exp (-t) * t ^ (x - 1) ≤
        ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (-1 / 4 : ℝ) := by
      refine setIntegral_mono_on (hint_x.mono_set Set.Ioc_subset_Ioi_self) hdom measurableSet_Ioc ?_
      intro t ht
      have htpos : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hrp : t ^ (x - 1) ≤ t ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge htpos ht1 (by linarith)
      calc
        Real.exp (-t) * t ^ (x - 1) ≤ 1 * t ^ (-1 / 4 : ℝ) :=
          mul_le_mul hexp hrp (Real.rpow_nonneg htpos.le _) zero_le_one
        _ = t ^ (-1 / 4 : ℝ) := one_mul _
    have hval : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (-1 / 4 : ℝ) = 4 / 3 := by
      rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
      norm_num
    linarith
  have hpart2 : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1) ≤ (x + 1) ^ n := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hint_n : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ ((n : ℝ) - 1)) (Set.Ioi (0 : ℝ)) := by
      have h : IntegrableOn (fun t : ℝ => ‖(Real.exp (-t) : ℂ) * (t : ℂ) ^ (((n : ℝ) : ℂ) - 1)‖) (Set.Ioi (0 : ℝ)) :=
        (Complex.GammaIntegral_convergent (s := ((n : ℝ) : ℂ)) (by simpa using hnpos)).norm
      refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos ht, sub_re, ofReal_re, one_re]
    have hle_n : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ (x - 1) ≤
        ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ ((n : ℝ) - 1) := by
      refine setIntegral_mono_on (hint_x.mono_set (Set.Ioi_subset_Ioi zero_le_one))
        (hint_n.mono_set (Set.Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi ?_
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (Real.exp_pos _).le
    have hle_full : ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) * t ^ ((n : ℝ) - 1) ≤
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ ((n : ℝ) - 1) := by
      refine setIntegral_mono_set hint_n ?_ (Set.Ioi_subset_Ioi zero_le_one).eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
    have hgam : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ ((n : ℝ) - 1) = ((n - 1)! : ℝ) := by
      rw [← Real.Gamma_eq_integral hnpos]
      have : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
        have : n = (n - 1) + 1 := (Nat.sub_add_cancel hn1).symm
        exact_mod_cast this
      rw [this, Real.Gamma_nat_eq_factorial]
    have hfac : ((n - 1)! : ℝ) ≤ (x + 1) ^ n := by
      have h1 : (n - 1)! ≤ n ^ n :=
        le_trans (Nat.factorial_le (Nat.sub_le n 1)) (Nat.factorial_le_pow n)
      have h2 : (n : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxpos.le).le
      calc
        ((n - 1)! : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast h1
        _ ≤ (x + 1) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg n) h2 n
    linarith
  linarith

private lemma norm_xi4_le_exp_R_log_R :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s - 1 / 2‖ →
      ‖xi4 s‖ ≤ Real.exp (C * ‖s - 1 / 2‖ * Real.log ‖s - 1 / 2‖) := by
  obtain ⟨CL, hCLpos, hCL⟩ := norm_L4_le_of_half_le_re
  have hright : ∃ C1 : ℝ, 0 < C1 ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 2 ≤ ‖s - 1 / 2‖ →
      ‖xi4 s‖ ≤ Real.exp (C1 * ‖s - 1 / 2‖ * Real.log ‖s - 1 / 2‖) := by
    let C1 : ℝ := 12 * CL + 10
    refine ⟨C1, by positivity, fun s hsre hR => ?_⟩
    set R := ‖s - 1 / 2‖ with hR_def
    have hRpos : 0 < R := by linarith
    have hlogR : 1 / 2 ≤ Real.log R := by
      have h1 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [sq, ← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) (le_trans h1 hR)
    have hnorm_s : ‖s‖ ≤ 2 * R := by
      calc ‖s‖ = ‖(s - 1 / 2) + 1 / 2‖ := by ring_nf
        _ ≤ R + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 * R := by norm_num; linarith
    have hsre_le : s.re ≤ 2 * R := le_trans (Complex.re_le_norm s) hnorm_s
    rw [xi4_eq_L4_mul_gammaℝ (by linarith), Complex.Gammaℝ_def, norm_mul, norm_mul]
    have hpi_le : ‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have hre : (-(s + 1) / 2).re ≤ 0 := by
        simp only [div_ofNat_re, neg_re, add_re, one_re]; linarith
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) hre
    have hgam_le : ‖Complex.Gamma ((s + 1) / 2)‖ ≤ Real.Gamma ((s.re + 1) / 2) := by
      have hre_pos : 0 < ((s + 1) / 2).re := by simp only [div_ofNat_re, add_re, one_re]; linarith
      rw [Complex.Gamma_eq_integral hre_pos,
        Real.Gamma_eq_integral (by linarith : 0 < (s.re + 1) / 2)]
      have h1 := norm_integral_le_integral_norm
        (f := fun t : ℝ => Real.exp (-t) * (t : ℂ) ^ ((s + 1) / 2 - 1))
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      refine h1.trans_eq ?_
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp only [sub_re, div_ofNat_re, add_re, one_re]
    have hgam_bound : Real.Gamma ((s.re + 1) / 2) ≤ 2 + (R + 2) ^ (⌈(s.re + 1) / 2⌉₊) := by
      have hx : 3 / 4 ≤ (s.re + 1) / 2 := by linarith
      have hle_base : (s.re + 1) / 2 + 1 ≤ R + 2 := by linarith
      refine (real_gamma_le_of_three_quarters_le hx).trans ?_
      have : ((s.re + 1) / 2 + 1) ^ ⌈(s.re + 1) / 2⌉₊ ≤ (R + 2) ^ ⌈(s.re + 1) / 2⌉₊ :=
        pow_le_pow_left₀ (by linarith) hle_base _
      linarith
    have hceil_le : (⌈(s.re + 1) / 2⌉₊ : ℝ) ≤ R + 2 := by
      have h1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ (s.re + 1) / 2)).le
      linarith
    have hpow_le : (R + 2) ^ (⌈(s.re + 1) / 2⌉₊) ≤ Real.exp ((R + 2) * Real.log (R + 2)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
      exact Real.exp_le_exp.mpr (by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hceil_le (Real.log_nonneg (by linarith)))
    have hlog2 : Real.log (R + 2) ≤ 2 * Real.log R := by
      have : R + 2 ≤ R ^ 2 := by nlinarith
      calc Real.log (R + 2) ≤ Real.log (R ^ 2) := Real.log_le_log (by linarith) this
        _ = 2 * Real.log R := by rw [Real.log_pow]; norm_num
    have hR2 : R + 2 ≤ 2 * R := by linarith
    have hgam_exp : 2 + (R + 2) ^ (⌈(s.re + 1) / 2⌉₊) ≤ 3 * Real.exp (4 * R * Real.log R) := by
      have hexp1 : 1 ≤ Real.exp (4 * R * Real.log R) :=
        Real.one_le_exp (by nlinarith)
      have hexp2 : (R + 2) ^ (⌈(s.re + 1) / 2⌉₊) ≤ Real.exp (4 * R * Real.log R) := by
        refine hpow_le.trans (Real.exp_le_exp.mpr ?_)
        nlinarith [Real.log_nonneg (by linarith : 1 ≤ R + 2)]
      linarith
    have hL_le : ‖L4 s‖ ≤ 2 * CL * R := by
      have h1 := (hCL s hsre).trans (mul_le_mul_of_nonneg_left hnorm_s hCLpos.le)
      linarith
    have hprod_le : ‖L4 s‖ * (‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ * ‖Complex.Gamma ((s + 1) / 2)‖) ≤
        (6 * CL * R) * Real.exp (4 * R * Real.log R) := by
      have hGtot : ‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ * ‖Complex.Gamma ((s + 1) / 2)‖ ≤
          3 * Real.exp (4 * R * Real.log R) := by
        calc
          ‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ * ‖Complex.Gamma ((s + 1) / 2)‖
              ≤ 1 * (3 * Real.exp (4 * R * Real.log R)) :=
                mul_le_mul hpi_le (hgam_le.trans (hgam_bound.trans hgam_exp))
                  (norm_nonneg _) zero_le_one
          _ = 3 * Real.exp (4 * R * Real.log R) := one_mul _
      calc
        ‖L4 s‖ * (‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ * ‖Complex.Gamma ((s + 1) / 2)‖)
            ≤ (2 * CL * R) * (3 * Real.exp (4 * R * Real.log R)) :=
              mul_le_mul hL_le hGtot (by positivity) (by positivity)
        _ = (6 * CL * R) * Real.exp (4 * R * Real.log R) := by ring
    have hlin_exp : 6 * CL * R ≤ Real.exp (12 * CL * R * Real.log R) := by
      have h1 : 6 * CL * R ≤ 12 * CL * R * Real.log R := by
        nlinarith [mul_le_mul_of_nonneg_left hlogR (by positivity : 0 ≤ 12 * CL * R)]
      have h2 := Real.add_one_le_exp (6 * CL * R)
      exact le_trans (by linarith) (Real.exp_le_exp.mpr h1)
    calc
      ‖L4 s‖ * (‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ * ‖Complex.Gamma ((s + 1) / 2)‖)
          ≤ (6 * CL * R) * Real.exp (4 * R * Real.log R) := hprod_le
      _ ≤ Real.exp (12 * CL * R * Real.log R) * Real.exp (4 * R * Real.log R) :=
            mul_le_mul_of_nonneg_right hlin_exp (Real.exp_pos _).le
      _ = Real.exp ((12 * CL + 4) * R * Real.log R) := by
            rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (C1 * R * Real.log R) := by
            refine Real.exp_le_exp.mpr ?_
            dsimp [C1]
            nlinarith [mul_nonneg hRpos.le (by linarith : 0 ≤ Real.log R)]
  obtain ⟨C1, hC1pos, hC1⟩ := hright
  refine ⟨C1 + 4, by positivity, fun s hR => ?_⟩
  by_cases hsre : 1 / 2 ≤ s.re
  · refine (hC1 s hsre hR).trans (Real.exp_le_exp.mpr ?_)
    have hlog0 : 0 ≤ Real.log ‖s - 1 / 2‖ := Real.log_nonneg (by linarith)
    nlinarith [mul_nonneg (by linarith : 0 ≤ ‖s - 1 / 2‖) hlog0]
  · push Not at hsre
    let s' : ℂ := 1 - s
    have hs're : 1 / 2 ≤ s'.re := by simp [s']; linarith
    have hs'norm : ‖s' - 1 / 2‖ = ‖s - 1 / 2‖ := by
      have : s' - 1 / 2 = -(s - 1 / 2) := by dsimp [s']; ring
      rw [this, norm_neg]
    have hfe := xi4_functional_eq s'
    have h1s' : 1 - s' = s := by dsimp [s']; ring
    rw [h1s'] at hfe
    rw [hfe, norm_mul]
    have h4pow : ‖(4 : ℂ) ^ (s' - 1 / 2)‖ ≤ Real.exp (2 * ‖s - 1 / 2‖) := by
      rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
      refine Real.exp_le_exp.mpr ?_
      have hlog4 : Real.log 4 ≤ 2 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        have : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      have hre_le : (s' - 1 / 2).re ≤ ‖s - 1 / 2‖ := by
        rw [← hs'norm]; exact Complex.re_le_norm _
      have hre_nn : 0 ≤ (s' - 1 / 2).re := by simp [s']; linarith
      nlinarith
    have hlogR : 1 / 2 ≤ Real.log ‖s - 1 / 2‖ := by
      have h1 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [sq, ← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos _) (le_trans h1 hR)
    calc
      ‖(4 : ℂ) ^ (s' - 1 / 2)‖ * ‖xi4 s'‖
          ≤ Real.exp (2 * ‖s - 1 / 2‖) * Real.exp (C1 * ‖s - 1 / 2‖ * Real.log ‖s - 1 / 2‖) := by
            rw [← hs'norm] at hR ⊢
            have h2 := hC1 s' hs're hR
            rw [hs'norm] at h2 ⊢
            exact mul_le_mul h4pow h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * ‖s - 1 / 2‖ + C1 * ‖s - 1 / 2‖ * Real.log ‖s - 1 / 2‖) :=
            (Real.exp_add _ _).symm
      _ ≤ Real.exp ((C1 + 4) * ‖s - 1 / 2‖ * Real.log ‖s - 1 / 2‖) := by
            refine Real.exp_le_exp.mpr ?_
            nlinarith [mul_le_mul_of_nonneg_left hlogR (by linarith : 0 ≤ ‖s - 1 / 2‖)]

private lemma pow_le_two_mul_factorial (m : ℕ) : m ^ m ≤ (2 * m)! := by
  have h1 : m ^ m = ∏ _j ∈ Finset.Icc (m + 1) (2 * m), m := by
    rw [Finset.prod_const, Nat.card_Icc]
    congr 1; omega
  have h2 : ∏ _j ∈ Finset.Icc (m + 1) (2 * m), m ≤ ∏ j ∈ Finset.Icc (m + 1) (2 * m), j :=
    Finset.prod_le_prod' fun j hj => by
      have := (Finset.mem_Icc.mp hj).1; omega
  have h3 : ∏ j ∈ Finset.Icc (m + 1) (2 * m), j ≤ ∏ j ∈ Finset.Icc 1 (2 * m), j := by
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ fun j hj _ => ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · exact (Finset.mem_Icc.mp hj).1
  have h4 : ∏ j ∈ Finset.Icc 1 (2 * m), j = (2 * m)! := by
    induction (2 * m) with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]
  omega

private lemma xi4_real_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    (1 / 2 : ℝ) * Real.pi ^ (-(2 * m + 1 : ℤ)) * (m : ℝ) ^ m ≤ ‖xi4 ((4 * m + 1 : ℕ) : ℂ)‖ := by
  have hsre : (0 : ℝ) < ((4 * m + 1 : ℕ) : ℝ) := by positivity
  rw [xi4_eq_L4_mul_gammaℝ (by simp; linarith), Complex.Gammaℝ_def, norm_mul, norm_mul]
  obtain ⟨x, hxpos, hxeq, hxge⟩ := L4_real_pos hsre
  have hLnorm : (1 / 2 : ℝ) ≤ ‖L4 ((4 * m + 1 : ℕ) : ℂ)‖ := by
    have hxeq' : L4 ((4 * m + 1 : ℕ) : ℂ) = (x : ℂ) := by simpa using hxeq
    rw [hxeq', Complex.norm_real, Real.norm_of_nonneg hxpos.le]
    have h3le : (3 : ℝ) ^ (-((4 * m + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
      have h1 : (3 : ℝ) ^ (-((4 * m + 1 : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_cast; omega)
      rw [Real.rpow_neg_one] at h1
      linarith
    linarith
  have harg : (((4 * m + 1 : ℕ) : ℂ) + 1) / 2 = ((2 * m : ℕ) : ℂ) + 1 := by
    push_cast; ring
  have hG : ‖Complex.Gamma ((((4 * m + 1 : ℕ) : ℂ) + 1) / 2)‖ = ((2 * m)! : ℝ) := by
    rw [harg, Complex.Gamma_nat_eq_factorial, Complex.norm_natCast]
  have hpi : ‖(Real.pi : ℂ) ^ (-(((4 * m + 1 : ℕ) : ℂ) + 1) / 2)‖ =
      Real.pi ^ (-(2 * m + 1 : ℤ)) := by
    have hexp : -(((4 * m + 1 : ℕ) : ℂ) + 1) / 2 = (((-(2 * m + 1 : ℤ) : ℤ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hexp, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re, Real.rpow_intCast]
  rw [hG, hpi]
  have hfac : (m : ℝ) ^ m ≤ ((2 * m)! : ℝ) := by exact_mod_cast pow_le_two_mul_factorial m
  have hpi_pos : 0 ≤ Real.pi ^ (-(2 * m + 1 : ℤ)) := by positivity
  calc
    (1 / 2 : ℝ) * Real.pi ^ (-(2 * m + 1 : ℤ)) * (m : ℝ) ^ m
        = (1 / 2 : ℝ) * (Real.pi ^ (-(2 * m + 1 : ℤ)) * (m : ℝ) ^ m) := by ring
    _ ≤ ‖L4 ((4 * m + 1 : ℕ) : ℂ)‖ * (Real.pi ^ (-(2 * m + 1 : ℤ)) * ((2 * m)! : ℝ)) := by
          exact mul_le_mul hLnorm (mul_le_mul_of_nonneg_left hfac hpi_pos) (by positivity) (norm_nonneg _)

/- ### Step 3: Entire holomorphic logarithm and Fourier-coefficient growth bound -/

/-- Term-by-term antiderivative power series centered at 0 with value v0 at 0. -/
noncomputable def antiderivEntire (f : ℂ → ℂ) (v0 z : ℂ) : ℂ :=
  v0 + ∑' n : ℕ, (((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ (n + 1)

private lemma antiderivEntire_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) (v0 z : ℂ) :
    HasDerivAt (antiderivEntire f v0) (f z) z := by
  let r1 : ℝ := ‖z‖ + 1
  let r2 : ℝ := ‖z‖ + 2
  have hr1pos : 0 < r1 := by positivity
  have hr2pos : 0 < r2 := by positivity
  have hr1r2 : r1 < r2 := by dsimp [r1, r2]; linarith
  have hsum2 : Summable (fun n : ℕ => (n ! : ℂ)⁻¹ * iteratedDeriv n f 0 * (r2 : ℂ) ^ n) := by
    have h := (Complex.hasSum_taylorSeries_of_entire hf 0 (r2 : ℂ)).summable
    refine h.congr fun n => ?_
    simp [smul_eq_mul]; ring
  have htend0 : Tendsto (fun n : ℕ => ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f 0 * (r2 : ℂ) ^ n‖)
      atTop (𝓝 0) := by
    have h := (Nat.cofinite_eq_atTop ▸ hsum2.tendsto_cofinite_zero).norm
    simpa only [norm_zero] using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend0) 1 zero_lt_one
  let b : ℕ → ℝ := fun n => ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f 0‖ * r2 ^ n
  have hne_rng : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  let M : ℝ := max 1 ((Finset.range (N + 1)).sup' hne_rng b)
  have hM : ∀ n : ℕ, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f 0‖ * r2 ^ n ≤ M := fun n => by
    by_cases hn : n < N + 1
    · exact le_trans (Finset.le_sup' b (Finset.mem_range.mpr hn)) (le_max_right _ _)
    · have h1 := hN n (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
      have h2 : ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f 0‖ * r2 ^ n =
          ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f 0 * (r2 : ℂ) ^ n‖ := by
        symm; rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr2pos.le]
      rw [h2]
      exact le_trans h1.le (le_max_left _ _)
  let F : ℕ → ℂ → ℂ := fun n w => (((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f 0 * w ^ (n + 1)
  have hu_sum : Summable (fun n : ℕ => M * r1 * (r1 / r2) ^ n) :=
    (summable_geometric_of_lt_one (div_nonneg hr1pos.le hr2pos.le)
      ((div_lt_one hr2pos).mpr hr1r2)).mul_left _
  have hF_le : ∀ n : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) r1, ‖F n w‖ ≤ M * r1 * (r1 / r2) ^ n := by
    intro n w hw
    have hw1 : ‖w‖ ≤ r1 := by
      have : ‖w‖ < r1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      exact this.le
    dsimp [F]
    rw [norm_mul, norm_mul, norm_pow]
    have hfac : ‖(((n + 1)! : ℕ) : ℂ)⁻¹‖ ≤ ‖(n ! : ℂ)⁻¹‖ := by
      rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      exact inv_anti₀ (by exact_mod_cast Nat.factorial_pos n)
        (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
    have hpow : ‖w‖ ^ (n + 1) ≤ r1 * r1 ^ n := by
      rw [pow_succ']
      exact mul_le_mul hw1 (pow_le_pow_left₀ (norm_nonneg _) hw1 n) (by positivity) hr1pos.le
    calc
      ‖(((n + 1)! : ℕ) : ℂ)⁻¹‖ * ‖iteratedDeriv n f 0‖ * ‖w‖ ^ (n + 1)
          ≤ ‖(n ! : ℂ)⁻¹‖ * ‖iteratedDeriv n f 0‖ * (r1 * r1 ^ n) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)) hpow
              (by positivity) (by positivity)
      _ = (‖(n ! : ℂ)⁻¹ * iteratedDeriv n f 0‖ * r2 ^ n) * r1 * (r1 / r2) ^ n := by
            rw [norm_mul, div_pow]; field_simp [hr2pos.ne']
      _ ≤ M * r1 * (r1 / r2) ^ n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM n) hr1pos.le) (by positivity)
  have hF_diff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (Metric.ball (0 : ℂ) r1) := fun n =>
    ((differentiable_const _).mul (differentiable_id.pow (n + 1))).differentiableOn
  have hz_ball1 : z ∈ Metric.ball (0 : ℂ) r1 := by
    rw [Metric.mem_ball, dist_zero_right]; dsimp [r1]; linarith
  have hdiff_sum : DifferentiableOn ℂ (fun w => ∑' n : ℕ, F n w) (Metric.ball (0 : ℂ) r1) :=
    differentiableOn_tsum_of_summable_norm hu_sum hF_diff Metric.isOpen_ball hF_le
  have hderiv_sum := hasSum_deriv_of_summable_norm hu_sum hF_diff Metric.isOpen_ball hF_le hz_ball1
  have hterm_deriv : ∀ n : ℕ, deriv (F n) z = (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n f 0 := by
    intro n
    have hd : HasDerivAt (F n)
        ((((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f 0 * (((n + 1 : ℕ) : ℂ) * z ^ n)) z := by
      have h1 := (hasDerivAt_id z).pow (n + 1)
      simpa [F, mul_one] using h1.const_mul ((((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f 0)
    rw [hd.deriv]
    have hfac : (((n + 1)! : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) * (n ! : ℂ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hnf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [hfac, sub_zero, smul_eq_mul, smul_eq_mul]
    field_simp [hn1, hnf]
  simp_rw [hterm_deriv] at hderiv_sum
  have hval : deriv (fun w => ∑' n : ℕ, F n w) z = f z :=
    hderiv_sum.unique (Complex.hasSum_taylorSeries_of_entire hf 0 z)
  have hda : HasDerivAt (fun w => ∑' n : ℕ, F n w) (f z) z := by
    rw [← hval]
    exact (hdiff_sum.differentiableAt (Metric.isOpen_ball.mem_nhds hz_ball1)).hasDerivAt
  exact hda.const_add v0

private lemma exists_entire_log {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hne : ∀ z, Q z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, Complex.exp (h z) = Q z := by
  have hld : Differentiable ℂ (fun z => deriv Q z / Q z) :=
    (hQ.deriv).div hQ hne
  let h := antiderivEntire (fun z => deriv Q z / Q z) (Complex.log (Q 0))
  have hh_deriv : ∀ z, HasDerivAt h (deriv Q z / Q z) z :=
    fun z => antiderivEntire_hasDerivAt hld _ z
  have hh_diff : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hconst : ∀ z, Q z * Complex.exp (-h z) = 1 := by
    have hQderiv : ∀ z, HasDerivAt (fun w => Q w * Complex.exp (-h w)) 0 z := fun z => by
      have hE : HasDerivAt (fun w => Complex.exp (-h w))
          (Complex.exp (-h z) * -(deriv Q z / Q z)) z :=
        ((hh_deriv z).neg).cexp
      have hm : HasDerivAt (fun w => Q w * Complex.exp (-h w))
          (deriv Q z * Complex.exp (-h z) + Q z * (Complex.exp (-h z) * -(deriv Q z / Q z))) z :=
        (hQ z).hasDerivAt.mul hE
      have hz0 : deriv Q z * Complex.exp (-h z) +
          Q z * (Complex.exp (-h z) * -(deriv Q z / Q z)) = 0 := by
        have hqz := hne z
        field_simp [hqz]; ring
      exact hm.congr_deriv hz0
    intro z
    have h0 := is_const_of_deriv_eq_zero (fun w => (hQderiv w).differentiableAt)
      (fun w => (hQderiv w).deriv) z 0
    rw [h0]
    have hh0 : h 0 = Complex.log (Q 0) := by simp [h, antiderivEntire]
    rw [hh0, Complex.exp_neg, Complex.exp_log (hne 0), mul_inv_cancel₀ (hne 0)]
  refine ⟨h, hh_diff, fun z => ?_⟩
  have h1 := hconst z
  calc
    Complex.exp (h z) = 1 * Complex.exp (h z) := (one_mul _).symm
    _ = (Q z * Complex.exp (-h z)) * Complex.exp (h z) := by rw [h1]
    _ = Q z * (Complex.exp (-h z) * Complex.exp (h z)) := by ring
    _ = Q z := by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

private lemma integral_exp_int_mul_I (m : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    have hne : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.I_ne_zero
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun x : ℝ => Complex.exp ((m : ℂ) * (x : ℂ) * Complex.I) / ((m : ℂ) * Complex.I))
          (Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)) θ := fun θ _ => by
      have h1 : HasDerivAt (fun x : ℝ => (m : ℂ) * (x : ℂ) * Complex.I) ((m : ℂ) * Complex.I) θ := by
        have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
        have h2 := (h0.const_mul (m : ℂ)).mul_const Complex.I
        simpa [mul_one] using h2
      have h3 := h1.cexp.div_const ((m : ℂ) * Complex.I)
      have h4 : Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) * ((m : ℂ) * Complex.I) /
          ((m : ℂ) * Complex.I) = Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) :=
        mul_div_cancel_right₀ _ hne
      exact h3.congr_deriv h4
    have hint : IntervalIntegrable (fun θ : ℝ => Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I))
        volume 0 (2 * Real.pi) :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2pi : Complex.exp ((m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      have : (m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h2pi]; simp

/-- Elementary Borel-Caratheodory coefficient bound via Fourier orthogonality on a circle. -/
private lemma norm_taylor_coeff_le_of_re_le {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (c : ℂ) {R M : ℝ} (hR : 0 < R)
    (hM : ∀ θ : ℝ, (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re ≤ M)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖(n ! : ℂ)⁻¹ * iteratedDeriv n h c‖ * R ^ n ≤ 2 * (M - (h c).re) := by
  let a : ℕ → ℂ := fun k => (k ! : ℂ)⁻¹ * iteratedDeriv k h c
  have hsumR : Summable (fun k : ℕ => ‖a k‖ * R ^ k) := by
    have h2R : Summable (fun k : ℕ => ‖a k * ((2 * R : ℝ) : ℂ) ^ k‖) := by
      have hts := (Complex.hasSum_taylorSeries_of_entire hh c (c + ((2 * R : ℝ) : ℂ))).summable
      have hts' : Summable (fun k : ℕ => a k * ((2 * R : ℝ) : ℂ) ^ k) := by
        refine hts.congr fun k => ?_
        simp [a, smul_eq_mul]; ring
      have hts2 := (Complex.hasSum_taylorSeries_of_entire hh c (c + ((4 * R : ℝ) : ℂ))).summable
      have hts2' : Summable (fun k : ℕ => a k * ((4 * R : ℝ) : ℂ) ^ k) := by
        refine hts2.congr fun k => ?_
        simp [a, smul_eq_mul]; ring
      have htend : Tendsto (fun k : ℕ => ‖a k * ((4 * R : ℝ) : ℂ) ^ k‖) atTop (𝓝 0) := by
        have h := (Nat.cofinite_eq_atTop ▸ hts2'.tendsto_cofinite_zero).norm
        simpa only [norm_zero] using h
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend) 1 zero_lt_one
      let b : ℕ → ℝ := fun k => ‖a k‖ * (4 * R) ^ k
      have hne_rng : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
      let B : ℝ := max 1 ((Finset.range (N + 1)).sup' hne_rng b)
      have hB : ∀ k : ℕ, ‖a k‖ * (4 * R) ^ k ≤ B := fun k => by
        by_cases hk : k < N + 1
        · exact le_trans (Finset.le_sup' b (Finset.mem_range.mpr hk)) (le_max_right _ _)
        · have h1 := hN k (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
          have h2 : ‖a k‖ * (4 * R) ^ k = ‖a k * ((4 * R : ℝ) : ℂ) ^ k‖ := by
            symm; rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          rw [h2]; exact le_trans h1.le (le_max_left _ _)
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left B)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hpow : (2 * R) ^ k = (4 * R) ^ k * (1 / 2 : ℝ) ^ k := by
        rw [← mul_pow]; congr 1; ring
      rw [hpow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hB k) (by positivity)
    refine h2R.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    have hrhs : ‖a k * ((2 * R : ℝ) : ℂ) ^ k‖ = ‖a k‖ * (2 * R) ^ k := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le (by linarith) k) (norm_nonneg _)
  have hseries : ∀ θ : ℝ,
      h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      ∑' k : ℕ, a k * (R : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) := fun θ => by
    have h1 := (Complex.hasSum_taylorSeries_of_entire hh c
      (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).tsum_eq.symm
    rw [h1]
    refine tsum_congr fun k => ?_
    rw [add_sub_cancel_left, smul_eq_mul, smul_eq_mul, mul_pow, ← Complex.exp_nat_mul]
    dsimp [a]; ring_nf
  have hnorm_exp : ∀ (m : ℤ) (θ : ℝ), ‖Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
    intro m θ
    have : (m : ℂ) * (θ : ℂ) * Complex.I = (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hint_pos : ∀ m : ℕ,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) =
      (2 * Real.pi : ℂ) * a m * (R : ℂ) ^ m := by
    intro m
    let F : ℕ → ℝ → ℂ := fun k θ =>
      a k * (R : ℂ) ^ k * Complex.exp ((((k : ℤ) - (m : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
    have hcongr : ∀ θ : ℝ,
        h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) = ∑' k : ℕ, F k θ := fun θ => by
      rw [hseries θ, ← tsum_mul_right]
      refine tsum_congr fun k => ?_
      dsimp [F]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    simp_rw [hcongr]
    have hint_tsum : ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑' k : ℕ, F k θ =
        ∑' k : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), F k θ := by
      rw [intervalIntegral.integral_of_le (by positivity)]
      simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      refine (hasSum_integral_of_summable_integral_norm (F := F)
        (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) (fun k => ?_) ?_).tsum_eq.symm
      · exact (Continuous.intervalIntegrable (by dsimp [F]; fun_prop) 0 (2 * Real.pi)).1
      · refine (hsumR.mul_left (2 * Real.pi)).of_nonneg_of_le
          (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
        have hconst : ∀ θ : ℝ, ‖F k θ‖ = ‖a k‖ * R ^ k := fun θ => by
          dsimp [F]
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
            hnorm_exp _ θ, mul_one]
        simp_rw [hconst]
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc,
          sub_zero, ENNReal.toReal_ofReal (by positivity)]
    rw [hint_tsum]
    have hterm : ∀ k : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), F k θ =
        if k = m then (2 * Real.pi : ℂ) * a m * (R : ℂ) ^ m else 0 := fun k => by
      dsimp [F]
      rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
      by_cases hkm : k = m
      · subst hkm; simp; ring
      · have hne : (k : ℤ) - (m : ℤ) ≠ 0 := by omega
        simp [hne, hkm]
    simp_rw [hterm, tsum_ite_eq]
  have hint_neg :
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        starRingEnd ℂ (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
          Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) = 0 := by
    let G : ℕ → ℝ → ℂ := fun k θ =>
      starRingEnd ℂ (a k) * (R : ℂ) ^ k *
        Complex.exp (((-((k : ℤ) + (n : ℤ)) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
    have hcongr : ∀ θ : ℝ,
        starRingEnd ℂ (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
          Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) = ∑' k : ℕ, G k θ := fun θ => by
      rw [hseries θ]
      have hsθ : Summable (fun k : ℕ => a k * (R : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) := by
        refine Summable.of_norm_bounded hsumR fun k => ?_
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
          show (k : ℂ) * (θ : ℂ) * Complex.I = (((k : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hconj_tsum : starRingEnd ℂ (∑' k : ℕ, a k * (R : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) =
          ∑' k : ℕ, starRingEnd ℂ (a k * (R : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) :=
        (hsθ.hasSum.map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj).tsum_eq.symm
      rw [hconj_tsum, ← tsum_mul_right]
      refine tsum_congr fun k => ?_
      dsimp [G]
      simp only [map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj,
        map_natCast, Complex.conj_I]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    simp_rw [hcongr]
    have hint_tsum : ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑' k : ℕ, G k θ =
        ∑' k : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), G k θ := by
      rw [intervalIntegral.integral_of_le (by positivity)]
      simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      refine (hasSum_integral_of_summable_integral_norm (F := G)
        (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) (fun k => ?_) ?_).tsum_eq.symm
      · exact (Continuous.intervalIntegrable (by dsimp [G]; fun_prop) 0 (2 * Real.pi)).1
      · refine (hsumR.mul_left (2 * Real.pi)).of_nonneg_of_le
          (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
        have hconst : ∀ θ : ℝ, ‖G k θ‖ = ‖a k‖ * R ^ k := fun θ => by
          dsimp [G]
          rw [norm_mul, norm_mul, RCLike.norm_conj, norm_pow, Complex.norm_real,
            Real.norm_of_nonneg hR.le, hnorm_exp _ θ, mul_one]
        simp_rw [hconst]
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc,
          sub_zero, ENNReal.toReal_ofReal (by positivity)]
    rw [hint_tsum]
    have hall0 : ∀ k : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), G k θ = 0 := fun k => by
      dsimp [G]
      rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
      have hne : -((k : ℤ) + (n : ℤ)) ≠ 0 := by omega
      rw [if_neg hne, mul_zero]
    simp [hall0]
  -- Combine hint_pos n and hint_neg to extract Re(h)
  have hcont_h : Continuous (fun θ : ℝ => h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :=
    hh.continuous.comp (by fun_prop)
  have hint_M : ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (M : ℂ) * Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) = 0 := by
    rw [intervalIntegral.integral_const_mul]
    have h1 := integral_exp_int_mul_I (-(n : ℤ))
    have hne : -(n : ℤ) ≠ 0 := by omega
    rw [if_neg hne] at h1
    have h2 : (fun θ : ℝ => Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))) =
        (fun θ : ℝ => Complex.exp (((-(n : ℤ) : ℤ) : ℂ) * (θ : ℂ) * Complex.I)) := by
      ext θ; congr 1; push_cast; ring
    rw [h2, h1, mul_zero]
  have hint_re_n : ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ((M - (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re : ℝ) : ℂ) *
        Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) =
      -(Real.pi : ℂ) * a n * (R : ℂ) ^ n := by
    have hsub : ∀ θ : ℝ,
        ((M - (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re : ℝ) : ℂ) *
          Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) =
        (M : ℂ) * Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) -
          (1 / 2 : ℂ) * (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) +
          starRingEnd ℂ (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
            Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))) := fun θ => by
      have hre := Complex.add_conj (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      push_cast at hre ⊢
      linear_combination (1 / 2 : ℂ) * Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)) * hre
    simp_rw [hsub]
    have hi1 : IntervalIntegrable (fun θ : ℝ => (M : ℂ) * Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I)))
        volume 0 (2 * Real.pi) := Continuous.intervalIntegrable (by fun_prop) _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
        Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))) volume 0 (2 * Real.pi) :=
      Continuous.intervalIntegrable (hcont_h.mul (by fun_prop)) _ _
    have hi3 : IntervalIntegrable (fun θ : ℝ => starRingEnd ℂ (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
        Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))) volume 0 (2 * Real.pi) :=
      Continuous.intervalIntegrable ((Complex.continuous_conj.comp hcont_h).mul (by fun_prop)) _ _
    rw [intervalIntegral.integral_sub hi1 ((hi2.add hi3).const_mul _),
      hint_M, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi2 hi3,
      hint_pos n, hint_neg]
    ring
  -- Mean value of Re(h) on the circle equals Re(h(c))
  have hint_re_0 : ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (M - (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re) =
      2 * Real.pi * (M - (h c).re) := by
    have h0 := hint_pos 0
    simp only [Nat.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, pow_zero, a,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero] at h0
    have h0re : ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re = 2 * Real.pi * (h c).re := by
      have hch : IntervalIntegrable
          (fun θ : ℝ => h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) volume 0 (2 * Real.pi) :=
        hcont_h.intervalIntegrable 0 (2 * Real.pi)
      have hcomp := Complex.reCLM.intervalIntegral_comp_comm hch
      rw [h0] at hcomp
      simpa using hcomp
    have hci : IntervalIntegrable (fun _ : ℝ => M) volume 0 (2 * Real.pi) := intervalIntegrable_const
    have hcont_re : Continuous (fun θ : ℝ => (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re) :=
      Complex.continuous_re.comp hcont_h
    have hcre : IntervalIntegrable
        (fun θ : ℝ => (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re) volume 0 (2 * Real.pi) :=
      hcont_re.intervalIntegrable 0 (2 * Real.pi)
    rw [intervalIntegral.integral_sub hci hcre,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, h0re]
    ring
  have hnorm_bound : Real.pi * (‖a n‖ * R ^ n) ≤ 2 * Real.pi * (M - (h c).re) := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := fun θ : ℝ =>
        ((M - (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re : ℝ) : ℂ) *
          Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))) (by positivity)
    rw [hint_re_n] at h1
    have hlhs : ‖-(Real.pi : ℂ) * a n * (R : ℂ) ^ n‖ = Real.pi * (‖a n‖ * R ^ n) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, mul_assoc]
    have hrhs : ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖((M - (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re : ℝ) : ℂ) *
          Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))‖ =
        2 * Real.pi * (M - (h c).re) := by
      rw [← hint_re_0]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hnn : 0 ≤ M - (h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re := by
        linarith [hM θ]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn,
        show -((n : ℂ) * (θ : ℂ) * Complex.I) = (((-(n : ℝ)) * θ : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    linarith
  nlinarith [Real.pi_pos]

/- ### Step 4: 1D Pigeonhole on [X, 2 * X] and discrete zeros -/

private lemma pigeonhole_radius {X : ℝ} (hX : 0 < X) (S : Finset ℝ) :
    ∃ R ∈ Set.Icc X (2 * X), ∀ g ∈ S, X / (2 * (S.card + 1 : ℝ)) ≤ |R - g| := by
  let M : ℕ := S.card
  let Rpt : ℕ → ℝ := fun j => X + ((2 * (j : ℝ) + 1) / (2 * (M + 1 : ℝ))) * X
  let δ : ℝ := X / (2 * (M + 1 : ℝ))
  have hM1 : (0 : ℝ) < (M + 1 : ℝ) := by positivity
  have hδpos : 0 < δ := by positivity
  have hmem : ∀ j ∈ Finset.range (M + 1), Rpt j ∈ Set.Icc X (2 * X) := by
    intro j hj
    have hjlt : j < M + 1 := Finset.mem_range.mp hj
    have hjle : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show j ≤ M by omega)
    constructor
    · dsimp [Rpt]
      have : 0 ≤ (2 * (j : ℝ) + 1) / (2 * (M + 1 : ℝ)) * X := by positivity
      linarith
    · dsimp [Rpt]
      have hfrac : (2 * (j : ℝ) + 1) / (2 * (M + 1 : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
  have hsep : ∀ j1 j2 : ℕ, j1 ≠ j2 → 2 * δ ≤ |Rpt j1 - Rpt j2| := by
    intro j1 j2 hne
    have hdiff : Rpt j1 - Rpt j2 = (((j1 : ℝ) - (j2 : ℝ)) / (M + 1 : ℝ)) * X := by
      dsimp [Rpt]; field_simp [hM1.ne']; ring
    rw [hdiff, abs_mul, abs_div, abs_of_pos hM1, abs_of_pos hX]
    have habs : (1 : ℝ) ≤ |(j1 : ℝ) - (j2 : ℝ)| := by
      rcases lt_or_gt_of_ne hne with h | h
      · have hle : (j1 : ℝ) + 1 ≤ (j2 : ℝ) := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]
        linarith
      · have hle : (j2 : ℝ) + 1 ≤ (j1 : ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]
        linarith
    dsimp [δ]
    have h2δ : 2 * (X / (2 * (M + 1 : ℝ))) = (1 / (M + 1 : ℝ)) * X := by field_simp [hM1.ne']
    rw [h2δ]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right habs hM1.le) hX.le
  -- Every g ∈ S is within < δ of at most one j ∈ range (M + 1)
  let bad := (Finset.range (M + 1)).filter (fun j => ∃ g ∈ S, |Rpt j - g| < δ)
  have hbad_card : bad.card ≤ S.card := by
    have hchoose : ∀ j ∈ bad, ∃ g ∈ S, |Rpt j - g| < δ := fun j hj => (Finset.mem_filter.mp hj).2
    classical
    let f : ℕ → ℝ := fun j => if hj : j ∈ bad then (hchoose j hj).choose else 0
    refine Finset.card_le_card_of_injOn f (fun j hj => ?_) (fun j1 hj1 j2 hj2 heq => ?_)
    · simp only [Finset.mem_coe] at hj ⊢
      dsimp [f]; rw [dif_pos hj]; exact (hchoose j hj).choose_spec.1
    · simp only [Finset.mem_coe] at hj1 hj2
      dsimp [f] at heq
      rw [dif_pos hj1, dif_pos hj2] at heq
      by_contra hne
      have h1 := (hchoose j1 hj1).choose_spec.2
      have h2 := (hchoose j2 hj2).choose_spec.2
      rw [← heq] at h2
      have htri : |Rpt j1 - Rpt j2| ≤ |Rpt j1 - (hchoose j1 hj1).choose| +
          |Rpt j2 - (hchoose j1 hj1).choose| := by
        have := abs_sub_le (Rpt j1) (hchoose j1 hj1).choose (Rpt j2)
        rwa [abs_sub_comm (hchoose j1 hj1).choose (Rpt j2)] at this
      have hs := hsep j1 j2 hne
      linarith
  have hlt : bad.card < (Finset.range (M + 1)).card := by
    rw [Finset.card_range]; dsimp [M]; omega
  obtain ⟨j, hj_mem, hj_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨Rpt j, hmem j hj_mem, fun g hg => ?_⟩
  by_contra hlt'
  push Not at hlt'
  exact hj_not (Finset.mem_filter.mpr ⟨hj_mem, g, hg, hlt'⟩)

private lemma finite_zeros_on_Ioc (T : ℝ) :
    Set.Finite {g : ℝ | 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0} := by
  let K : Set ℂ := (fun g : ℝ => (1 / 2 : ℂ) + (g : ℂ) * Complex.I) '' Set.Icc 0 T
  have hK_compact : IsCompact K := isCompact_Icc.image (by fun_prop)
  let Z : Set ℂ := {z ∈ K | L4 z = 0}
  have hZ_closed : IsClosed Z :=
    hK_compact.isClosed.inter (isClosed_eq L4_differentiable.continuous continuous_const)
  have hZ_compact : IsCompact Z := hK_compact.of_isClosed_subset hZ_closed (Set.sep_subset K _)
  have hZ_discrete : ∀ z ∈ Z, ∃ U ∈ 𝓝 z, U ∩ Z = {z} := by
    intro z hz
    have hne_all : ¬ Set.EqOn L4 0 Set.univ := fun heq =>
      L4_real_ne_zero (by norm_num : (0 : ℝ) < 1) (heq (Set.mem_univ (1 : ℂ)))
    have han : AnalyticOnNhd ℂ L4 Set.univ :=
      L4_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have hnotfreq : ¬ ∃ᶠ w in 𝓝[≠] z, L4 w = 0 := fun hfreq =>
      hne_all (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ z) hfreq)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff] at hnotfreq
    obtain ⟨U, hU_sub, hU_open, hzU⟩ := eventually_nhds_iff.mp hnotfreq
    refine ⟨U, hU_open.mem_nhds hzU, ?_⟩
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hwU, hwZ⟩
      by_contra hwne
      exact hU_sub w hwU hwne hwZ.2
    · rintro rfl; exact ⟨hzU, hz⟩
  have hZ_fin : Z.Finite := by
    have hopen_cov : Z ⊆ ⋃ z : Z, interior (hZ_discrete z.1 z.2).choose := fun z hz =>
      Set.mem_iUnion.mpr ⟨⟨z, hz⟩, mem_interior_iff_mem_nhds.mpr (hZ_discrete z hz).choose_spec.1⟩
    obtain ⟨F, hF⟩ := hZ_compact.elim_finite_subcover
      (fun z : Z => interior (hZ_discrete z.1 z.2).choose)
      (fun z => isOpen_interior) hopen_cov
    have hsub : Z ⊆ F.image Subtype.val := by
      intro w hw
      have hwU := hF hw
      simp only [Set.mem_iUnion] at hwU
      obtain ⟨z, hzF, hwint⟩ := hwU
      have hwmem : w ∈ (hZ_discrete z.1 z.2).choose ∩ Z := ⟨interior_subset hwint, hw⟩
      rw [(hZ_discrete z.1 z.2).choose_spec.2, Set.mem_singleton_iff] at hwmem
      subst hwmem
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem Subtype.val hzF)
    exact (F.image Subtype.val).finite_toSet.subset hsub
  have hinj : Set.InjOn (fun g : ℝ => (1 / 2 : ℂ) + (g : ℂ) * Complex.I)
      {g : ℝ | 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0} := by
    intro g1 _ g2 _ heq
    have := congrArg Complex.im heq
    simpa using this
  refine Set.Finite.of_finite_image (hZ_fin.subset ?_) hinj
  rintro _ ⟨g, ⟨hg0, hgT, hgz⟩, rfl⟩
  exact ⟨⟨g, ⟨hg0.le, hgT⟩, rfl⟩, hgz⟩

private lemma analyticOrderAt_finset_prod_aux {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ)
    (hF : ∀ i ∈ s, AnalyticAt ℂ (F i) z) :
    analyticOrderAt (fun w => ∏ i ∈ s, F i w) z = ∑ i ∈ s, analyticOrderAt (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  | @insert a s ha ih =>
    have hFa : AnalyticAt ℂ (F a) z := hF a (Finset.mem_insert_self a s)
    have hFs : AnalyticAt ℂ (fun w => ∏ i ∈ s, F i w) z :=
      Finset.analyticAt_fun_prod s fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hprod_eq : (fun w => ∏ i ∈ insert a s, F i w) = F a * (fun w => ∏ i ∈ s, F i w) := by
      ext w; simp [Finset.prod_insert ha]
    rw [hprod_eq, analyticOrderAt_mul hFa hFs, Finset.sum_insert ha,
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

set_option maxHeartbeats 1600000 in
private theorem critical_line_zero_count_param (M_param : ℝ) (hM_param : 0 < M_param)
    (hRH : ∀ s : ℂ, 1 / 2 < s.re → L4 s ≠ 0) :
    ∃ (T : ℝ) (Z : Finset ℝ), 2 ≤ T ∧
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0) ∧
      M_param * T < ∑ g ∈ Z.filter (fun g => 1 ≤ g ∧ g ≤ T / 2),
        ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) := by
  classical
  -- Step 5a: All zeros of xi4 lie on Re(s) = 1/2 with Im(s) ≠ 0
  have hxi_nz_off : ∀ s : ℂ, s.re ≠ 1 / 2 → xi4 s ≠ 0 := by
    intro s hs
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · have h1s : 1 / 2 < (1 - s).re := by simp; linarith
      have hne1 : xi4 (1 - s) ≠ 0 := by
        rw [xi4_eq_L4_mul_gammaℝ (by linarith)]
        exact mul_ne_zero (hRH (1 - s) h1s) (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
      rw [xi4_functional_eq] at hne1
      exact right_ne_zero_of_mul hne1
    · rw [xi4_eq_L4_mul_gammaℝ (by linarith)]
      exact mul_ne_zero (hRH s hgt) (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
  have hxi_half_ne : xi4 (1 / 2 : ℂ) ≠ 0 := by
    rw [xi4_eq_L4_mul_gammaℝ (by norm_num)]
    exact mul_ne_zero (by simpa using L4_real_ne_zero (by norm_num : (0 : ℝ) < 1 / 2))
      (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  -- Analytic orders of xi4 and L4 agree on Re(s) = 1/2, and are symmetric under conjugation
  have hord_xi_eq_L : ∀ g : ℝ,
      analyticOrderAt xi4 (1 / 2 + (g : ℂ) * Complex.I) =
      analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I) := by
    intro g
    set z : ℂ := 1 / 2 + (g : ℂ) * Complex.I
    have hre : -1 < z.re := by simp [z]; norm_num
    have hev : xi4 =ᶠ[𝓝 z] fun w => L4 w * Complex.Gammaℝ (w + 1) := by
      refine Filter.eventually_of_mem
        ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hre) ?_
      intro w hw; exact xi4_eq_L4_mul_gammaℝ hw
    have hG_an : AnalyticAt ℂ (fun w => Complex.Gammaℝ (w + 1)) z := by
      have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
      have hdiff : DifferentiableOn ℂ (fun w => Complex.Gammaℝ (w + 1)) {w : ℂ | -1 < w.re} := by
        intro w hw
        have hw' : -1 < w.re := hw
        have hwre : 0 < ((w + 1) / 2).re := by simp only [div_ofNat_re, add_re, one_re]; linarith
        have hGdiff : DifferentiableAt ℂ Complex.Gamma ((w + 1) / 2) :=
          Complex.differentiableAt_Gamma _ (fun m => by
            intro hm
            have := congrArg Complex.re hm
            simp only [neg_re, natCast_re] at this
            linarith [Nat.cast_nonneg (α := ℝ) m])
        have hpi : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2)) w :=
          (differentiableAt_const _).cpow
            (((differentiableAt_id.add_const 1).neg).div_const 2)
            (Or.inl (by simp; exact Real.pi_pos))
        have hcomp : DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma ((u + 1) / 2)) w :=
          hGdiff.comp w ((differentiableAt_id.add_const 1).div_const 2)
        have hmul : DifferentiableAt ℂ
            (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2) * Complex.Gamma ((u + 1) / 2)) w :=
          hpi.fun_mul hcomp
        have heq : (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2) * Complex.Gamma ((u + 1) / 2)) =
            (fun u : ℂ => Complex.Gammaℝ (u + 1)) := by
          ext u; simp [Complex.Gammaℝ_def]
        rw [heq] at hmul
        exact hmul.differentiableWithinAt
      exact (hdiff.analyticOnNhd hopen) z hre
    have hG_nz : Complex.Gammaℝ (z + 1) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp [z]; norm_num)
    rw [analyticOrderAt_congr hev]
    change analyticOrderAt (L4 * fun w => Complex.Gammaℝ (w + 1)) z = analyticOrderAt L4 z
    rw [analyticOrderAt_mul (L4_differentiable.analyticAt z) hG_an,
      hG_an.analyticOrderAt_eq_zero.mpr hG_nz, add_zero]
  have hord_xi_ne_top : ∀ z : ℂ, analyticOrderAt xi4 z ≠ ⊤ := by
    intro z
    rw [ne_eq, analyticOrderAt_eq_top]
    intro hev
    have h0 := (xi4_differentiable.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ (1 / 2 : ℂ))
    exact hxi_half_ne h0
  have hord_xi_conj : ∀ g : ℝ,
      analyticOrderAt xi4 (1 / 2 - (g : ℂ) * Complex.I) =
      analyticOrderAt xi4 (1 / 2 + (g : ℂ) * Complex.I) := by
    intro g
    set z : ℂ := 1 / 2 + (g : ℂ) * Complex.I
    set zc : ℂ := 1 / 2 - (g : ℂ) * Complex.I
    have hzc : starRingEnd ℂ z = zc := by
      dsimp [z, zc]
      simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hzc' : starRingEnd ℂ zc = z := by
      rw [← hzc, Complex.conj_conj]
    have hfin := hord_xi_ne_top z
    obtain ⟨f, hf_an, hfz, hfeq⟩ := (xi4_differentiable.analyticAt z).analyticOrderAt_ne_top.mp hfin
    let n := analyticOrderNatAt xi4 z
    have hn_eq : analyticOrderAt xi4 z = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt hfin).symm
    let fc : ℂ → ℂ := fun w => starRingEnd ℂ (f (starRingEnd ℂ w))
    have hfc_an : AnalyticAt ℂ fc zc := by
      have hdiff_on : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w :=
        (hf_an.eventually_analyticAt).mono fun w hw => hw.differentiableAt
      obtain ⟨U, hUsub, hUopen, hzU⟩ := eventually_nhds_iff.mp hdiff_on
      have hUc_open : IsOpen (starRingEnd ℂ ⁻¹' U) := hUopen.preimage Complex.continuous_conj
      have hzcU : zc ∈ starRingEnd ℂ ⁻¹' U := by
        change starRingEnd ℂ zc ∈ U
        rwa [hzc']
      have hdiff_c : DifferentiableOn ℂ fc (starRingEnd ℂ ⁻¹' U) := fun w hw =>
        (differentiableAt_conj_comp (hUsub _ hw)).differentiableWithinAt
      exact (DifferentiableOn.analyticOnNhd hdiff_c hUc_open) zc hzcU
    have hfcz : fc zc ≠ 0 := by
      dsimp [fc]; rw [hzc']; exact (map_ne_zero (starRingEnd ℂ)).mpr hfz
    have hfeqc : ∀ᶠ w in 𝓝 zc, xi4 w = (w - zc) ^ n • fc w := by
      have hnh : Filter.Tendsto (starRingEnd ℂ) (𝓝 zc) (𝓝 z) := by
        simpa [hzc'] using Complex.continuous_conj.tendsto zc
      filter_upwards [hnh hfeq] with w hw
      have h1 := congrArg (starRingEnd ℂ) hw
      rw [← xi4_conj, Complex.conj_conj, smul_eq_mul, map_mul, map_pow, map_sub,
        Complex.conj_conj, hzc] at h1
      simpa [fc, smul_eq_mul] using h1
    rw [hn_eq, (xi4_differentiable.analyticAt zc).analyticOrderAt_eq_natCast]
    exact ⟨fc, hfc_an, hfcz, hfeqc⟩
  -- Step 5b: Assume for contradiction that no cutoff T ≥ 2 has > 32 * T zeros on [1, T/2]
  by_contra hcontra
  have hbound_all : ∀ T : ℝ, 2 ≤ T →
      ∑ g ∈ ((finite_zeros_on_Ioc T).toFinset).filter (fun g => 1 ≤ g ∧ g ≤ T / 2),
        ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) ≤ M_param * T := by
    intro T hT
    by_contra hgt
    push Not at hgt
    exact hcontra ⟨T, (finite_zeros_on_Ioc T).toFinset, hT,
      fun g => (finite_zeros_on_Ioc T).mem_toFinset, hgt⟩
  -- Define unit annulus blocks B k = zeros in (k, k + 1]
  let B : ℕ → Finset ℝ := fun k =>
    ((finite_zeros_on_Ioc (k + 1 : ℝ)).toFinset).filter (fun g => (k : ℝ) < g)
  let mult : ℝ → ℕ := fun g => (analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat
  have hB_mem : ∀ k g, g ∈ B k ↔ (k : ℝ) < g ∧ g ≤ (k + 1 : ℝ) ∧
      L4 (1 / 2 + (g : ℂ) * Complex.I) = 0 := by
    intro k g
    simp only [B, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨_, hle, hz⟩, hgt⟩; exact ⟨hgt, hle, hz⟩
    · rintro ⟨hgt, hle, hz⟩
      exact ⟨⟨lt_of_le_of_lt (Nat.cast_nonneg k) hgt, hle, hz⟩, hgt⟩
  have hB_disj : Pairwise (fun k1 k2 => Disjoint (B k1) (B k2)) := by
    intro k1 k2 hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (hB_mem k1 g).mp hg1
    have h2 := (hB_mem k2 g).mp hg2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (k1 + 1 : ℝ) ≤ (k2 : ℝ) := by exact_mod_cast hlt
      linarith
    · have : (k2 + 1 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hgt
      linarith
  -- Weight of block k and cumulative count Ncount K = ∑_{k < K} w k
  let w : ℕ → ℝ := fun k => ∑ g ∈ B k, (mult g : ℝ)
  let Ncount : ℕ → ℝ := fun K => ∑ k ∈ Finset.range K, w k
  have hw_nn : ∀ k, 0 ≤ w k := fun k => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hNcount_le : ∀ K : ℕ, Ncount K ≤ w 0 + (2 * M_param) * (K : ℝ) := by
    intro K
    rcases K with _ | K
    · simp [Ncount, hw_nn 0]
    · by_cases hK0 : K = 0
      · subst hK0; simp [Ncount]; linarith
      · have hK1 : 1 ≤ K := by omega
        let T : ℝ := 2 * (K + 1 : ℝ)
        have hT2 : 2 ≤ T := by
          dsimp [T]
          have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
          linarith
        have hsum_split : Ncount (K + 1) = w 0 + ∑ k ∈ Finset.Ico 1 (K + 1), w k := by
          dsimp [Ncount]
          simpa using Finset.sum_range_eq_add_Ico w (Nat.succ_pos K)
        rw [hsum_split]
        have hbi : ∑ k ∈ Finset.Ico 1 (K + 1), w k =
            ∑ g ∈ (Finset.Ico 1 (K + 1)).biUnion B, (mult g : ℝ) := by
          rw [Finset.sum_biUnion (fun a _ b _ hab => hB_disj hab)]
        have hsub : (Finset.Ico 1 (K + 1)).biUnion B ⊆
            ((finite_zeros_on_Ioc T).toFinset).filter (fun g => 1 ≤ g ∧ g ≤ T / 2) := by
          intro g hg
          obtain ⟨k, hk, hgk⟩ := Finset.mem_biUnion.mp hg
          obtain ⟨hk1, hkK⟩ := Finset.mem_Ico.mp hk
          obtain ⟨hgt, hle, hz⟩ := (hB_mem k g).mp hgk
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          have hk1le : (k + 1 : ℝ) ≤ (K + 1 : ℝ) := by exact_mod_cast hkK
          refine ⟨⟨by linarith, by dsimp [T]; linarith, hz⟩, by linarith, by dsimp [T]; linarith⟩
        have hle_T := hbound_all T hT2
        have hle_sub : ∑ g ∈ (Finset.Ico 1 (K + 1)).biUnion B, (mult g : ℝ) ≤
            ∑ g ∈ ((finite_zeros_on_Ioc T).toFinset).filter (fun g => 1 ≤ g ∧ g ≤ T / 2),
              (mult g : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
        have hT64 : M_param * T = (2 * M_param) * ((K + 1 : ℕ) : ℝ) := by dsimp [T]; push_cast; ring
        linarith
  -- Step 5c: Tail convergence of ∑_{k ≥ K0} w k / k^2 ≤ 5 * C0 / K0
  let C0 : ℝ := w 0 + 2 * M_param + 1
  have hC0pos : 0 < C0 := by dsimp [C0]; linarith [hw_nn 0]
  have hsum_tail_bound : ∀ K0 : ℕ, 1 ≤ K0 →
      Summable (fun k : ℕ => w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2) ∧
      ∑' k : ℕ, w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2 ≤ 5 * C0 / (K0 : ℝ) := by
    intro K0 hK0
    have htel_all : ∀ m : ℕ,
        ∑ k ∈ Finset.range m, (1 / ((K0 + k : ℕ) : ℝ) - 1 / ((K0 + k + 1 : ℕ) : ℝ)) =
          1 / (K0 : ℝ) - 1 / ((K0 + m : ℕ) : ℝ) := by
      intro m
      induction m with
      | zero => simp
      | succ d ihd =>
        rw [Finset.sum_range_succ, ihd]
        have hadd : K0 + (d + 1) = K0 + d + 1 := by omega
        rw [hadd]; ring
    have hpart_le : ∀ M : ℕ,
        ∑ k ∈ Finset.range M, w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2 ≤ 5 * C0 / (K0 : ℝ) := by
      intro M
      rcases M with _ | M
      · simp; positivity
      · have hstep : ∀ k : ℕ, w (K0 + k) = Ncount (K0 + k + 1) - Ncount (K0 + k) := fun k => by
          dsimp [Ncount]; rw [Finset.sum_range_succ]; ring
        have hsbp : ∑ k ∈ Finset.range (M + 1), w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2 =
            Ncount (K0 + M + 1) / ((K0 + M : ℕ) : ℝ) ^ 2 -
            Ncount K0 / (K0 : ℝ) ^ 2 +
            ∑ k ∈ Finset.range M, Ncount (K0 + k + 1) *
              (1 / ((K0 + k : ℕ) : ℝ) ^ 2 - 1 / ((K0 + k + 1 : ℕ) : ℝ) ^ 2) := by
          induction M with
          | zero => simp [hstep]; ring
          | succ m ih =>
            rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hstep (m + 1)]
            have hadd : K0 + (m + 1) = K0 + m + 1 := by omega
            rw [hadd]
            ring
        rw [hsbp]
        have hN_nonneg : 0 ≤ Ncount K0 / (K0 : ℝ) ^ 2 := by
          refine div_nonneg (Finset.sum_nonneg fun _ _ => hw_nn _) (sq_nonneg _)
        have hterm_top : Ncount (K0 + M + 1) / ((K0 + M : ℕ) : ℝ) ^ 2 ≤ 2 * C0 / (K0 : ℝ) := by
          have h1 := hNcount_le (K0 + M + 1)
          have hKM : (K0 : ℝ) ≤ ((K0 + M : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right K0 M
          have hKMpos : (0 : ℝ) < ((K0 + M : ℕ) : ℝ) := by positivity
          have hnum : Ncount (K0 + M + 1) ≤ 2 * C0 * ((K0 + M : ℕ) : ℝ) := by
            have h1' : (1 : ℝ) ≤ (K0 : ℝ) + (M : ℝ) := by
              have : (1 : ℝ) ≤ ((K0 + M : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ K0 + M by omega)
              simpa using this
            dsimp [C0] at *; push_cast at h1 ⊢; nlinarith [hw_nn 0]
          calc
            Ncount (K0 + M + 1) / ((K0 + M : ℕ) : ℝ) ^ 2
                ≤ (2 * C0 * ((K0 + M : ℕ) : ℝ)) / ((K0 + M : ℕ) : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_right hnum (sq_nonneg _)
            _ = 2 * C0 / ((K0 + M : ℕ) : ℝ) := by field_simp [hKMpos.ne']
            _ ≤ 2 * C0 / (K0 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by positivity) hKM
        have hsum_diff : ∑ k ∈ Finset.range M, Ncount (K0 + k + 1) *
              (1 / ((K0 + k : ℕ) : ℝ) ^ 2 - 1 / ((K0 + k + 1 : ℕ) : ℝ) ^ 2) ≤
            3 * C0 / (K0 : ℝ) := by
          have htele : ∑ k ∈ Finset.range M,
              (3 * C0) * (1 / ((K0 + k : ℕ) : ℝ) - 1 / ((K0 + k + 1 : ℕ) : ℝ)) ≤
              3 * C0 / (K0 : ℝ) := by
            rw [← Finset.mul_sum, htel_all M]
            have : 0 ≤ 1 / ((K0 + M : ℕ) : ℝ) := by positivity
            nlinarith [show (3 * C0) * (1 / (K0 : ℝ)) = 3 * C0 / (K0 : ℝ) by ring]
          refine le_trans ?_ htele
          refine Finset.sum_le_sum fun k _ => ?_
          set x : ℝ := ((K0 + k : ℕ) : ℝ)
          have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ K0 + k by omega)
          have hxpos : 0 < x := by linarith
          have hx1pos : 0 < x + 1 := by linarith
          have hN_le : Ncount (K0 + k + 1) ≤ C0 * (x + 1) := by
            have h1 := hNcount_le (K0 + k + 1)
            dsimp [C0, x] at *; push_cast at h1 ⊢; nlinarith [hw_nn 0]
          have hdiff_nn : 0 ≤ 1 / x ^ 2 - 1 / (x + 1) ^ 2 := by
            rw [sub_nonneg]; exact one_div_le_one_div_of_le (sq_pos_of_pos hxpos) (by nlinarith)
          have hcast : ((K0 + k + 1 : ℕ) : ℝ) = x + 1 := by dsimp [x]; push_cast; ring
          rw [hcast]
          calc
            Ncount (K0 + k + 1) * (1 / x ^ 2 - 1 / (x + 1) ^ 2)
                ≤ (C0 * (x + 1)) * (1 / x ^ 2 - 1 / (x + 1) ^ 2) :=
                  mul_le_mul_of_nonneg_right hN_le hdiff_nn
            _ = C0 * ((2 * x + 1) / (x ^ 2 * (x + 1))) := by
                  field_simp [hxpos.ne', hx1pos.ne']; ring
            _ ≤ (3 * C0) * (1 / x - 1 / (x + 1)) := by
                  have : (3 * C0) * (1 / x - 1 / (x + 1)) = C0 * (3 / (x * (x + 1))) := by
                    field_simp [hxpos.ne', hx1pos.ne']; ring
                  rw [this]
                  refine mul_le_mul_of_nonneg_left ?_ hC0pos.le
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith
        have hadd5 : 2 * C0 / (K0 : ℝ) + 3 * C0 / (K0 : ℝ) = 5 * C0 / (K0 : ℝ) := by ring
        linarith
    have hsum : Summable (fun k : ℕ => w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2) :=
      summable_of_sum_range_le (fun k => div_nonneg (hw_nn _) (sq_nonneg _)) hpart_le
    exact ⟨hsum, hsum.tsum_le_of_sum_range_le hpart_le⟩
  -- Step 5d: Annulus-blocked canonical product P(s)
  let Fblk : ℕ → ℂ → ℂ := fun k s =>
    ∏ g ∈ B k, (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2) ^ (mult g)
  let tailLog : ℕ → ℂ → ℂ := fun K0 s =>
    ∑' k : ℕ, ∑ g ∈ B (K0 + k), (mult g : ℂ) * Complex.log (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2)
  let P : ℂ → ℂ := fun s => limUnder atTop (fun N : ℕ => ∏ k ∈ Finset.range N, Fblk k s)
  -- Local representation of P on Metric.ball (1/2) R for K0 ≥ 2 * R + 1
  have hP_local : ∀ (R : ℝ), 0 < R → ∀ (K0 : ℕ), 1 ≤ K0 → 2 * R ≤ (K0 : ℝ) →
      DifferentiableOn ℂ (tailLog K0) (Metric.ball (1 / 2 : ℂ) R) ∧
      (∀ s ∈ Metric.ball (1 / 2 : ℂ) R,
        ‖tailLog K0 s‖ ≤ 8 * C0 * R ^ 2 / (K0 : ℝ) ∧
        P s = (∏ k ∈ Finset.range K0, Fblk k s) * Complex.exp (tailLog K0 s)) := by
    intro R hR K0 hK0 h2R
    let termK : ℕ → ℂ → ℂ := fun k s =>
      ∑ g ∈ B (K0 + k), (mult g : ℂ) * Complex.log (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2)
    let u : ℕ → ℝ := fun k => (3 / 2 : ℝ) * R ^ 2 * (w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2)
    have hu_sum : Summable u := (hsum_tail_bound K0 hK0).1.mul_left _
    have hratio_le : ∀ k : ℕ, ∀ g ∈ B (K0 + k), ∀ s ∈ Metric.ball (1 / 2 : ℂ) R,
        ‖(s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ ≤ 1 / 4 ∧
        ‖(s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ ≤ R ^ 2 / ((K0 + k : ℕ) : ℝ) ^ 2 := by
      intro k g hg s hs
      have hgt : ((K0 + k : ℕ) : ℝ) < g := (hB_mem (K0 + k) g).mp hg |>.1
      have hKpos : (0 : ℝ) < ((K0 + k : ℕ) : ℝ) := by positivity
      have hgpos : 0 < g := hKpos.trans hgt
      have hsR : ‖s - 1 / 2‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have hnorm_eq : ‖(s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ = ‖s - 1 / 2‖ ^ 2 / g ^ 2 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hgpos.le]
      rw [hnorm_eq]
      have hle_R : ‖s - 1 / 2‖ ^ 2 / g ^ 2 ≤ R ^ 2 / ((K0 + k : ℕ) : ℝ) ^ 2 := by
        refine div_le_div₀ (sq_nonneg R) (pow_le_pow_left₀ (norm_nonneg _) hsR.le 2)
          (sq_pos_of_pos hKpos) (pow_le_pow_left₀ hKpos.le hgt.le 2)
      have hle_quarter : R ^ 2 / ((K0 + k : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
        have h2Rk : 2 * R ≤ ((K0 + k : ℕ) : ℝ) :=
          le_trans h2R (by exact_mod_cast Nat.le_add_right K0 k)
        rw [div_le_iff₀ (sq_pos_of_pos hKpos)]
        nlinarith
      exact ⟨hle_R.trans hle_quarter, hle_R⟩
    have hterm_le : ∀ k : ℕ, ∀ s ∈ Metric.ball (1 / 2 : ℂ) R, ‖termK k s‖ ≤ u k := by
      intro k s hs
      dsimp [termK, u]
      calc
        ‖∑ g ∈ B (K0 + k), (mult g : ℂ) * Complex.log (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2)‖
            ≤ ∑ g ∈ B (K0 + k), ‖(mult g : ℂ) * Complex.log (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2)‖ :=
              norm_sum_le _ _
        _ ≤ ∑ g ∈ B (K0 + k), (mult g : ℝ) * ((3 / 2 : ℝ) * (R ^ 2 / ((K0 + k : ℕ) : ℝ) ^ 2)) := by
              refine Finset.sum_le_sum fun g hg => ?_
              rw [norm_mul, Complex.norm_natCast]
              have ⟨hr1, hr2⟩ := hratio_le k g hg s hs
              have hlog := Complex.norm_log_one_add_half_le_self (by linarith : ‖(s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ ≤ 1 / 2)
              exact mul_le_mul_of_nonneg_left (hlog.trans (by linarith)) (Nat.cast_nonneg _)
        _ = (3 / 2 : ℝ) * R ^ 2 * (w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2) := by
              rw [← Finset.sum_mul]; dsimp [w]; ring
    have hterm_diff : ∀ k : ℕ, DifferentiableOn ℂ (termK k) (Metric.ball (1 / 2 : ℂ) R) := by
      intro k s hs
      refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.fun_sum fun g hg => ?_
      have hgt : ((K0 + k : ℕ) : ℝ) < g := (hB_mem (K0 + k) g).mp hg |>.1
      have hgpos : 0 < g := lt_trans (by positivity) hgt
      have hre : 0 < (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2).re := by
        have hr1 := (hratio_le k g hg s hs).1
        have hre_le : |((s - 1 / 2) ^ 2 / (g : ℂ) ^ 2).re| ≤ 1 / 4 :=
          (Complex.abs_re_le_norm _).trans hr1
        have := (abs_le.mp hre_le).1
        simp only [add_re, one_re]; linarith
      have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 + (z - 1 / 2) ^ 2 / (g : ℂ) ^ 2) s := by
        fun_prop
      exact (differentiableAt_const _).mul (hinner.clog (Or.inl hre))
    have hdiff_tail : DifferentiableOn ℂ (tailLog K0) (Metric.ball (1 / 2 : ℂ) R) :=
      differentiableOn_tsum_of_summable_norm hu_sum hterm_diff Metric.isOpen_ball hterm_le
    refine ⟨hdiff_tail, fun s hs => ⟨?_, ?_⟩⟩
    · have hnorm_tsum : ‖tailLog K0 s‖ ≤ ∑' k : ℕ, u k := by
        have hsum_k : Summable (fun k => termK k s) :=
          Summable.of_norm_bounded hu_sum (fun k => hterm_le k s hs)
        exact (norm_tsum_le_tsum_norm hsum_k.norm).trans
          (Summable.tsum_le_tsum (fun k => hterm_le k s hs) hsum_k.norm hu_sum)
      have hu_tsum : ∑' k : ℕ, u k ≤ 8 * C0 * R ^ 2 / (K0 : ℝ) := by
        dsimp [u]
        rw [tsum_mul_left]
        have htb := (hsum_tail_bound K0 hK0).2
        calc
          (3 / 2 : ℝ) * R ^ 2 * ∑' k : ℕ, w (K0 + k) / ((K0 + k : ℕ) : ℝ) ^ 2
              ≤ (3 / 2 : ℝ) * R ^ 2 * (5 * C0 / (K0 : ℝ)) :=
                mul_le_mul_of_nonneg_left htb (by positivity)
          _ ≤ 8 * C0 * R ^ 2 / (K0 : ℝ) := by
                have hpos : (0 : ℝ) ≤ C0 * R ^ 2 / (K0 : ℝ) := by positivity
                linarith [show (3 / 2 : ℝ) * R ^ 2 * (5 * C0 / (K0 : ℝ)) =
                  (15 / 2 : ℝ) * (C0 * R ^ 2 / (K0 : ℝ)) by ring,
                  show 8 * C0 * R ^ 2 / (K0 : ℝ) = 8 * (C0 * R ^ 2 / (K0 : ℝ)) by ring]
      exact hnorm_tsum.trans hu_tsum
    · -- Show partial products converge to (∏_{k < K0} Fblk k s) * exp(tailLog K0 s)
      have hsum_k : Summable (fun k => termK k s) :=
        Summable.of_norm_bounded hu_sum (fun k => hterm_le k s hs)
      have hF_eq_exp : ∀ k : ℕ, Fblk (K0 + k) s = Complex.exp (termK k s) := fun k => by
        dsimp [Fblk, termK]
        rw [Complex.exp_sum]
        refine Finset.prod_congr rfl fun g hg => ?_
        have hre : 0 < (1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2).re := by
          have hr1 := (hratio_le k g hg s hs).1
          have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hr1)).1
          simp only [add_re, one_re]; linarith
        have hne : 1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2 ≠ 0 := fun h => by
          rw [h, zero_re] at hre; linarith
        rw [Complex.exp_nat_mul, Complex.exp_log hne]
      have htend : Tendsto (fun N : ℕ => ∏ k ∈ Finset.range N, Fblk k s) atTop
          (𝓝 ((∏ k ∈ Finset.range K0, Fblk k s) * Complex.exp (tailLog K0 s))) := by
        have h1 : Tendsto (fun m : ℕ => (∏ k ∈ Finset.range K0, Fblk k s) *
            Complex.exp (∑ k ∈ Finset.range m, termK k s)) atTop
            (𝓝 ((∏ k ∈ Finset.range K0, Fblk k s) * Complex.exp (tailLog K0 s))) :=
          ((Complex.continuous_exp.tendsto _).comp hsum_k.hasSum.tendsto_sum_nat).const_mul _
        rw [← tendsto_add_atTop_iff_nat K0]
        refine h1.congr fun m => ?_
        rw [add_comm m K0, Finset.prod_range_add]
        congr 1
        rw [Complex.exp_sum]
        exact (Finset.prod_congr rfl fun k _ => hF_eq_exp k).symm
      exact htend.limUnder_eq
  have hP_diff : Differentiable ℂ P := by
    intro s
    let R : ℝ := ‖s - 1 / 2‖ + 1
    let K0 : ℕ := ⌈2 * R⌉₊ + 1
    have hR : 0 < R := by positivity
    have hK0 : 1 ≤ K0 := by omega
    have h2R : 2 * R ≤ (K0 : ℝ) := by
      dsimp [K0]; push_cast; linarith [Nat.le_ceil (2 * R)]
    obtain ⟨htd, hrep⟩ := hP_local R hR K0 hK0 h2R
    have hs_mem : s ∈ Metric.ball (1 / 2 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm]; dsimp [R]; linarith
    have hprod_diff : Differentiable ℂ (fun z => ∏ k ∈ Finset.range K0, Fblk k z) := by
      intro z
      refine DifferentiableAt.fun_finsetProd fun k _ => ?_
      refine DifferentiableAt.fun_finsetProd fun g _ => ?_
      fun_prop
    have hev : P =ᶠ[𝓝 s] fun z => (∏ k ∈ Finset.range K0, Fblk k z) * Complex.exp (tailLog K0 z) := by
      refine Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hs_mem) ?_
      intro z hz; exact (hrep z hz).2
    exact ((hprod_diff s).mul ((htd.differentiableAt (Metric.isOpen_ball.mem_nhds hs_mem)).cexp)).congr_of_eventuallyEq hev
  -- Step 5e: Exact order matching analyticOrderAt P z = analyticOrderAt xi4 z for all z ∈ ℂ
  have hord_P_eq_xi : ∀ z : ℂ, analyticOrderAt P z = analyticOrderAt xi4 z := by
    intro z
    let R : ℝ := ‖z - 1 / 2‖ + 2
    let K0 : ℕ := ⌈2 * R⌉₊ + 1
    have hR : 0 < R := by positivity
    have hK0 : 1 ≤ K0 := by omega
    have h2R : 2 * R ≤ (K0 : ℝ) := by
      dsimp [K0]; push_cast; linarith [Nat.le_ceil (2 * R)]
    obtain ⟨htd, hrep⟩ := hP_local R hR K0 hK0 h2R
    have hz_mem : z ∈ Metric.ball (1 / 2 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm]; dsimp [R]; linarith
    have hevP : P =ᶠ[𝓝 z] fun w => (∏ k ∈ Finset.range K0, Fblk k w) * Complex.exp (tailLog K0 w) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz_mem) fun w hw => (hrep w hw).2
    have hexp_an : AnalyticAt ℂ (fun w => Complex.exp (tailLog K0 w)) z :=
      ((htd.analyticOnNhd Metric.isOpen_ball) z hz_mem).cexp
    have hprod_an : AnalyticAt ℂ (fun w => ∏ k ∈ Finset.range K0, Fblk k w) z := by
      refine Finset.analyticAt_fun_prod _ fun k _ => ?_
      refine Finset.analyticAt_fun_prod _ fun g _ => ?_
      exact ((analyticAt_const.add (((analyticAt_id.sub analyticAt_const).pow 2).div analyticAt_const
        (by
          have hgt := (hB_mem k g).mp ‹_› |>.1
          have hgpos : 0 < g := lt_of_le_of_lt (Nat.cast_nonneg k) hgt
          exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hgpos.ne')))).pow _)
    rw [analyticOrderAt_congr hevP]
    change analyticOrderAt
      ((fun w => ∏ k ∈ Finset.range K0, Fblk k w) * (fun w => Complex.exp (tailLog K0 w))) z = _
    rw [analyticOrderAt_mul hprod_an hexp_an,
      hexp_an.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), add_zero]
    -- Compute order of finite product of (1 + (w - 1/2)^2 / g^2)^(mult g) at z
    have hfactor_ord : ∀ k ∈ Finset.range K0, ∀ g ∈ B k,
        analyticOrderAt (fun w : ℂ => (1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) ^ (mult g)) z =
          if z = 1 / 2 + (g : ℂ) * Complex.I ∨ z = 1 / 2 - (g : ℂ) * Complex.I then (mult g : ℕ∞) else 0 := by
      intro k _ g hg
      have hgt := (hB_mem k g).mp hg |>.1
      have hgpos : 0 < g := lt_of_le_of_lt (Nat.cast_nonneg k) hgt
      have hgne : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hgpos.ne'
      have hfac_eq : (fun w : ℂ => 1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) =
          (fun _ : ℂ => ((g : ℂ) ^ 2)⁻¹) *
            ((fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I)) *
             (fun w : ℂ => w - (1 / 2 - (g : ℂ) * Complex.I))) := by
        ext w; simp only [Pi.mul_apply]; field_simp [hgne]; ring_nf; simp [Complex.I_sq]
      have han_base : AnalyticAt ℂ (fun w : ℂ => 1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) z := by
        rw [hfac_eq]
        exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).mul
          (analyticAt_id.sub analyticAt_const))
      change analyticOrderAt ((fun w : ℂ => 1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) ^ (mult g)) z = _
      rw [analyticOrderAt_pow han_base]
      rw [hfac_eq]
      have h1 : AnalyticAt ℂ (fun _ : ℂ => ((g : ℂ) ^ 2)⁻¹) z := analyticAt_const
      have h2 : AnalyticAt ℂ (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I)) z := by fun_prop
      have h3 : AnalyticAt ℂ (fun w : ℂ => w - (1 / 2 - (g : ℂ) * Complex.I)) z := by fun_prop
      rw [analyticOrderAt_mul h1 (h2.mul h3), h1.analyticOrderAt_eq_zero.mpr (inv_ne_zero (pow_ne_zero 2 hgne)),
        zero_add, analyticOrderAt_mul h2 h3]
      have hne_pm : (1 / 2 : ℂ) + (g : ℂ) * Complex.I ≠ 1 / 2 - (g : ℂ) * Complex.I := by
        intro heq
        have := congrArg Complex.im heq
        simp at this; linarith
      have hord_lin : ∀ a : ℂ, analyticOrderAt (fun w : ℂ => w - a) a = 1 := fun a => by
        have hlin : AnalyticAt ℂ (fun w : ℂ => w - a) a := by fun_prop
        change analyticOrderAt (fun w : ℂ => w - a) a = ((1 : ℕ) : ℕ∞)
        rw [hlin.analyticOrderAt_eq_natCast]
        exact ⟨fun _ => 1, analyticAt_const, one_ne_zero,
          Filter.Eventually.of_forall fun w => by simp [smul_eq_mul]⟩
      by_cases hp : z = 1 / 2 + (g : ℂ) * Complex.I
      · subst hp
        rw [if_pos (Or.inl rfl)]
        have ho1 : analyticOrderAt (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I))
            (1 / 2 + (g : ℂ) * Complex.I) = 1 := hord_lin _
        have ho2 : analyticOrderAt (fun w : ℂ => w - (1 / 2 - (g : ℂ) * Complex.I))
            (1 / 2 + (g : ℂ) * Complex.I) = 0 :=
          h3.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hne_pm)
        rw [ho1, ho2, add_zero, nsmul_eq_mul, mul_one]
      · by_cases hm : z = 1 / 2 - (g : ℂ) * Complex.I
        · subst hm
          rw [if_pos (Or.inr rfl)]
          have ho1 : analyticOrderAt (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I))
              (1 / 2 - (g : ℂ) * Complex.I) = 0 :=
            h2.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hne_pm.symm)
          have ho2 : analyticOrderAt (fun w : ℂ => w - (1 / 2 - (g : ℂ) * Complex.I))
              (1 / 2 - (g : ℂ) * Complex.I) = 1 := hord_lin _
          rw [ho1, ho2, zero_add, nsmul_eq_mul, mul_one]
        · rw [if_neg (by tauto)]
          rw [h2.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hp),
            h3.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hm), add_zero, smul_zero]
    -- Expand analyticOrderAt of the double finite product
    have hprod_ord : analyticOrderAt (fun w => ∏ k ∈ Finset.range K0, Fblk k w) z =
        ∑ k ∈ Finset.range K0, ∑ g ∈ B k,
          if z = 1 / 2 + (g : ℂ) * Complex.I ∨ z = 1 / 2 - (g : ℂ) * Complex.I then (mult g : ℕ∞) else 0 := by
      have han_fac : ∀ k : ℕ, ∀ g ∈ B k,
          AnalyticAt ℂ (fun w : ℂ => (1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) ^ (mult g)) z := by
        intro k g hg
        have hgpos : 0 < g := lt_of_le_of_lt (Nat.cast_nonneg k) ((hB_mem k g).mp hg).1
        exact ((analyticAt_const.add (((analyticAt_id.sub analyticAt_const).pow 2).div analyticAt_const
          (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hgpos.ne')))).pow _)
      have hFblk_an : ∀ k ∈ Finset.range K0, AnalyticAt ℂ (Fblk k) z := fun k _ =>
        Finset.analyticAt_fun_prod (B k) (han_fac k)
      rw [analyticOrderAt_finset_prod_aux (Finset.range K0) Fblk z hFblk_an]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hinner := analyticOrderAt_finset_prod_aux (B k)
        (fun g w => (1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) ^ (mult g)) z (han_fac k)
      change analyticOrderAt (fun w => ∏ g ∈ B k, (1 + (w - 1 / 2) ^ 2 / (g : ℂ) ^ 2) ^ (mult g)) z = _
      rw [hinner]
      exact Finset.sum_congr rfl fun g hg => hfactor_ord k hk g hg
    rw [hprod_ord]
    -- Now compare with analyticOrderAt xi4 z by cases on whether xi4 z = 0
    by_cases hxz : xi4 z = 0
    · have hzre : z.re = 1 / 2 := by
        by_contra hne; exact hxi_nz_off z hne hxz
      have hzim_ne : z.im ≠ 0 := by
        intro h0
        have hz_half : z = 1 / 2 := Complex.ext (by simpa using hzre) (by simpa using h0)
        exact hxi_half_ne (hz_half ▸ hxz)
      let g0 : ℝ := |z.im|
      have hg0_pos : 0 < g0 := abs_pos.mpr hzim_ne
      have hg0_lt_K0 : g0 < (K0 : ℝ) := by
        have h1 : g0 = ‖z - 1 / 2‖ := by
          have : z - 1 / 2 = ((z.im : ℂ) * Complex.I) := Complex.ext (by simp [hzre]) (by simp)
          rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        dsimp [R, K0] at h2R ⊢; linarith
      have hz_eq_pm : z = 1 / 2 + (g0 : ℂ) * Complex.I ∨ z = 1 / 2 - (g0 : ℂ) * Complex.I := by
        rcases lt_or_gt_of_ne hzim_ne with him | him
        · right
          apply Complex.ext <;> simp [hzre, g0, abs_of_neg him]
        · left
          apply Complex.ext <;> simp [hzre, g0, abs_of_pos him]
      have hxi_g0 : xi4 (1 / 2 + (g0 : ℂ) * Complex.I) = 0 := by
        rcases hz_eq_pm with h | h
        · rwa [← h]
        · have hzc : starRingEnd ℂ z = 1 / 2 + (g0 : ℂ) * Complex.I := by
            rw [h]
            simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
            ring
          rw [← hzc, xi4_conj, hxz, map_zero]
      have hL_g0 : L4 (1 / 2 + (g0 : ℂ) * Complex.I) = 0 := by
        rw [L4_eq_xi4_div_gammaℝ, hxi_g0, zero_div]
      -- Find the unique k0 < K0 with g0 ∈ B k0
      let k0 : ℕ := ⌈g0⌉₊ - 1
      have hk0_lt : k0 < K0 := by
        have hceil : ⌈g0⌉₊ ≤ K0 := Nat.ceil_le.mpr hg0_lt_K0.le
        have hpos : 1 ≤ ⌈g0⌉₊ := Nat.ceil_pos.mpr hg0_pos
        omega
      have hg0_in_B : g0 ∈ B k0 := by
        rw [hB_mem]
        have hpos : 1 ≤ ⌈g0⌉₊ := Nat.ceil_pos.mpr hg0_pos
        have h1 : ((⌈g0⌉₊ - 1 : ℕ) : ℝ) < g0 := by
          have := Nat.lt_ceil.mp (show ⌈g0⌉₊ - 1 < ⌈g0⌉₊ by omega)
          exact this
        have h2 : g0 ≤ (((⌈g0⌉₊ - 1 : ℕ) : ℝ) + 1) := by
          have : ((⌈g0⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈g0⌉₊ : ℝ) := by
            have : (⌈g0⌉₊ - 1) + 1 = ⌈g0⌉₊ := Nat.sub_add_cancel hpos
            exact_mod_cast this
          rw [this]; exact Nat.le_ceil g0
        exact ⟨h1, h2, hL_g0⟩
      -- Every other (k, g) contributes 0
      have huniq : ∀ k ∈ Finset.range K0, ∀ g ∈ B k,
          (z = 1 / 2 + (g : ℂ) * Complex.I ∨ z = 1 / 2 - (g : ℂ) * Complex.I) ↔
            k = k0 ∧ g = g0 := by
        intro k _ g hg
        constructor
        · intro hor
          have hgpos : 0 < g := lt_of_le_of_lt (Nat.cast_nonneg k) ((hB_mem k g).mp hg).1
          have hgeq : g = g0 := by
            rcases hor with h | h
            · have := congrArg Complex.im h; simp at this; dsimp [g0]; rw [this, abs_of_pos hgpos]
            · have := congrArg Complex.im h; simp at this; dsimp [g0]; rw [this, abs_neg, abs_of_pos hgpos]
          subst hgeq
          have hkeq : k = k0 := by
            by_contra hkne
            exact Finset.disjoint_left.mp (hB_disj hkne) hg hg0_in_B
          exact ⟨hkeq, rfl⟩
        · rintro ⟨rfl, rfl⟩; exact hz_eq_pm
      have hsum_val : (∑ k ∈ Finset.range K0, ∑ g ∈ B k,
          if z = 1 / 2 + (g : ℂ) * Complex.I ∨ z = 1 / 2 - (g : ℂ) * Complex.I then (mult g : ℕ∞) else 0) =
          (mult g0 : ℕ∞) := by
        rw [Finset.sum_eq_single k0]
        · rw [Finset.sum_eq_single g0]
          · rw [if_pos hz_eq_pm]
          · intro g hg hgne
            rw [if_neg (fun h => hgne ((huniq k0 (Finset.mem_range.mpr hk0_lt) g hg).mp h).2)]
          · intro hnot; exact absurd hg0_in_B hnot
        · intro k hk hkne
          refine Finset.sum_eq_zero fun g hg => ?_
          rw [if_neg (fun h => hkne ((huniq k hk g hg).mp h).1)]
        · intro hnot; exact absurd (Finset.mem_range.mpr hk0_lt) hnot
      rw [hsum_val]
      have hord_g0 : (mult g0 : ℕ∞) = analyticOrderAt xi4 (1 / 2 + (g0 : ℂ) * Complex.I) := by
        dsimp [mult]
        rw [← hord_xi_eq_L g0, ENat.natCast_toNat (hord_xi_ne_top _)]
      rw [hord_g0]
      rcases hz_eq_pm with h | h
      · rw [h]
      · rw [h, hord_xi_conj]
    · -- xi4 z ≠ 0: every term in the sum is 0
      rw [(xi4_differentiable.analyticAt z).analyticOrderAt_eq_zero.mpr hxz]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun g hg => ?_
      rw [if_neg]
      rintro (rfl | rfl)
      · have hLz := ((hB_mem k g).mp hg).2.2
        rw [xi4_eq_L4_mul_gammaℝ (by simp; norm_num), hLz, zero_mul] at hxz
        exact hxz rfl
      · have hLz := ((hB_mem k g).mp hg).2.2
        have hxi_p : xi4 (1 / 2 + (g : ℂ) * Complex.I) = 0 := by
          rw [xi4_eq_L4_mul_gammaℝ (by simp; norm_num), hLz, zero_mul]
        have hzc : starRingEnd ℂ (1 / 2 + (g : ℂ) * Complex.I) = 1 / 2 - (g : ℂ) * Complex.I := by
          simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
          ring
        rw [← hzc, xi4_conj, hxi_p, map_zero] at hxz
        exact hxz rfl
  -- Step 5f: Construct nowhere-zero entire quotient Q with xi4 = P * Q and entire log h with exp h = Q
  have hP_nz_some : P (1 / 2 : ℂ) ≠ 0 := by
    intro h0
    have h1 := (hP_diff.analyticAt (1 / 2 : ℂ)).analyticOrderAt_ne_zero.mpr h0
    rw [hord_P_eq_xi, (xi4_differentiable.analyticAt (1 / 2 : ℂ)).analyticOrderAt_eq_zero.mpr hxi_half_ne] at h1
    exact h1 rfl
  have hord_P_ne_top : ∀ z, analyticOrderAt P z ≠ ⊤ := fun z => by
    rw [hord_P_eq_xi]; exact hord_xi_ne_top z
  have hQ_loc : ∀ z0 : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z0 ∈ U ∧
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧ ∀ z ∈ U, q z ≠ 0 ∧ xi4 z = P z * q z := by
    intro z0
    have hfinP := hord_P_ne_top z0
    have hfinXi := hord_xi_ne_top z0
    obtain ⟨f, hf_an, hfz, hfeq⟩ := (xi4_differentiable.analyticAt z0).analyticOrderAt_ne_top.mp hfinXi
    obtain ⟨g, hg_an, hgz, hgeq⟩ := (hP_diff.analyticAt z0).analyticOrderAt_ne_top.mp hfinP
    have hneq_ord : analyticOrderNatAt P z0 = analyticOrderNatAt xi4 z0 := by
      have h1 := Nat.cast_analyticOrderNatAt hfinP
      have h2 := Nat.cast_analyticOrderNatAt hfinXi
      rw [hord_P_eq_xi z0] at h1
      exact Nat.cast_injective (h1.trans h2.symm)
    let q : ℂ → ℂ := fun z => f z / g z
    have hq_an : AnalyticAt ℂ q z0 := hf_an.div hg_an hgz
    have hq_ev : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ q z ∧ q z ≠ 0 ∧ xi4 z = P z * q z := by
      filter_upwards [hq_an.eventually_analyticAt, hq_an.continuousAt.eventually_ne (div_ne_zero hfz hgz),
        hg_an.continuousAt.eventually_ne hgz, hfeq, hgeq] with z hqa hqnz hgnz hfz' hgz'
      refine ⟨hqa.differentiableAt, hqnz, ?_⟩
      rw [hfz', hgz', hneq_ord, smul_eq_mul, smul_eq_mul]
      dsimp [q]
      field_simp [hgnz]
    obtain ⟨U, hUsub, hUopen, hz0U⟩ := eventually_nhds_iff.mp hq_ev
    exact ⟨U, hUopen, hz0U, q, fun z hz => (hUsub z hz).1.differentiableWithinAt,
      fun z hz => ⟨(hUsub z hz).2.1, (hUsub z hz).2.2⟩⟩
  let Q : ℂ → ℂ := fun z0 => (hQ_loc z0).choose_spec.2.2.choose z0
  have hQ_eq_loc : ∀ z0 : ℂ, ∀ z ∈ (hQ_loc z0).choose,
      Q z = (hQ_loc z0).choose_spec.2.2.choose z := by
    intro z0 z hz
    let q0 := (hQ_loc z0).choose_spec.2.2.choose
    let qz := (hQ_loc z).choose_spec.2.2.choose
    have hU0 := (hQ_loc z0).choose_spec.1
    have hUz := (hQ_loc z).choose_spec.1
    have hzUz := (hQ_loc z).choose_spec.2.1
    have hq0_spec := (hQ_loc z0).choose_spec.2.2.choose_spec
    have hqz_spec := (hQ_loc z).choose_spec.2.2.choose_spec
    have hP_ev_ne : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 := by
      have hanP : AnalyticOnNhd ℂ P Set.univ := hP_diff.differentiableOn.analyticOnNhd isOpen_univ
      by_contra hnot
      have hfreq : ∃ᶠ w in 𝓝[≠] z, P w = 0 := by simpa [Filter.not_eventually] using hnot
      have h0 := hanP.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ z) hfreq (Set.mem_univ (1 / 2 : ℂ))
      exact hP_nz_some h0
    have heq_punc : ∀ᶠ w in 𝓝[≠] z, qz w = q0 w := by
      filter_upwards [nhdsWithin_le_nhds ((hU0.inter hUz).mem_nhds ⟨hz, hzUz⟩), hP_ev_ne] with w hw hPw
      have h1 := (hqz_spec.2 w hw.2).2
      have h2 := (hq0_spec.2 w hw.1).2
      exact mul_left_cancel₀ hPw (h1.symm.trans h2)
    have hc1 : ContinuousAt qz z :=
      (hqz_spec.1.differentiableAt (hUz.mem_nhds hzUz)).continuousAt
    have hc2 : ContinuousAt q0 z :=
      (hq0_spec.1.differentiableAt (hU0.mem_nhds hz)).continuousAt
    exact tendsto_nhds_unique (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' (heq_punc.mono fun _ h => h.symm))
  have hQ_diff : Differentiable ℂ Q := by
    intro z0
    have hU0 := (hQ_loc z0).choose_spec.1
    have hz0 := (hQ_loc z0).choose_spec.2.1
    have hq0_diff := (hQ_loc z0).choose_spec.2.2.choose_spec.1
    refine (hq0_diff.differentiableAt (hU0.mem_nhds hz0)).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (hU0.mem_nhds hz0) (hQ_eq_loc z0)
  have hQ_nz : ∀ z, Q z ≠ 0 := fun z =>
    ((hQ_loc z).choose_spec.2.2.choose_spec.2 z (hQ_loc z).choose_spec.2.1).1
  have hxi_eq_PQ : ∀ z, xi4 z = P z * Q z := fun z =>
    ((hQ_loc z).choose_spec.2.2.choose_spec.2 z (hQ_loc z).choose_spec.2.1).2
  obtain ⟨h, hh_diff, hh_exp⟩ := exists_entire_log hQ_diff hQ_nz
  -- Step 5g: On pigeonhole radii R ∈ [X, 2X], Re(h(1/2 + R e^{iθ})) ≤ C_tot * R * log R
  obtain ⟨Cxi, hCxipos, hCxi⟩ := norm_xi4_le_exp_R_log_R
  have hRe_h_pigeonhole : ∃ Ctot : ℝ, 0 < Ctot ∧ ∀ X : ℝ, 4 ≤ X →
      ∃ R ∈ Set.Icc X (2 * X), ∀ θ : ℝ,
        (h (1 / 2 + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re ≤
          Ctot * R * Real.log R := by
    let Bconst : ℝ := 10 * C0 * (Real.log (200 * C0) + 1)
    have hlog200_nn : 0 ≤ Real.log (200 * C0) := Real.log_nonneg (by dsimp [C0]; linarith [hw_nn 0])
    have hBconst_nn : 0 ≤ Bconst := by dsimp [Bconst]; positivity
    let Ctot : ℝ := Cxi + 16 * C0 + Bconst + 10
    refine ⟨Ctot, by positivity, fun X hX => ?_⟩
    let K_hi : ℕ := ⌈4 * X⌉₊ + 2
    let S : Finset ℝ := (Finset.range K_hi).biUnion B
    have hS_card : (S.card : ℝ) ≤ C0 * (4 * X + 4) := by
      have h1 : (S.card : ℝ) ≤ ∑ g ∈ S, (mult g : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_le_sum fun g hg => ?_
        obtain ⟨k, _, hgk⟩ := Finset.mem_biUnion.mp hg
        have hLz := ((hB_mem k g).mp hgk).2.2
        have hord_pos : 0 < mult g := by
          dsimp [mult]
          have hne0 : analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I) ≠ 0 :=
            (L4_differentiable.analyticAt _).analyticOrderAt_ne_zero.mpr hLz
          have hnetop : analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I) ≠ ⊤ := by
            rw [← hord_xi_eq_L]; exact hord_xi_ne_top _
          have hcast := ENat.natCast_toNat hnetop
          by_contra h0
          have : (analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat = 0 := by omega
          rw [this, Nat.cast_zero] at hcast
          exact hne0 hcast.symm
        exact_mod_cast hord_pos
      have h2 : ∑ g ∈ S, (mult g : ℝ) = Ncount K_hi := by
        dsimp [S, Ncount, w]
        rw [Finset.sum_biUnion (fun a _ b _ hab => hB_disj hab)]
      have h3 := hNcount_le K_hi
      have hK_le : (K_hi : ℝ) ≤ 4 * X + 3 := by
        dsimp [K_hi]; push_cast; linarith [(Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * X)).le]
      dsimp [C0] at *; nlinarith [hw_nn 0]
    obtain ⟨R, hR_Icc, hR_sep⟩ := pigeonhole_radius (by linarith : 0 < X) S
    have hRX : X ≤ R := hR_Icc.1
    have hR2X : R ≤ 2 * X := hR_Icc.2
    have hR2 : 2 ≤ R := by linarith
    have hRpos : 0 < R := by linarith
    have hlogR_ge : 1 ≤ Real.log R := by
      have hexp1 : Real.exp 1 ≤ R := by linarith [Real.exp_one_lt_d9]
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp1
    -- Separation bound: |R - g| ≥ 1 / (20 * C0) for all g ∈ S
    have hsep_const : ∀ g ∈ S, 1 / (20 * C0) ≤ |R - g| := fun g hg => by
      refine le_trans ?_ (hR_sep g hg)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hC01 : 1 ≤ C0 := by dsimp [C0]; linarith [hw_nn 0]
      nlinarith
    -- Apply hP_local on Metric.ball (1/2) (R + 1) with K0 = K_hi
    have hK0_ge : 2 * (R + 1) ≤ (K_hi : ℝ) := by
      dsimp [K_hi]; push_cast; linarith [Nat.le_ceil (4 * X)]
    have hK0_1 : 1 ≤ K_hi := by dsimp [K_hi]; omega
    obtain ⟨_, hrep⟩ := hP_local (R + 1) (by positivity) K_hi hK0_1 hK0_ge
    refine ⟨R, hR_Icc, fun θ => ?_⟩
    set z : ℂ := 1 / 2 + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hz_norm : ‖z - 1 / 2‖ = R := by
      dsimp [z]
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hRpos.le,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hz_mem : z ∈ Metric.ball (1 / 2 : ℂ) (R + 1) := by
      rw [Metric.mem_ball, dist_eq_norm, hz_norm]; linarith
    obtain ⟨htail_le, hPeq⟩ := hrep z hz_mem
    have hP_lower : Real.exp (-(16 * C0 * R + Bconst * R * Real.log R)) ≤ ‖P z‖ := by
      rw [hPeq, norm_mul, Complex.norm_exp]
      -- Lower bound the finite product ∏_{k < K_hi} |Fblk k z|
      have hfin_lower : Real.exp (-(Bconst * R * Real.log R)) ≤
          ‖∏ k ∈ Finset.range K_hi, Fblk k z‖ := by
        rw [norm_prod]
        have hprod_ge : ∀ k ∈ Finset.range K_hi,
            Real.exp (-(w k * (2 * Real.log (200 * C0 * R)))) ≤ ‖Fblk k z‖ := by
          intro k hk
          dsimp [Fblk, w]
          rw [norm_prod, Finset.sum_mul, ← Finset.sum_neg_distrib, Real.exp_sum]
          refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun g hg => ?_
          rw [norm_pow]
          have hgS : g ∈ S := Finset.mem_biUnion.mpr ⟨k, hk, hg⟩
          have hgt := (hB_mem k g).mp hg |>.1
          have hgpos : 0 < g := lt_of_le_of_lt (Nat.cast_nonneg k) hgt
          have hgle : g ≤ (K_hi : ℝ) := by
            have h1 := ((hB_mem k g).mp hg).2.1
            have h2 : k + 1 ≤ K_hi := Finset.mem_range.mp hk
            exact le_trans h1 (by exact_mod_cast h2)
          have hgle_R : g ≤ 5 * R := by
            have hK_le : (K_hi : ℝ) ≤ 4 * X + 3 := by
              dsimp [K_hi]; push_cast; linarith [(Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * X)).le]
            linarith
          have hfac_ge : (1 / (200 * C0 * R)) ^ 2 ≤ ‖1 + (z - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ := by
            have hgne : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hgpos.ne'
            have hsplit : 1 + (z - 1 / 2) ^ 2 / (g : ℂ) ^ 2 =
                (((g : ℂ) + Complex.I * (z - 1 / 2)) * ((g : ℂ) - Complex.I * (z - 1 / 2))) /
                  (g : ℂ) ^ 2 := by
              field_simp [hgne]; ring_nf; simp [Complex.I_sq]; ring
            rw [hsplit, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hgpos.le]
            have htri1 : 1 / (20 * C0) ≤ ‖(g : ℂ) + Complex.I * (z - 1 / 2)‖ := by
              have h1 := abs_norm_sub_norm_le (g : ℂ) (-(Complex.I * (z - 1 / 2)))
              rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_I, one_mul, hz_norm,
                Complex.norm_real, Real.norm_of_nonneg hgpos.le, abs_sub_comm] at h1
              exact (hsep_const g hgS).trans h1
            have htri2 : 1 / (20 * C0) ≤ ‖(g : ℂ) - Complex.I * (z - 1 / 2)‖ := by
              have h1 := abs_norm_sub_norm_le (g : ℂ) (Complex.I * (z - 1 / 2))
              rw [norm_mul, Complex.norm_I, one_mul, hz_norm,
                Complex.norm_real, Real.norm_of_nonneg hgpos.le, abs_sub_comm] at h1
              exact (hsep_const g hgS).trans h1
            have hnum : (1 / (20 * C0)) ^ 2 ≤
                ‖(g : ℂ) + Complex.I * (z - 1 / 2)‖ * ‖(g : ℂ) - Complex.I * (z - 1 / 2)‖ := by
              rw [sq]; exact mul_le_mul htri1 htri2 (by positivity) (norm_nonneg _)
            have hden : g ^ 2 ≤ (5 * R) ^ 2 := pow_le_pow_left₀ hgpos.le hgle_R 2
            calc
              (1 / (200 * C0 * R)) ^ 2 ≤ (1 / (20 * C0)) ^ 2 / (5 * R) ^ 2 := by
                rw [div_pow, div_pow, one_pow, div_div]
                refine one_div_le_one_div_of_le (by positivity) ?_
                nlinarith [sq_nonneg (C0 * R)]
              _ ≤ (‖(g : ℂ) + Complex.I * (z - 1 / 2)‖ * ‖(g : ℂ) - Complex.I * (z - 1 / 2)‖) / g ^ 2 :=
                div_le_div₀ (by positivity) hnum (sq_pos_of_pos hgpos) hden
          have hexp_eq : Real.exp (-((mult g : ℝ) * (2 * Real.log (200 * C0 * R)))) =
              ((1 / (200 * C0 * R)) ^ 2) ^ (mult g) := by
            have hpos : 0 < 200 * C0 * R := by positivity
            rw [show -((mult g : ℝ) * (2 * Real.log (200 * C0 * R))) =
                (mult g : ℝ) * ((-Real.log (200 * C0 * R)) * 2) by ring,
              Real.exp_nat_mul, Real.exp_mul, Real.exp_neg, Real.exp_log hpos,
              one_div, Real.rpow_two]
          rw [hexp_eq]
          exact pow_le_pow_left₀ (by positivity) hfac_ge (mult g)
        have hprod_all := Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) hprod_ge
        rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_mul] at hprod_all
        refine le_trans (Real.exp_le_exp.mpr ?_) hprod_all
        have hN_hi : ∑ k ∈ Finset.range K_hi, w k ≤ C0 * (5 * R) := by
          have h1 := hNcount_le K_hi
          have hK_le : (K_hi : ℝ) ≤ 4 * X + 3 := by
            dsimp [K_hi]; push_cast; linarith [(Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * X)).le]
          dsimp [Ncount, C0] at *; nlinarith [hw_nn 0]
        have hlog_le : Real.log (200 * C0 * R) ≤ (Real.log (200 * C0) + 1) * Real.log R := by
          rw [Real.log_mul (by positivity) hRpos.ne']
          nlinarith
        have hsum_nn : 0 ≤ ∑ k ∈ Finset.range K_hi, w k := Finset.sum_nonneg fun k _ => hw_nn k
        have hlog_pos : 0 ≤ 2 * Real.log (200 * C0 * R) := by
          have : 1 ≤ 200 * C0 * R := by dsimp [C0]; nlinarith [hw_nn 0]
          linarith [Real.log_nonneg this]
        have hmul_le : (∑ k ∈ Finset.range K_hi, w k) * (2 * Real.log (200 * C0 * R)) ≤
            Bconst * R * Real.log R := by
          calc
            (∑ k ∈ Finset.range K_hi, w k) * (2 * Real.log (200 * C0 * R))
                ≤ (C0 * (5 * R)) * (2 * ((Real.log (200 * C0) + 1) * Real.log R)) :=
                  mul_le_mul hN_hi (by linarith) hlog_pos (by positivity)
            _ = Bconst * R * Real.log R := by dsimp [Bconst]; ring
        linarith
      have htail_ge : Real.exp (-(16 * C0 * R)) ≤ Real.exp (tailLog K_hi z).re := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : -(tailLog K_hi z).re ≤ ‖tailLog K_hi z‖ := by
          have := (abs_le.mp (Complex.abs_re_le_norm (tailLog K_hi z))).1; linarith
        have h2 : 8 * C0 * (R + 1) ^ 2 / (K_hi : ℝ) ≤ 16 * C0 * R := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (K_hi : ℝ))]
          have hstep1 : 8 * (R + 1) ^ 2 ≤ 16 * R * (K_hi : ℝ) := by nlinarith [hK0_ge, hR2]
          calc
            8 * C0 * (R + 1) ^ 2 = C0 * (8 * (R + 1) ^ 2) := by ring
            _ ≤ C0 * (16 * R * (K_hi : ℝ)) := mul_le_mul_of_nonneg_left hstep1 hC0pos.le
            _ = 16 * C0 * R * (K_hi : ℝ) := by ring
        linarith
      calc
        Real.exp (-(16 * C0 * R + Bconst * R * Real.log R))
            = Real.exp (-(Bconst * R * Real.log R)) * Real.exp (-(16 * C0 * R)) := by
              rw [← Real.exp_add]; congr 1; ring
        _ ≤ ‖∏ k ∈ Finset.range K_hi, Fblk k z‖ * Real.exp (tailLog K_hi z).re :=
              mul_le_mul hfin_lower htail_ge (Real.exp_pos _).le (norm_nonneg _)
    -- Now combine ‖xi4 z‖ = ‖P z‖ * exp(Re(h z))
    have hnorm_eq : ‖xi4 z‖ = ‖P z‖ * Real.exp (h z).re := by
      rw [hxi_eq_PQ z, ← hh_exp z, norm_mul, Complex.norm_exp]
    have hxi_up := hCxi z (by rw [hz_norm]; exact hR2)
    rw [hz_norm] at hxi_up
    have hexp_le : Real.exp (h z).re ≤ Real.exp (Ctot * R * Real.log R) := by
      have h1 : Real.exp (-(16 * C0 * R + Bconst * R * Real.log R)) *
          Real.exp (h z).re ≤ Real.exp (Cxi * R * Real.log R) := by
        calc
          _ ≤ ‖P z‖ * Real.exp (h z).re := mul_le_mul_of_nonneg_right hP_lower (Real.exp_pos _).le
          _ = ‖xi4 z‖ := hnorm_eq.symm
          _ ≤ Real.exp (Cxi * R * Real.log R) := hxi_up
      rw [← Real.exp_add, Real.exp_le_exp] at h1
      refine Real.exp_le_exp.mpr ?_
      dsimp [Ctot]
      nlinarith [mul_le_mul_of_nonneg_left hlogR_ge (by positivity : 0 ≤ 16 * C0 * R)]
    exact Real.exp_le_exp.mp hexp_le
  -- Step 5h: Therefore iteratedDeriv n h (1/2) = 0 for all n ≥ 2, so h is linear!
  obtain ⟨Ctot, hCtot_pos, hCtot⟩ := hRe_h_pigeonhole
  have hderiv_zero : ∀ n : ℕ, 2 ≤ n → iteratedDeriv n h (1 / 2 : ℂ) = 0 := by
    intro n hn
    by_contra hne
    have hpos : 0 < ‖(n ! : ℂ)⁻¹ * iteratedDeriv n h (1 / 2 : ℂ)‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_pos (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos n)) (norm_pos_iff.mpr hne)
    let c := ‖(n ! : ℂ)⁻¹ * iteratedDeriv n h (1 / 2 : ℂ)‖
    let X : ℝ := max 4 ((8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) / c) ^ 2 + 4
    have hX4 : 4 ≤ X := by
      dsimp [X]
      linarith [sq_nonneg (max 4 ((8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) / c))]
    obtain ⟨R, hR_Icc, hRM⟩ := hCtot X hX4
    have hRX : X ≤ R := hR_Icc.1
    have hRpos : 0 < R := by linarith
    have hR1 : 1 ≤ R := by linarith
    have hcb := norm_taylor_coeff_le_of_re_le hh_diff (1 / 2 : ℂ) hRpos hRM n (by omega)
    have hRn : R ^ 2 ≤ R ^ n := by
      have : R ^ 2 * 1 ≤ R ^ 2 * R ^ (n - 2) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hR1) (sq_nonneg R)
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hn] at this
      exact this
    have hlog_le_sqrt : Real.log R ≤ 2 * Real.sqrt R := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hRpos)
      rw [Real.log_sqrt hRpos.le] at h1
      linarith
    have hsqrt_ge : (8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) / c ≤ Real.sqrt R := by
      have hsq : ((8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) / c) ^ 2 ≤ R := by
        have h1 : ((8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) / c) ^ 2 ≤
            (max 4 ((8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) / c)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2
        dsimp [X] at hRX; linarith
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity)] at this
    have hlt_contra : 2 * (Ctot * R * Real.log R - (h (1 / 2 : ℂ)).re) < c * R ^ 2 := by
      have hre_le : -(h (1 / 2 : ℂ)).re ≤ |(h (1 / 2 : ℂ)).re| := neg_le_abs _
      have hR_sqrt : R = Real.sqrt R * Real.sqrt R := (Real.mul_self_sqrt hRpos.le).symm
      have hsqrt_pos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
      have hsqrt_ge1 : 1 ≤ Real.sqrt R := by
        simpa [Real.sqrt_one] using Real.sqrt_le_sqrt hR1
      have hcR : 8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4 ≤ c * Real.sqrt R := by
        have h1 := (div_le_iff₀ hpos).mp hsqrt_ge
        dsimp [c] at *; linarith
      have h1 : 2 * Ctot * R * Real.log R ≤ 4 * Ctot * R * Real.sqrt R := by
        nlinarith [mul_le_mul_of_nonneg_left hlog_le_sqrt (by positivity : 0 ≤ 2 * Ctot * R)]
      have h2 : 2 * |(h (1 / 2 : ℂ)).re| ≤ 2 * |(h (1 / 2 : ℂ)).re| * R * Real.sqrt R := by
        have : 1 ≤ R * Real.sqrt R := by nlinarith
        nlinarith [abs_nonneg (h (1 / 2 : ℂ)).re]
      have h3 : (8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) * R * Real.sqrt R ≤ c * R ^ 2 := by
        calc
          (8 * Ctot + 4 * |(h (1 / 2 : ℂ)).re| + 4) * R * Real.sqrt R
              ≤ (c * Real.sqrt R) * R * Real.sqrt R := by
                nlinarith [mul_le_mul_of_nonneg_right hcR (by positivity : 0 ≤ R * Real.sqrt R)]
          _ = c * R * (Real.sqrt R * Real.sqrt R) := by ring
          _ = c * R ^ 2 := by rw [← hR_sqrt]; ring
      nlinarith [mul_pos hRpos hsqrt_pos]
    have hge : c * R ^ 2 ≤ c * R ^ n := mul_le_mul_of_nonneg_left hRn hpos.le
    dsimp [c] at hlt_contra hge
    linarith
  have hh_linear : ∀ z : ℂ, h z = h (1 / 2 : ℂ) + deriv h (1 / 2 : ℂ) * (z - 1 / 2) := by
    intro z
    rw [← Complex.taylorSeries_eq_of_entire hh_diff (1 / 2 : ℂ) z]
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul]; ring
    · intro k hk
      have hk2 : 2 ≤ k := by simp only [Finset.mem_range, not_lt] at hk; exact hk
      rw [hderiv_zero k hk2, smul_zero, smul_zero]
  -- Step 5i: Exponential upper bound on ‖P(4m + 1)‖ and ‖xi4(4m + 1)‖ contradicts (2m)!
  have hP_exp_bound : ∃ Cp : ℝ, 0 < Cp ∧ ∀ m : ℕ, 1 ≤ m →
      ‖P ((4 * m + 1 : ℕ) : ℂ)‖ ≤ Real.exp (Cp * (m : ℝ)) := by
    have hB0_min : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ g ∈ B 0, δ0 ≤ g := by
      by_cases hne : (B 0).Nonempty
      · refine ⟨min 1 ((B 0).inf' hne id), lt_min zero_lt_one ?_, min_le_left _ _,
          fun g hg => le_trans (min_le_right _ _) (Finset.inf'_le id hg)⟩
        rw [Finset.lt_inf'_iff]
        intro g hg
        simpa using ((hB_mem 0 g).mp hg).1
      · refine ⟨1, zero_lt_one, le_rfl, fun g hg => absurd ⟨g, hg⟩ hne⟩
    obtain ⟨δ0, hδ0pos, _, hδ0⟩ := hB0_min
    let Cp : ℝ := 240 * C0 + 10 * w 0 / δ0 + 10
    refine ⟨Cp, by have := hw_nn 0; positivity, fun m hm => ?_⟩
    set s : ℂ := ((4 * m + 1 : ℕ) : ℂ)
    set r : ℝ := 4 * (m : ℝ) + 1 / 2
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hrpos : 0 < r := by dsimp [r]; linarith
    have hr_le : r ≤ 5 * (m : ℝ) := by dsimp [r]; linarith
    have hs_norm : ‖s - 1 / 2‖ = r := by
      have : s - 1 / 2 = (r : ℂ) := by dsimp [s, r]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
    let K0 : ℕ := ⌈2 * (r + 1)⌉₊ + 2
    have hK0_2 : 2 ≤ K0 := by dsimp [K0]; omega
    have hK0_1 : 1 ≤ K0 := by omega
    have hK0_ge : 2 * (r + 1) ≤ (K0 : ℝ) := by
      dsimp [K0]; push_cast; linarith [Nat.le_ceil (2 * (r + 1))]
    have hK0_le : (K0 : ℝ) ≤ 16 * (m : ℝ) := by
      dsimp [K0]; push_cast
      linarith [(Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * (r + 1))).le]
    obtain ⟨_, hrep⟩ := hP_local (r + 1) (by linarith) K0 hK0_1 hK0_ge
    have hs_mem : s ∈ Metric.ball (1 / 2 : ℂ) (r + 1) := by
      rw [Metric.mem_ball, dist_eq_norm, hs_norm]; linarith
    obtain ⟨htail_le, hPeq⟩ := hrep s hs_mem
    rw [hPeq, norm_mul, Complex.norm_exp, norm_prod]
    -- Bound tail
    have htail_up : (tailLog K0 s).re ≤ 24 * C0 * (m : ℝ) := by
      have h1 : (tailLog K0 s).re ≤ ‖tailLog K0 s‖ := Complex.re_le_norm _
      have h2 : 8 * C0 * (r + 1) ^ 2 / (K0 : ℝ) ≤ 4 * C0 * (r + 1) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (K0 : ℝ))]
        have hstep1 : 8 * (r + 1) ^ 2 ≤ 4 * (r + 1) * (K0 : ℝ) := by nlinarith [hK0_ge, hrpos]
        calc
          8 * C0 * (r + 1) ^ 2 = C0 * (8 * (r + 1) ^ 2) := by ring
          _ ≤ C0 * (4 * (r + 1) * (K0 : ℝ)) := mul_le_mul_of_nonneg_left hstep1 hC0pos.le
          _ = 4 * C0 * (r + 1) * (K0 : ℝ) := by ring
      nlinarith [hC0pos]
    -- Split finite product into k = 0 and 1 ≤ k < K0
    rw [Finset.prod_range_eq_mul_Ico _ hK0_1]
    -- Bound k = 0 block
    have hblk0 : ‖Fblk 0 s‖ ≤ Real.exp (10 * w 0 / δ0 * (m : ℝ)) := by
      dsimp [Fblk, w]
      rw [norm_prod]
      have hsum_eq : 10 * (∑ g ∈ B 0, (mult g : ℝ)) / δ0 * (m : ℝ) =
          ∑ g ∈ B 0, (mult g : ℝ) * (10 * (m : ℝ) / δ0) := by
        rw [← Finset.sum_mul]; ring
      rw [hsum_eq, Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun g hg => ?_
      rw [norm_pow]
      have hgpos : 0 < g := lt_of_lt_of_le hδ0pos (hδ0 g hg)
      have h1 : ‖1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ ≤ 1 + (r / δ0) ^ 2 := by
        calc
          ‖1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖
              ≤ ‖(1 : ℂ)‖ + ‖(s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ := norm_add_le _ _
          _ = 1 + r ^ 2 / g ^ 2 := by
                rw [norm_one, norm_div, norm_pow, norm_pow, hs_norm, Complex.norm_real,
                  Real.norm_of_nonneg hgpos.le]
          _ ≤ 1 + r ^ 2 / δ0 ^ 2 := by
                gcongr; exact hδ0 g hg
          _ = 1 + (r / δ0) ^ 2 := by rw [div_pow]
      have h2 : 1 + (r / δ0) ^ 2 ≤ Real.exp (10 * (m : ℝ) / δ0) := by
        have hsq : 1 + (r / δ0) ^ 2 ≤ (1 + r / δ0) ^ 2 := by nlinarith [div_nonneg hrpos.le hδ0pos.le]
        have hexp1 : 1 + r / δ0 ≤ Real.exp (r / δ0) := by linarith [Real.add_one_le_exp (r / δ0)]
        have hexp2 : (1 + r / δ0) ^ 2 ≤ Real.exp (2 * (r / δ0)) := by
          rw [show 2 * (r / δ0) = r / δ0 + r / δ0 by ring, Real.exp_add, ← sq]
          exact pow_le_pow_left₀ (by positivity) hexp1 2
        have h3 : 2 * (r / δ0) ≤ 10 * (m : ℝ) / δ0 := by
          rw [show 2 * (r / δ0) = (2 * r) / δ0 by ring]
          exact div_le_div_of_nonneg_right (by linarith) hδ0pos.le
        exact hsq.trans (hexp2.trans (Real.exp_le_exp.mpr h3))
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) (mult g)
    -- Bound 1 ≤ k < K0 blocks by summation by parts
    let fl : ℕ → ℝ := fun k => Real.log (1 + r ^ 2 / (k : ℝ) ^ 2)
    have hfl_nn : ∀ k : ℕ, 0 ≤ fl k := fun k =>
      Real.log_nonneg (by linarith [div_nonneg (sq_nonneg r) (sq_nonneg (k : ℝ))])
    have hblk_pos : ∏ k ∈ Finset.Ico 1 K0, ‖Fblk k s‖ ≤
        Real.exp (∑ k ∈ Finset.Ico 1 K0, w k * fl k) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      dsimp [Fblk, w]
      rw [norm_prod, Finset.sum_mul, Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun g hg => ?_
      rw [norm_pow, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 1 + r ^ 2 / (k : ℝ) ^ 2)]
      have hgt : (k : ℝ) < g := ((hB_mem k g).mp hg).1
      have hgpos : 0 < g := hkpos.trans hgt
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ (mult g)
      calc
        ‖1 + (s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖
            ≤ ‖(1 : ℂ)‖ + ‖(s - 1 / 2) ^ 2 / (g : ℂ) ^ 2‖ := norm_add_le _ _
        _ = 1 + r ^ 2 / g ^ 2 := by
              rw [norm_one, norm_div, norm_pow, norm_pow, hs_norm, Complex.norm_real,
                Real.norm_of_nonneg hgpos.le]
        _ ≤ 1 + r ^ 2 / (k : ℝ) ^ 2 := by
              gcongr
    have hsum_fl : ∑ k ∈ Finset.Ico 1 K0, w k * fl k ≤ 180 * C0 * (m : ℝ) := by
      let M : ℕ := K0 - 2
      have hK0_eq : K0 = M + 2 := by dsimp [M]; omega
      have hstep : ∀ k : ℕ, w k = Ncount (k + 1) - Ncount k := fun k => by
        dsimp [Ncount]; rw [Finset.sum_range_succ]; ring
      have hsbp : ∀ M' : ℕ, ∑ k ∈ Finset.Ico 1 (M' + 2), w k * fl k =
          Ncount (M' + 2) * fl (M' + 1) - Ncount 1 * fl 1 +
          ∑ k ∈ Finset.Ico 1 (M' + 1), Ncount (k + 1) * (fl k - fl (k + 1)) := by
        intro M'
        induction M' with
        | zero =>
          simp only [zero_add, Finset.Ico_self, Finset.sum_empty, add_zero,
            Finset.sum_Ico_succ_top (le_refl 1), hstep 1]
          ring
        | succ d ih =>
          have h1 : ∑ k ∈ Finset.Ico 1 (d + 1 + 2), w k * fl k =
              (∑ k ∈ Finset.Ico 1 (d + 2), w k * fl k) + w (d + 2) * fl (d + 2) := by
            rw [show d + 1 + 2 = (d + 2) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
          have h2 : ∑ k ∈ Finset.Ico 1 (d + 1 + 1), Ncount (k + 1) * (fl k - fl (k + 1)) =
              (∑ k ∈ Finset.Ico 1 (d + 1), Ncount (k + 1) * (fl k - fl (k + 1))) +
                Ncount (d + 2) * (fl (d + 1) - fl (d + 2)) := by
            rw [show d + 1 + 1 = (d + 1) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
          rw [h1, h2, ih, hstep (d + 2)]
          ring
      rw [hK0_eq, hsbp M]
      have hN1_nn : 0 ≤ Ncount 1 * fl 1 :=
        mul_nonneg (Finset.sum_nonneg fun _ _ => hw_nn _) (hfl_nn 1)
      have htop : Ncount (M + 2) * fl (M + 1) ≤ 17 * C0 * (m : ℝ) := by
        have hfl_top : fl (M + 1) ≤ 1 := by
          dsimp [fl]
          have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + r ^ 2 / ((M + 1 : ℕ) : ℝ) ^ 2)
          have hM1 : r ≤ ((M + 1 : ℕ) : ℝ) := by
            have : (K0 : ℝ) - 1 = ((M + 1 : ℕ) : ℝ) := by
              have : M + 1 + 1 = K0 := by dsimp [M]; omega
              have hcast : ((M + 1 : ℕ) : ℝ) + 1 = (K0 : ℝ) := by exact_mod_cast this
              linarith
            linarith
          have hdiv : r ^ 2 / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact pow_le_pow_left₀ hrpos.le hM1 2
          linarith
        have hN_top : Ncount (M + 2) ≤ 17 * C0 * (m : ℝ) := by
          rw [← hK0_eq]
          have h1 := hNcount_le K0
          dsimp [C0] at *; nlinarith [hw_nn 0]
        calc
          Ncount (M + 2) * fl (M + 1) ≤ (17 * C0 * (m : ℝ)) * 1 :=
            mul_le_mul hN_top hfl_top (hfl_nn _) (by positivity)
          _ = 17 * C0 * (m : ℝ) := mul_one _
      have hdiff_sum : ∑ k ∈ Finset.Ico 1 (M + 1), Ncount (k + 1) * (fl k - fl (k + 1)) ≤
          128 * C0 * (m : ℝ) := by
        have hterm_le : ∀ k ∈ Finset.Ico 1 (M + 1),
            Ncount (k + 1) * (fl k - fl (k + 1)) ≤ 8 * C0 := by
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
          set x : ℝ := (k : ℝ)
          have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hk1
          have hxpos : 0 < x := by linarith
          have hN_k : Ncount (k + 1) ≤ C0 * (x + 1) := by
            have h1 := hNcount_le (k + 1)
            dsimp [C0, x] at *; push_cast at h1 ⊢; nlinarith [hw_nn 0]
          have hcast : ((k + 1 : ℕ) : ℝ) = x + 1 := by dsimp [x]; push_cast; ring
          have hfl_diff : fl k - fl (k + 1) ≤
              r ^ 2 * (2 * x + 1) / (x ^ 2 * ((x + 1) ^ 2 + r ^ 2)) := by
            dsimp [fl]
            rw [hcast, ← Real.log_div (by positivity) (by positivity)]
            have hratio : (1 + r ^ 2 / x ^ 2) / (1 + r ^ 2 / (x + 1) ^ 2) =
                1 + r ^ 2 * (2 * x + 1) / (x ^ 2 * ((x + 1) ^ 2 + r ^ 2)) := by
              have h1 : (x : ℝ) ≠ 0 := hxpos.ne'
              have h2 : x + 1 ≠ 0 := by linarith
              have h3 : (x + 1) ^ 2 + r ^ 2 ≠ 0 := by positivity
              field_simp [h1, h2, h3]; ring
            rw [hratio]
            linarith [Real.log_le_sub_one_of_pos
              (by positivity : 0 < 1 + r ^ 2 * (2 * x + 1) / (x ^ 2 * ((x + 1) ^ 2 + r ^ 2)))]
          have hfl_nn_diff : 0 ≤ fl k - fl (k + 1) := by
            dsimp [fl]; rw [sub_nonneg]
            refine Real.log_le_log (by positivity) ?_
            gcongr; exact_mod_cast Nat.le_succ k
          calc
            Ncount (k + 1) * (fl k - fl (k + 1))
                ≤ (C0 * (x + 1)) * (r ^ 2 * (2 * x + 1) / (x ^ 2 * ((x + 1) ^ 2 + r ^ 2))) :=
                  mul_le_mul hN_k hfl_diff hfl_nn_diff (by positivity)
            _ ≤ 8 * C0 := by
                  rw [mul_div_assoc', div_le_iff₀ (by positivity : 0 < x ^ 2 * ((x + 1) ^ 2 + r ^ 2))]
                  have h1 : 2 * x + 1 ≤ 2 * (x + 1) := by linarith
                  have h2 : (x + 1) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
                  have h3 : (x + 1) * (2 * x + 1) ≤ 8 * x ^ 2 := by nlinarith
                  have h4 : r ^ 2 ≤ (x + 1) ^ 2 + r ^ 2 := by linarith [sq_nonneg (x + 1)]
                  nlinarith [mul_le_mul h3 h4 (sq_nonneg r) (by positivity)]
        calc
          ∑ k ∈ Finset.Ico 1 (M + 1), Ncount (k + 1) * (fl k - fl (k + 1))
              ≤ ∑ _k ∈ Finset.Ico 1 (M + 1), (8 * C0) := Finset.sum_le_sum hterm_le
          _ = ((Finset.Ico 1 (M + 1)).card : ℝ) * (8 * C0) := by simp
          _ ≤ (K0 : ℝ) * (8 * C0) := by
                have hc : (Finset.Ico 1 (M + 1)).card ≤ K0 := by simp; omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
          _ ≤ (16 * (m : ℝ)) * (8 * C0) := mul_le_mul_of_nonneg_right hK0_le (by positivity)
          _ = 128 * C0 * (m : ℝ) := by ring
      have hCm_nn : 0 ≤ C0 * (m : ℝ) := by positivity
      linarith
    have hprod_tot : ‖Fblk 0 s‖ * (∏ k ∈ Finset.Ico 1 K0, ‖Fblk k s‖) * Real.exp (tailLog K0 s).re ≤
        Real.exp (Cp * (m : ℝ)) := by
      calc
        ‖Fblk 0 s‖ * (∏ k ∈ Finset.Ico 1 K0, ‖Fblk k s‖) * Real.exp (tailLog K0 s).re
            ≤ Real.exp (10 * w 0 / δ0 * (m : ℝ)) * Real.exp (180 * C0 * (m : ℝ)) *
                Real.exp (24 * C0 * (m : ℝ)) := by
              refine mul_le_mul
                (mul_le_mul hblk0 (hblk_pos.trans (Real.exp_le_exp.mpr hsum_fl))
                  (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Real.exp_pos _).le)
                (Real.exp_le_exp.mpr htail_up) (Real.exp_pos _).le (by positivity)
        _ = Real.exp ((10 * w 0 / δ0 + 204 * C0) * (m : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (Cp * (m : ℝ)) := by
              refine Real.exp_le_exp.mpr ?_
              dsimp [Cp]; nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
    exact hprod_tot
  obtain ⟨Cp, hCppos, hCp⟩ := hP_exp_bound
  -- Combine with linear h(z) to get ‖xi4(4m+1)‖ ≤ exp(C_all * m)
  let Call : ℝ := Cp + |(h (1 / 2 : ℂ)).re| + 5 * ‖deriv h (1 / 2 : ℂ)‖ + 1
  have hCallpos : 0 < Call := by positivity
  have hxi_exp : ∀ m : ℕ, 1 ≤ m → ‖xi4 ((4 * m + 1 : ℕ) : ℂ)‖ ≤ Real.exp (Call * (m : ℝ)) := by
    intro m hm
    rw [hxi_eq_PQ, ← hh_exp, norm_mul, Complex.norm_exp, hh_linear]
    have hhm : (h (1 / 2 : ℂ) + deriv h (1 / 2 : ℂ) * (((4 * m + 1 : ℕ) : ℂ) - 1 / 2)).re ≤
        (|(h (1 / 2 : ℂ)).re| + 5 * ‖deriv h (1 / 2 : ℂ)‖) * (m : ℝ) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h1 : (h (1 / 2 : ℂ)).re ≤ |(h (1 / 2 : ℂ)).re| * (m : ℝ) :=
        le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hm1)
      have h2 : (deriv h (1 / 2 : ℂ) * (((4 * m + 1 : ℕ) : ℂ) - 1 / 2)).re ≤
          5 * ‖deriv h (1 / 2 : ℂ)‖ * (m : ℝ) := by
        refine (Complex.re_le_norm _).trans ?_
        rw [norm_mul]
        have h3 : ‖((4 * m + 1 : ℕ) : ℂ) - 1 / 2‖ ≤ 5 * (m : ℝ) := by
          have : ((4 * m + 1 : ℕ) : ℂ) - 1 / 2 = ((4 * (m : ℝ) + 1 / 2 : ℝ) : ℂ) := by
            push_cast; ring
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          linarith
        calc
          ‖deriv h (1 / 2 : ℂ)‖ * ‖((4 * m + 1 : ℕ) : ℂ) - 1 / 2‖
              ≤ ‖deriv h (1 / 2 : ℂ)‖ * (5 * (m : ℝ)) :=
                mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
          _ = 5 * ‖deriv h (1 / 2 : ℂ)‖ * (m : ℝ) := by ring
      rw [Complex.add_re]
      linarith
    calc
      ‖P ((4 * m + 1 : ℕ) : ℂ)‖ *
          Real.exp (h (1 / 2 : ℂ) + deriv h (1 / 2 : ℂ) * (((4 * m + 1 : ℕ) : ℂ) - 1 / 2)).re
          ≤ Real.exp (Cp * (m : ℝ)) *
              Real.exp ((|(h (1 / 2 : ℂ)).re| + 5 * ‖deriv h (1 / 2 : ℂ)‖) * (m : ℝ)) :=
            mul_le_mul (hCp m hm) (Real.exp_le_exp.mpr hhm) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((Cp + |(h (1 / 2 : ℂ)).re| + 5 * ‖deriv h (1 / 2 : ℂ)‖) * (m : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (Call * (m : ℝ)) := by
            refine Real.exp_le_exp.mpr ?_
            dsimp [Call]; nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  -- Pick m large enough that (1/2) * π^{-(2m+1)} * m^m > exp(Call * m)
  let m0 : ℕ := ⌈2 * Real.pi ^ 3 * Real.exp Call⌉₊ + 2
  have hm0 : 1 ≤ m0 := by dsimp [m0]; omega
  have hlo := xi4_real_lower_bound m0 hm0
  have hhi := hxi_exp m0 hm0
  have hm0_ge : 2 * Real.pi ^ 3 * Real.exp Call ≤ (m0 : ℝ) := by
    dsimp [m0]; push_cast
    linarith [Nat.le_ceil (2 * Real.pi ^ 3 * Real.exp Call)]
  have hcontra_num : Real.exp (Call * (m0 : ℝ)) <
      (1 / 2 : ℝ) * Real.pi ^ (-(2 * m0 + 1 : ℤ)) * (m0 : ℝ) ^ m0 := by
    have hpi_gt1 : 1 < Real.pi := by linarith [Real.pi_gt_three]
    have hpow_gt : (2 * Real.pi ^ 3 * Real.exp Call) ^ m0 ≤ (m0 : ℝ) ^ m0 :=
      pow_le_pow_left₀ (by positivity) hm0_ge m0
    have hlhs_eq : Real.exp (Call * (m0 : ℝ)) = (Real.exp Call) ^ m0 := by
      rw [mul_comm, Real.exp_nat_mul]
    have hpi_pow : Real.pi ^ (-(2 * m0 + 1 : ℤ)) * (Real.pi ^ 3) ^ m0 = Real.pi ^ (m0 - 1 : ℕ) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ Real.pi_pos.ne']
      congr 1; omega
    have h2m : (2 : ℝ) ≤ (2 : ℝ) ^ m0 := by
      have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m0 := pow_le_pow_right₀ (by norm_num) hm0
      simpa using this
    have hpi_m1 : 1 ≤ Real.pi ^ (m0 - 1 : ℕ) := one_le_pow₀ hpi_gt1.le
    have hstrict : (Real.exp Call) ^ m0 <
        (1 / 2 : ℝ) * Real.pi ^ (-(2 * m0 + 1 : ℤ)) * (2 * Real.pi ^ 3 * Real.exp Call) ^ m0 := by
      rw [mul_pow, mul_pow]
      have hrew : (1 / 2 : ℝ) * Real.pi ^ (-(2 * m0 + 1 : ℤ)) *
            ((2 : ℝ) ^ m0 * (Real.pi ^ 3) ^ m0 * (Real.exp Call) ^ m0) =
          ((1 / 2 : ℝ) * (2 : ℝ) ^ m0 * Real.pi ^ (m0 - 1 : ℕ)) * (Real.exp Call) ^ m0 := by
        rw [← hpi_pow]; ring
      rw [hrew]
      have hcoef : 1 < (1 / 2 : ℝ) * (2 : ℝ) ^ m0 * Real.pi ^ (m0 - 1 : ℕ) := by
        have h2m2 : (4 : ℝ) ≤ (2 : ℝ) ^ m0 := by
          have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ m0 := pow_le_pow_right₀ (by norm_num) (by dsimp [m0]; omega)
          norm_num at this; exact this
        nlinarith
      nlinarith [pow_pos (Real.exp_pos Call) m0]
    rw [hlhs_eq]
    exact lt_of_lt_of_le hstrict (mul_le_mul_of_nonneg_left hpow_gt (by positivity))
  linarith


/- ### Part B2: Uniform upper bound on ∑ m(g) / (1/4 + g^2) -/

private lemma integral_circle_entire {h : ℂ → ℂ} (hh : Differentiable ℂ h) (c : ℂ)
    {R : ℝ} (hR : 0 < R) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      (2 * Real.pi : ℂ) * h c := by
  let a : ℕ → ℂ := fun k => (k ! : ℂ)⁻¹ * iteratedDeriv k h c
  have hsumR : Summable (fun k : ℕ => ‖a k‖ * R ^ k) := by
    have h2R : Summable (fun k : ℕ => ‖a k * ((2 * R : ℝ) : ℂ) ^ k‖) := by
      have hts2 := (Complex.hasSum_taylorSeries_of_entire hh c (c + ((4 * R : ℝ) : ℂ))).summable
      have hts2' : Summable (fun k : ℕ => a k * ((4 * R : ℝ) : ℂ) ^ k) := by
        refine hts2.congr fun k => ?_
        simp [a, smul_eq_mul]; ring
      have htend : Tendsto (fun k : ℕ => ‖a k * ((4 * R : ℝ) : ℂ) ^ k‖) atTop (𝓝 0) := by
        have h := (Nat.cofinite_eq_atTop ▸ hts2'.tendsto_cofinite_zero).norm
        simpa only [norm_zero] using h
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend) 1 zero_lt_one
      let b : ℕ → ℝ := fun k => ‖a k‖ * (4 * R) ^ k
      have hne_rng : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
      let B : ℝ := max 1 ((Finset.range (N + 1)).sup' hne_rng b)
      have hB : ∀ k : ℕ, ‖a k‖ * (4 * R) ^ k ≤ B := fun k => by
        by_cases hk : k < N + 1
        · exact le_trans (Finset.le_sup' b (Finset.mem_range.mpr hk)) (le_max_right _ _)
        · have h1 := hN k (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
          have h2 : ‖a k‖ * (4 * R) ^ k = ‖a k * ((4 * R : ℝ) : ℂ) ^ k‖ := by
            symm; rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          rw [h2]; exact le_trans h1.le (le_max_left _ _)
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left B)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hpow : (2 * R) ^ k = (4 * R) ^ k * (1 / 2 : ℝ) ^ k := by
        rw [← mul_pow]; congr 1; ring
      rw [hpow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hB k) (by positivity)
    refine h2R.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    have hrhs : ‖a k * ((2 * R : ℝ) : ℂ) ^ k‖ = ‖a k‖ * (2 * R) ^ k := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le (by linarith) k) (norm_nonneg _)
  let F : ℕ → ℝ → ℂ := fun k θ =>
    a k * (R : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)
  have hseries : ∀ θ : ℝ,
      h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = ∑' k : ℕ, F k θ := fun θ => by
    have h1 := (Complex.hasSum_taylorSeries_of_entire hh c
      (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).tsum_eq.symm
    rw [h1]
    refine tsum_congr fun k => ?_
    rw [add_sub_cancel_left, smul_eq_mul, smul_eq_mul, mul_pow, ← Complex.exp_nat_mul]
    dsimp [F, a]; ring_nf
  simp_rw [hseries]
  have hint_tsum : ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑' k : ℕ, F k θ =
      ∑' k : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), F k θ := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    refine (hasSum_integral_of_summable_integral_norm (F := F)
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) (fun k => ?_) ?_).tsum_eq.symm
    · exact (Continuous.intervalIntegrable (by dsimp [F]; fun_prop) 0 (2 * Real.pi)).1
    · refine (hsumR.mul_left (2 * Real.pi)).of_nonneg_of_le
        (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      have hconst : ∀ θ : ℝ, ‖F k θ‖ = ‖a k‖ * R ^ k := fun θ => by
        dsimp [F]
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
          show (k : ℂ) * (θ : ℂ) * Complex.I = (((k : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      simp_rw [hconst]
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc,
        sub_zero, ENNReal.toReal_ofReal (by positivity)]
  rw [hint_tsum]
  have hterm : ∀ k : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), F k θ =
      if k = 0 then (2 * Real.pi : ℂ) * h c else 0 := fun k => by
    dsimp [F]
    rw [intervalIntegral.integral_const_mul]
    have h1 := integral_exp_int_mul_I (k : ℤ)
    simp only [Int.cast_natCast] at h1
    rw [h1]
    by_cases hk : k = 0
    · subst hk
      simp [a, iteratedDeriv_zero]
      ring
    · have hne : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk
      rw [if_neg hne, if_neg hk, mul_zero]
  simp_rw [hterm, tsum_ite_eq]

private lemma norm_le_of_circle_bound {h : ℂ → ℂ} (hh : Differentiable ℂ h) (c : ℂ)
    {R B : ℝ} (hR : 0 < R)
    (hbound : ∀ θ : ℝ, ‖h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ B) :
    ‖h c‖ ≤ B := by
  have hint := integral_circle_entire hh c hR
  have h1 : ‖(2 * Real.pi : ℂ) * h c‖ ≤ 2 * Real.pi * B := by
    rw [← hint]
    calc
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi), h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖
          ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖h (c + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by positivity)
      _ ≤ ∫ _θ in (0 : ℝ)..(2 * Real.pi), B := by
            refine intervalIntegral.integral_mono_on (by positivity) ?_ intervalIntegrable_const
              (fun θ _ => hbound θ)
            exact (hh.continuous.comp (by fun_prop)).norm.intervalIntegrable _ _
      _ = 2 * Real.pi * B := by
            rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [norm_mul, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
  nlinarith [Real.pi_pos]

private lemma analyticOrderAt_xi4_eq_L4 (g : ℝ) :
    analyticOrderAt xi4 (1 / 2 + (g : ℂ) * Complex.I) =
      analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I) := by
  set z : ℂ := 1 / 2 + (g : ℂ) * Complex.I
  have hre : -1 < z.re := by simp [z]; norm_num
  have hev : xi4 =ᶠ[𝓝 z] fun w => L4 w * Complex.Gammaℝ (w + 1) := by
    refine Filter.eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hre) ?_
    intro w hw; exact xi4_eq_L4_mul_gammaℝ hw
  have hG_an : AnalyticAt ℂ (fun w => Complex.Gammaℝ (w + 1)) z := by
    have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    have hdiff : DifferentiableOn ℂ (fun w => Complex.Gammaℝ (w + 1)) {w : ℂ | -1 < w.re} := by
      intro w hw
      have hw' : -1 < w.re := hw
      have hwre : 0 < ((w + 1) / 2).re := by simp only [div_ofNat_re, add_re, one_re]; linarith
      have hGdiff : DifferentiableAt ℂ Complex.Gamma ((w + 1) / 2) :=
        Complex.differentiableAt_Gamma _ (fun m => by
          intro hm
          have := congrArg Complex.re hm
          simp only [neg_re, natCast_re] at this
          linarith [Nat.cast_nonneg (α := ℝ) m])
      have hpi : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2)) w :=
        (differentiableAt_const _).cpow
          (((differentiableAt_id.add_const 1).neg).div_const 2)
          (Or.inl (by simp; exact Real.pi_pos))
      have hcomp : DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma ((u + 1) / 2)) w :=
        hGdiff.comp w ((differentiableAt_id.add_const 1).div_const 2)
      have hmul : DifferentiableAt ℂ
          (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2) * Complex.Gamma ((u + 1) / 2)) w :=
        hpi.fun_mul hcomp
      have heq : (fun u : ℂ => (Real.pi : ℂ) ^ (-(u + 1) / 2) * Complex.Gamma ((u + 1) / 2)) =
          (fun u : ℂ => Complex.Gammaℝ (u + 1)) := by
        ext u; simp [Complex.Gammaℝ_def]
      rw [heq] at hmul
      exact hmul.differentiableWithinAt
    exact (hdiff.analyticOnNhd hopen) z hre
  have hG_nz : Complex.Gammaℝ (z + 1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [z]; norm_num)
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt (L4 * fun w => Complex.Gammaℝ (w + 1)) z = analyticOrderAt L4 z
  rw [analyticOrderAt_mul (L4_differentiable.analyticAt z) hG_an,
    hG_an.analyticOrderAt_eq_zero.mpr hG_nz, add_zero]

private lemma xi4_zero_count_upper :
    ∃ A : ℝ, 0 < A ∧ ∀ (R : ℝ) (S : Finset ℝ), 1 ≤ R →
      (∀ g ∈ S, 0 < g ∧ g ≤ R ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0) →
      ∑ g ∈ S, ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) ≤
        A * R * Real.log (3 * R) := by
  classical
  obtain ⟨Cxi, hCxipos, hCxi⟩ := norm_xi4_le_exp_R_log_R
  have hxi_half_ne : xi4 (1 / 2 : ℂ) ≠ 0 := by
    rw [xi4_eq_L4_mul_gammaℝ (by norm_num)]
    exact mul_ne_zero (by simpa using L4_real_ne_zero (by norm_num : (0 : ℝ) < 1 / 2))
      (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hxi_half_pos : 0 < ‖xi4 (1 / 2 : ℂ)‖ := norm_pos_iff.mpr hxi_half_ne
  have hord_xi_ne_top : ∀ z : ℂ, analyticOrderAt xi4 z ≠ ⊤ := by
    intro z
    rw [ne_eq, analyticOrderAt_eq_top]
    intro hev
    have h0 := (xi4_differentiable.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ (1 / 2 : ℂ))
    exact hxi_half_ne h0
  let A : ℝ := 6 * Cxi + 2 * |Real.log ‖xi4 (1 / 2 : ℂ)‖| + 1
  refine ⟨A, by positivity, fun R S hR hS => ?_⟩
  let mult : ℝ → ℕ := fun g => (analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat
  let P : ℂ → ℂ := fun z => ∏ g ∈ S, (z - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g
  have hP_diff : Differentiable ℂ P := fun z =>
    DifferentiableAt.fun_finsetProd fun g _ => (differentiableAt_id.sub (differentiableAt_const _)).pow _
  have hP_half_ne : P (1 / 2 : ℂ) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun g hg => pow_ne_zero _ ?_
    have hg0 : 0 < g := (hS g hg).1
    intro h0
    have := congrArg Complex.im h0
    simp at this; linarith
  have hord_P_le_xi : ∀ z : ℂ, analyticOrderAt P z ≤ analyticOrderAt xi4 z := by
    intro z
    have han_fac : ∀ g ∈ S,
        AnalyticAt ℂ (fun w : ℂ => (w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) z :=
      fun g _ => (analyticAt_id.sub analyticAt_const).pow _
    rw [analyticOrderAt_finset_prod_aux S _ z han_fac]
    have hfac_ord : ∀ g ∈ S,
        analyticOrderAt (fun w : ℂ => (w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) z =
        if z = 1 / 2 + (g : ℂ) * Complex.I then (mult g : ℕ∞) else 0 := by
      intro g _
      have hlin : AnalyticAt ℂ (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I)) z := by fun_prop
      change analyticOrderAt ((fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) z = _
      rw [analyticOrderAt_pow hlin]
      by_cases hzg : z = 1 / 2 + (g : ℂ) * Complex.I
      · subst hzg
        rw [if_pos rfl]
        have h1 : analyticOrderAt (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I))
            (1 / 2 + (g : ℂ) * Complex.I) = ((1 : ℕ) : ℕ∞) := by
          have hlin' : AnalyticAt ℂ (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I))
              (1 / 2 + (g : ℂ) * Complex.I) := by fun_prop
          rw [hlin'.analyticOrderAt_eq_natCast]
          exact ⟨fun _ => 1, analyticAt_const, one_ne_zero,
            Filter.Eventually.of_forall fun w => by simp [smul_eq_mul]⟩
        rw [h1, Nat.cast_one, nsmul_eq_mul, mul_one]
      · rw [if_neg hzg, hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hzg), smul_zero]
    rw [Finset.sum_congr rfl hfac_ord]
    by_cases hex : ∃ g ∈ S, z = 1 / 2 + (g : ℂ) * Complex.I
    · obtain ⟨g0, hg0S, rfl⟩ := hex
      have hsum_eq : (∑ g ∈ S, if (1 / 2 : ℂ) + (g0 : ℂ) * Complex.I = 1 / 2 + (g : ℂ) * Complex.I
          then (mult g : ℕ∞) else 0) = (mult g0 : ℕ∞) := by
        rw [Finset.sum_eq_single g0]
        · rw [if_pos rfl]
        · intro g _ hne
          rw [if_neg]
          intro heq
          have := congrArg Complex.im heq
          simp at this
          exact hne this.symm
        · intro hnot; exact absurd hg0S hnot
      rw [hsum_eq]
      dsimp [mult]
      rw [← analyticOrderAt_xi4_eq_L4 g0, ENat.natCast_toNat (hord_xi_ne_top _)]
    · push Not at hex
      have hsum0 : (∑ g ∈ S, if z = 1 / 2 + (g : ℂ) * Complex.I then (mult g : ℕ∞) else 0) = 0 :=
        Finset.sum_eq_zero fun g hg => if_neg (hex g hg)
      rw [hsum0]
      exact bot_le
  have hord_P_ne_top : ∀ z : ℂ, analyticOrderAt P z ≠ ⊤ := fun z htop => by
    have hle := hord_P_le_xi z
    rw [htop] at hle
    exact hord_xi_ne_top z (top_le_iff.mp hle)
  have hQ_loc : ∀ z0 : ℂ, ∃ U : Set ℂ, IsOpen U ∧ z0 ∈ U ∧
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧ ∀ z ∈ U, xi4 z = P z * q z := by
    intro z0
    have hfinP := hord_P_ne_top z0
    have hfinXi := hord_xi_ne_top z0
    obtain ⟨f, hf_an, _, hfeq⟩ := (xi4_differentiable.analyticAt z0).analyticOrderAt_ne_top.mp hfinXi
    obtain ⟨g, hg_an, hgz, hgeq⟩ := (hP_diff.analyticAt z0).analyticOrderAt_ne_top.mp hfinP
    have hle_nat : analyticOrderNatAt P z0 ≤ analyticOrderNatAt xi4 z0 := by
      have h1 := Nat.cast_analyticOrderNatAt hfinP
      have h2 := Nat.cast_analyticOrderNatAt hfinXi
      have hle := hord_P_le_xi z0
      rw [← h1, ← h2] at hle
      exact Nat.cast_le.mp hle
    let d : ℕ := analyticOrderNatAt xi4 z0 - analyticOrderNatAt P z0
    let q : ℂ → ℂ := fun z => (z - z0) ^ d * (f z / g z)
    have hq_an : AnalyticAt ℂ q z0 := ((analyticAt_id.sub analyticAt_const).pow d).mul (hf_an.div hg_an hgz)
    have hq_ev : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ q z ∧ xi4 z = P z * q z := by
      filter_upwards [hq_an.eventually_analyticAt, hg_an.continuousAt.eventually_ne hgz, hfeq, hgeq] with
        z hqa hgnz hfz' hgz'
      refine ⟨hqa.differentiableAt, ?_⟩
      rw [hfz', hgz', smul_eq_mul, smul_eq_mul]
      dsimp [q]
      have hpow : (z - z0) ^ analyticOrderNatAt xi4 z0 =
          (z - z0) ^ analyticOrderNatAt P z0 * (z - z0) ^ d := by
        rw [← pow_add, Nat.add_sub_cancel' hle_nat]
      rw [hpow]
      field_simp [hgnz]
    obtain ⟨U, hUsub, hUopen, hz0U⟩ := eventually_nhds_iff.mp hq_ev
    exact ⟨U, hUopen, hz0U, q, fun z hz => (hUsub z hz).1.differentiableWithinAt,
      fun z hz => (hUsub z hz).2⟩
  let Q : ℂ → ℂ := fun z0 => (hQ_loc z0).choose_spec.2.2.choose z0
  have hQ_eq_loc : ∀ z0 : ℂ, ∀ z ∈ (hQ_loc z0).choose,
      Q z = (hQ_loc z0).choose_spec.2.2.choose z := by
    intro z0 z hz
    let q0 := (hQ_loc z0).choose_spec.2.2.choose
    let qz := (hQ_loc z).choose_spec.2.2.choose
    have hU0 := (hQ_loc z0).choose_spec.1
    have hUz := (hQ_loc z).choose_spec.1
    have hzUz := (hQ_loc z).choose_spec.2.1
    have hq0_spec := (hQ_loc z0).choose_spec.2.2.choose_spec
    have hqz_spec := (hQ_loc z).choose_spec.2.2.choose_spec
    have hP_ev_ne : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 := by
      have hanP : AnalyticOnNhd ℂ P Set.univ := hP_diff.differentiableOn.analyticOnNhd isOpen_univ
      by_contra hnot
      have hfreq : ∃ᶠ w in 𝓝[≠] z, P w = 0 := by simpa [Filter.not_eventually] using hnot
      have h0 := hanP.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ z) hfreq (Set.mem_univ (1 / 2 : ℂ))
      exact hP_half_ne h0
    have heq_punc : ∀ᶠ w in 𝓝[≠] z, qz w = q0 w := by
      filter_upwards [nhdsWithin_le_nhds ((hU0.inter hUz).mem_nhds ⟨hz, hzUz⟩), hP_ev_ne] with w hw hPw
      exact mul_left_cancel₀ hPw ((hqz_spec.2 w hw.2).symm.trans (hq0_spec.2 w hw.1))
    have hc1 : ContinuousAt qz z := (hqz_spec.1.differentiableAt (hUz.mem_nhds hzUz)).continuousAt
    have hc2 : ContinuousAt q0 z := (hq0_spec.1.differentiableAt (hU0.mem_nhds hz)).continuousAt
    exact tendsto_nhds_unique (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      ((hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' (heq_punc.mono fun _ h => h.symm))
  have hQ_diff : Differentiable ℂ Q := by
    intro z0
    have hU0 := (hQ_loc z0).choose_spec.1
    have hz0 := (hQ_loc z0).choose_spec.2.1
    have hq0_diff := (hQ_loc z0).choose_spec.2.2.choose_spec.1
    exact (hq0_diff.differentiableAt (hU0.mem_nhds hz0)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU0.mem_nhds hz0) (hQ_eq_loc z0))
  have hxi_eq_PQ : ∀ z : ℂ, xi4 z = P z * Q z := fun z =>
    (hQ_loc z).choose_spec.2.2.choose_spec.2 z (hQ_loc z).choose_spec.2.1
  -- Circle bound on |z - 1/2| = 3 * R
  let N : ℕ := ∑ g ∈ S, mult g
  have hRpos : 0 < R := by linarith
  have hQ_circle : ∀ θ : ℝ,
      ‖Q (1 / 2 + ((3 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
        Real.exp (Cxi * (3 * R) * Real.log (3 * R)) / (2 * R) ^ N := by
    intro θ
    set z : ℂ := 1 / 2 + ((3 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    have hznorm : ‖z - 1 / 2‖ = 3 * R := by
      dsimp [z]
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hxi_up : ‖xi4 z‖ ≤ Real.exp (Cxi * (3 * R) * Real.log (3 * R)) := by
      have h1 := hCxi z (by rw [hznorm]; linarith)
      rwa [hznorm] at h1
    have hP_lo : (2 * R) ^ N ≤ ‖P z‖ := by
      dsimp [P, N]
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun g hg => ?_
      rw [norm_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ (mult g)
      have ⟨hg0, hgR, _⟩ := hS g hg
      have hsub : z - (1 / 2 + (g : ℂ) * Complex.I) = (z - 1 / 2) - (g : ℂ) * Complex.I := by ring
      rw [hsub]
      have htri := norm_sub_norm_le (z - 1 / 2) ((g : ℂ) * Complex.I)
      rw [hznorm, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hg0.le] at htri
      linarith
    have hPpos : 0 < ‖P z‖ := lt_of_lt_of_le (by positivity) hP_lo
    have hmul : ‖P z‖ * ‖Q z‖ = ‖xi4 z‖ := by rw [← norm_mul, ← hxi_eq_PQ z]
    rw [le_div_iff₀ (by positivity : 0 < (2 * R) ^ N)]
    calc
      ‖Q z‖ * (2 * R) ^ N = (2 * R) ^ N * ‖Q z‖ := mul_comm _ _
      _ ≤ ‖P z‖ * ‖Q z‖ := mul_le_mul_of_nonneg_right hP_lo (norm_nonneg _)
      _ = ‖xi4 z‖ := hmul
      _ ≤ Real.exp (Cxi * (3 * R) * Real.log (3 * R)) := hxi_up
  have hQ_half : ‖Q (1 / 2 : ℂ)‖ ≤ Real.exp (Cxi * (3 * R) * Real.log (3 * R)) / (2 * R) ^ N :=
    norm_le_of_circle_bound hQ_diff (1 / 2 : ℂ) (by positivity) hQ_circle
  have hP_half : ‖P (1 / 2 : ℂ)‖ ≤ R ^ N := by
    dsimp [P, N]
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun g hg => ?_
    rw [norm_pow]
    have ⟨hg0, hgR, _⟩ := hS g hg
    have hnorm : ‖(1 / 2 : ℂ) - (1 / 2 + (g : ℂ) * Complex.I)‖ = g := by
      have : (1 / 2 : ℂ) - (1 / 2 + (g : ℂ) * Complex.I) = -((g : ℂ) * Complex.I) := by ring
      rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hg0.le]
    rw [hnorm]
    exact pow_le_pow_left₀ hg0.le hgR (mult g)
  have hxi_half_le : ‖xi4 (1 / 2 : ℂ)‖ * (2 : ℝ) ^ N ≤ Real.exp (Cxi * (3 * R) * Real.log (3 * R)) := by
    have h1 : ‖xi4 (1 / 2 : ℂ)‖ ≤ R ^ N * (Real.exp (Cxi * (3 * R) * Real.log (3 * R)) / (2 * R) ^ N) := by
      rw [hxi_eq_PQ (1 / 2 : ℂ), norm_mul]
      exact mul_le_mul hP_half hQ_half (norm_nonneg _) (by positivity)
    have h2 : R ^ N * (Real.exp (Cxi * (3 * R) * Real.log (3 * R)) / (2 * R) ^ N) =
        Real.exp (Cxi * (3 * R) * Real.log (3 * R)) / (2 : ℝ) ^ N := by
      rw [mul_pow]; field_simp [hRpos.ne']
    rw [h2, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)] at h1
    exact h1
  have hlog_le := Real.log_le_log (by positivity) hxi_half_le
  rw [Real.log_mul hxi_half_pos.ne' (by positivity), Real.log_pow, Real.log_exp] at hlog_le
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog3R : 1 ≤ Real.log (3 * R) := by
    have hexp1 : Real.exp 1 ≤ 3 * R := by linarith [Real.exp_one_lt_d9]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp1
  have hRlog_ge1 : 1 ≤ R * Real.log (3 * R) := by nlinarith
  have hN_cast : ∑ g ∈ S, (mult g : ℝ) = (N : ℝ) := by dsimp [N]; rw [Nat.cast_sum]
  rw [show ∑ g ∈ S, ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) = (N : ℝ) from hN_cast]
  have hN_half : (1 / 2 : ℝ) * (N : ℝ) ≤ (N : ℝ) * Real.log 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hneg_log : -Real.log ‖xi4 (1 / 2 : ℂ)‖ ≤ |Real.log ‖xi4 (1 / 2 : ℂ)‖| := neg_le_abs _
  have habs_le : |Real.log ‖xi4 (1 / 2 : ℂ)‖| ≤ |Real.log ‖xi4 (1 / 2 : ℂ)‖| * (R * Real.log (3 * R)) :=
    le_mul_of_one_le_right (abs_nonneg _) hRlog_ge1
  dsimp [A]
  nlinarith

private lemma sum_inv_sq_zeros_bounded :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (T : ℝ) (Z : Finset ℝ), 2 ≤ T →
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0) →
      ∑ g ∈ Z, ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) / (1 / 4 + g ^ 2) ≤ C0 := by
  classical
  obtain ⟨A, hApos, hA⟩ := xi4_zero_count_upper
  refine ⟨4 * A * Real.log 3 + 16 * A, by
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity, fun T Z hT hZ => ?_⟩
  let mult : ℝ → ℕ := fun g => (analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat
  let K : ℕ := ⌈T⌉₊
  let Z0 : Finset ℝ := Z.filter (fun g => g ≤ 1)
  let Zj : ℕ → Finset ℝ := fun j => Z.filter (fun g => (2 : ℝ) ^ j < g ∧ g ≤ (2 : ℝ) ^ (j + 1))
  have hcov : Z ⊆ Z0 ∪ (Finset.range K).biUnion Zj := by
    intro g hg
    obtain ⟨_, hgT, _⟩ := (hZ g).mp hg
    by_cases hg1 : g ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, hg1⟩)
    · push Not at hg1
      refine Finset.mem_union_right _ ?_
      have hpow : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ n := by
        intro n
        induction n with
        | zero => norm_num
        | succ m ih =>
          rw [pow_succ]
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
          push_cast; linarith
      have hgK : g ≤ (2 : ℝ) ^ K := le_trans hgT (le_trans (Nat.le_ceil T) (hpow K))
      have hex : ∀ m : ℕ, 1 < g → g ≤ (2 : ℝ) ^ m →
          ∃ j < m, (2 : ℝ) ^ j < g ∧ g ≤ (2 : ℝ) ^ (j + 1) := by
        intro m
        induction m with
        | zero => intro h1 h2; norm_num at h2; linarith
        | succ d ih =>
          intro h1 h2
          by_cases hd : g ≤ (2 : ℝ) ^ d
          · obtain ⟨j, hjd, hlo, hhi⟩ := ih h1 hd
            exact ⟨j, Nat.lt_succ_of_lt hjd, hlo, hhi⟩
          · push Not at hd
            exact ⟨d, Nat.lt_succ_self d, hd, h2⟩
      obtain ⟨j, hjK, hlo, hhi⟩ := hex K hg1 hgK
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjK,
        Finset.mem_filter.mpr ⟨hg, hlo, hhi⟩⟩
  have hnn : ∀ g : ℝ, 0 ≤ (mult g : ℝ) / (1 / 4 + g ^ 2) := fun g => by positivity
  have hZj_disj : Pairwise (fun j1 j2 => Disjoint (Zj j1) (Zj j2)) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (Finset.mem_filter.mp hg1).2
    have h2 := (Finset.mem_filter.mp hg2).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpow : (2 : ℝ) ^ (j1 + 1) ≤ (2 : ℝ) ^ j2 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    · have hpow : (2 : ℝ) ^ (j2 + 1) ≤ (2 : ℝ) ^ j1 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  have hZ0_disj : Disjoint Z0 ((Finset.range K).biUnion Zj) := by
    rw [Finset.disjoint_left]
    intro g hg0 hgu
    have hle1 : g ≤ 1 := (Finset.mem_filter.mp hg0).2
    obtain ⟨j, _, hgj⟩ := Finset.mem_biUnion.mp hgu
    have hgt : (2 : ℝ) ^ j < g := (Finset.mem_filter.mp hgj).2.1
    have h1pow : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hsplit : ∑ g ∈ Z, (mult g : ℝ) / (1 / 4 + g ^ 2) ≤
      (∑ g ∈ Z0, (mult g : ℝ) / (1 / 4 + g ^ 2)) +
      ∑ j ∈ Finset.range K, ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2) := by
    calc
      ∑ g ∈ Z, (mult g : ℝ) / (1 / 4 + g ^ 2)
          ≤ ∑ g ∈ Z0 ∪ (Finset.range K).biUnion Zj, (mult g : ℝ) / (1 / 4 + g ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hcov fun g _ _ => hnn g
      _ = (∑ g ∈ Z0, (mult g : ℝ) / (1 / 4 + g ^ 2)) +
            ∑ g ∈ (Finset.range K).biUnion Zj, (mult g : ℝ) / (1 / 4 + g ^ 2) :=
            Finset.sum_union hZ0_disj
      _ = (∑ g ∈ Z0, (mult g : ℝ) / (1 / 4 + g ^ 2)) +
            ∑ j ∈ Finset.range K, ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2) := by
            rw [Finset.sum_biUnion (fun a _ b _ hab => hZj_disj hab)]
  have hZ0_le : ∑ g ∈ Z0, (mult g : ℝ) / (1 / 4 + g ^ 2) ≤ 4 * A * Real.log 3 := by
    have h1 : ∑ g ∈ Z0, (mult g : ℝ) / (1 / 4 + g ^ 2) ≤ 4 * ∑ g ∈ Z0, (mult g : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun g _ => ?_
      have hden : (1 / 4 : ℝ) ≤ 1 / 4 + g ^ 2 := by linarith [sq_nonneg g]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 / 4 + g ^ 2)]
      nlinarith [Nat.cast_nonneg (α := ℝ) (mult g)]
    have h2 : ∑ g ∈ Z0, (mult g : ℝ) ≤ A * 1 * Real.log (3 * 1) := by
      refine hA 1 Z0 le_rfl fun g hg => ?_
      obtain ⟨hgZ, hg1⟩ := Finset.mem_filter.mp hg
      obtain ⟨hg0, _, hLz⟩ := (hZ g).mp hgZ
      exact ⟨hg0, hg1, hLz⟩
    rw [mul_one, mul_one] at h2
    linarith
  have hZj_le : ∀ j : ℕ,
      ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2) ≤ 2 * A * (((j : ℝ) + 3) / (2 : ℝ) ^ j) := by
    intro j
    have h1 : ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2) ≤
        (∑ g ∈ Zj j, (mult g : ℝ)) / ((2 : ℝ) ^ j) ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun g hg => ?_
      have hlo : (2 : ℝ) ^ j < g := (Finset.mem_filter.mp hg).2.1
      have hden : ((2 : ℝ) ^ j) ^ 2 ≤ 1 / 4 + g ^ 2 := by
        have hsq : ((2 : ℝ) ^ j) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ (by positivity) hlo.le 2
        linarith
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hden
    have h2 : ∑ g ∈ Zj j, (mult g : ℝ) ≤ A * (2 : ℝ) ^ (j + 1) * Real.log (3 * (2 : ℝ) ^ (j + 1)) := by
      refine hA ((2 : ℝ) ^ (j + 1)) (Zj j) (one_le_pow₀ (by norm_num)) fun g hg => ?_
      obtain ⟨hgZ, _, hhi⟩ := Finset.mem_filter.mp hg
      obtain ⟨hg0, _, hLz⟩ := (hZ g).mp hgZ
      exact ⟨hg0, hhi, hLz⟩
    have hlog : Real.log (3 * (2 : ℝ) ^ (j + 1)) ≤ (j : ℝ) + 3 := by
      have h3le : 3 * (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + 3) := by
        have hrew : (2 : ℝ) ^ (j + 3) = (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ 2 := by
          rw [← pow_add]
        rw [hrew]
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
        nlinarith
      have h1' := Real.log_le_log (by positivity) h3le
      rw [Real.log_pow] at h1'
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
      push_cast at h1'
      nlinarith
    have h3 : A * (2 : ℝ) ^ (j + 1) * Real.log (3 * (2 : ℝ) ^ (j + 1)) ≤
        A * (2 : ℝ) ^ (j + 1) * ((j : ℝ) + 3) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    calc
      ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2)
          ≤ (∑ g ∈ Zj j, (mult g : ℝ)) / ((2 : ℝ) ^ j) ^ 2 := h1
      _ ≤ (A * (2 : ℝ) ^ (j + 1) * ((j : ℝ) + 3)) / ((2 : ℝ) ^ j) ^ 2 :=
            div_le_div_of_nonneg_right (h2.trans h3) (by positivity)
      _ = 2 * A * (((j : ℝ) + 3) / (2 : ℝ) ^ j) := by
            rw [pow_succ, sq]
            have h2j : (2 : ℝ) ^ j ≠ 0 := by positivity
            field_simp [h2j]
  have hgeom : ∑ j ∈ Finset.range K, (((j : ℝ) + 3) / (2 : ℝ) ^ j) ≤ 8 := by
    have hclosed : ∀ m : ℕ,
        ∑ j ∈ Finset.range m, (((j : ℝ) + 3) / (2 : ℝ) ^ j) = 8 - (2 * (m : ℝ) + 8) / (2 : ℝ) ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ d ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        have h2d : (2 : ℝ) ^ d ≠ 0 := by positivity
        push_cast
        field_simp [h2d]; ring
    rw [hclosed K]
    have hnn' : 0 ≤ (2 * (K : ℝ) + 8) / (2 : ℝ) ^ K := by positivity
    linarith
  have hdyadic : ∑ j ∈ Finset.range K, ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2) ≤ 16 * A := by
    calc
      ∑ j ∈ Finset.range K, ∑ g ∈ Zj j, (mult g : ℝ) / (1 / 4 + g ^ 2)
          ≤ ∑ j ∈ Finset.range K, 2 * A * (((j : ℝ) + 3) / (2 : ℝ) ^ j) :=
            Finset.sum_le_sum fun j _ => hZj_le j
      _ = 2 * A * ∑ j ∈ Finset.range K, (((j : ℝ) + 3) / (2 : ℝ) ^ j) := (Finset.mul_sum ..).symm
      _ ≤ 2 * A * 8 := mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 16 * A := by ring
  exact hsplit.trans (add_le_add hZ0_le hdyadic)

/- ### Part C: Flipped-sign Fejer explicit formula -/

/- ### Step 3: Fejer kernel K_T and its exact cosine transform -/

/-- The normalized Fejer kernel K_T(v) = (1 - cos(T v)) / (π T v^2). -/
noncomputable def fejerK (T v : ℝ) : ℝ :=
  if v = 0 then T / (2 * Real.pi) else (1 - Real.cos (T * v)) / (Real.pi * T * v ^ 2)

private lemma fejerK_nonneg {T : ℝ} (hT : 0 < T) (v : ℝ) : 0 ≤ fejerK T v := by
  dsimp [fejerK]
  split_ifs with hv
  · positivity
  · have h1 : Real.cos (T * v) ≤ 1 := Real.cos_le_one _
    exact div_nonneg (by linarith) (by positivity)

private lemma fejerK_neg (T v : ℝ) : fejerK T (-v) = fejerK T v := by
  dsimp [fejerK]
  by_cases hv : v = 0
  · subst hv; simp
  · have hnv : -v ≠ 0 := neg_ne_zero.mpr hv
    rw [if_neg hnv, if_neg hv, mul_neg, Real.cos_neg, neg_sq]

private lemma one_sub_cos_le_half_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h1 : 1 - Real.cos x = 2 * (Real.sin (x / 2)) ^ 2 := by
    have hcos := Real.cos_two_mul' (x / 2)
    have h2 : 2 * (x / 2) = x := by ring
    rw [h2] at hcos
    have hpy := Real.sin_sq_add_cos_sq (x / 2)
    nlinarith
  rw [h1]
  have hsin : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have hsq : (Real.sin (x / 2)) ^ 2 ≤ (x / 2) ^ 2 := by
    have := sq_le_sq.mpr hsin
    simpa using this
  nlinarith

private lemma fejerK_le_const {T : ℝ} (hT : 0 < T) (v : ℝ) :
    fejerK T v ≤ T / (2 * Real.pi) := by
  dsimp [fejerK]
  split_ifs with hv
  · exact le_rfl
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := one_sub_cos_le_half_sq (T * v)
    nlinarith [Real.pi_pos, hT, sq_nonneg v]

private lemma fejerK_le_tail {T : ℝ} (hT : 0 < T) {v : ℝ} (hv : v ≠ 0) :
    fejerK T v ≤ 2 / (Real.pi * T * v ^ 2) := by
  dsimp [fejerK]
  rw [if_neg hv]
  have h1 : 1 - Real.cos (T * v) ≤ 2 := by linarith [Real.neg_one_le_cos (T * v)]
  exact div_le_div_of_nonneg_right h1 (by positivity)

private lemma measurable_fejerK (T : ℝ) : Measurable (fejerK T) := by
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

private lemma integrable_fejerK {T : ℝ} (hT : 0 < T) : Integrable (fejerK T) := by
  have hmeas : AEStronglyMeasurable (fejerK T) volume := (measurable_fejerK T).aestronglyMeasurable
  have h1 : IntegrableOn (fejerK T) (Set.Icc (-1 : ℝ) 1) := by
    refine (integrableOn_const (C := T / (2 * Real.pi)) (hs := measure_Icc_lt_top.ne)).mono'
      hmeas.restrict ?_
    filter_upwards with v
    rw [Real.norm_of_nonneg (fejerK_nonneg hT v)]
    exact fejerK_le_const hT v
  have h2 : IntegrableOn (fejerK T) (Set.Ioi (1 : ℝ)) := by
    have hdom : IntegrableOn (fun v : ℝ => (2 / (Real.pi * T)) * v ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
    refine hdom.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hvpos : 0 < v := zero_lt_one.trans hv
    rw [Real.norm_of_nonneg (fejerK_nonneg hT v)]
    calc
      fejerK T v ≤ 2 / (Real.pi * T * v ^ 2) := fejerK_le_tail hT hvpos.ne'
      _ = (2 / (Real.pi * T)) * v ^ (-2 : ℝ) := by
            rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hvpos.le,
              Real.rpow_natCast]; ring
  have h3 : IntegrableOn (fejerK T) (Set.Iio (-1 : ℝ)) := by
    rw [← integrable_indicator_iff measurableSet_Iio]
    have h2ind : Integrable (Set.indicator (Set.Ioi (1 : ℝ)) (fejerK T)) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr h2
    have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
    refine (hmp.integrable_comp_emb (MeasurableEquiv.neg ℝ).measurableEmbedding).mp ?_
    refine h2ind.congr (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : 1 < v
    · have hnv : -v < -1 := by linarith
      simp [hv, hnv, fejerK_neg]
    · have hnv : ¬ (-v < -1) := by linarith
      simp [hv, hnv]
  have hunion : (Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1) ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext v; simp
  rw [← integrableOn_univ, ← hunion]
  exact (h3.union h1).union h2

/-- The positive universal constant C = ∫_0^∞ (1 - cos w) / w^2 dw. -/
noncomputable def fejerConst : ℝ :=
  ∫ w in Set.Ioi (0 : ℝ), (1 - Real.cos w) / w ^ 2

private lemma integrableOn_one_sub_cos_div_sq :
    IntegrableOn (fun w : ℝ => (1 - Real.cos w) / w ^ 2) (Set.Ioi (0 : ℝ)) := by
  have h1 := (integrable_fejerK zero_lt_one).integrableOn (s := Set.Ioi (0 : ℝ))
  have h2 := h1.const_mul Real.pi
  refine IntegrableOn.congr_fun h2 (fun w hw => ?_) measurableSet_Ioi
  have hwne : w ≠ 0 := (Set.mem_Ioi.mp hw).ne'
  dsimp [fejerK]
  rw [if_neg hwne, one_mul]
  field_simp [Real.pi_pos.ne']

private lemma fejerConst_pos : 0 < fejerConst := by
  have hint := integrableOn_one_sub_cos_div_sq
  have hsub : Set.Icc (1 : ℝ) 2 ⊆ Set.Ioi (0 : ℝ) := fun w hw => lt_of_lt_of_le zero_lt_one hw.1
  have hge : ∫ w in Set.Icc (1 : ℝ) 2, (1 - Real.cos w) / w ^ 2 ≤ fejerConst := by
    refine setIntegral_mono_set hint ?_ hsub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact div_nonneg (by linarith [Real.cos_le_one w]) (sq_nonneg w)
  have hlow : (1 - Real.cos 1) / 4 ≤ ∫ w in Set.Icc (1 : ℝ) 2, (1 - Real.cos w) / w ^ 2 := by
    have hconst_int : IntegrableOn (fun _ : ℝ => (1 - Real.cos 1) / 4) (Set.Icc (1 : ℝ) 2) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    have hmono : ∫ _w in Set.Icc (1 : ℝ) 2, (1 - Real.cos 1) / 4 ≤
        ∫ w in Set.Icc (1 : ℝ) 2, (1 - Real.cos w) / w ^ 2 := by
      refine setIntegral_mono_on hconst_int (hint.mono_set hsub) measurableSet_Icc ?_
      intro w hw
      have hcos_le : Real.cos w ≤ Real.cos 1 := by
        refine Real.strictAntiOn_cos.antitoneOn ?_ ?_ hw.1
        · exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
        · exact ⟨by linarith [hw.1], by linarith [hw.2, Real.pi_gt_three]⟩
      have hw2 : w ^ 2 ≤ 4 := by nlinarith [hw.1, hw.2]
      have hwpos : 0 < w ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hw.1)
      calc
        (1 - Real.cos 1) / 4 ≤ (1 - Real.cos w) / 4 := by linarith
        _ ≤ (1 - Real.cos w) / w ^ 2 :=
              div_le_div_of_nonneg_left (by linarith [Real.cos_le_one w]) hwpos hw2
    have hval : ∫ _w in Set.Icc (1 : ℝ) 2, (1 - Real.cos 1) / 4 = (1 - Real.cos 1) / 4 := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by norm_num)]; norm_num
    linarith
  have hcos1_lt : Real.cos 1 < 1 := by
    have := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨zero_le_one, by linarith [Real.pi_gt_three]⟩ zero_lt_one
    rwa [Real.cos_zero] at this
  linarith

private lemma integral_one_sub_cos_mul_div_sq {α : ℝ} (hα : 0 ≤ α) :
    ∫ w in Set.Ioi (0 : ℝ), (1 - Real.cos (α * w)) / w ^ 2 = α * fejerConst := by
  rcases hα.eq_or_lt with rfl | hαpos
  · simp
  · have h1 := integral_comp_mul_left_Ioi (fun u : ℝ => (1 - Real.cos u) / u ^ 2) 0 hαpos
    rw [mul_zero, smul_eq_mul] at h1
    have h2 : ∫ w in Set.Ioi (0 : ℝ), (1 - Real.cos (α * w)) / w ^ 2 =
        α ^ 2 * ∫ w in Set.Ioi (0 : ℝ), (1 - Real.cos (α * w)) / (α * w) ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
      have hne : α ≠ 0 := hαpos.ne'
      field_simp [hne]
    rw [h2, h1]
    dsimp [fejerConst]
    field_simp [hαpos.ne']

/-- Exact Fourier transform of the Fejer tent weight equals fejerK. -/
private lemma fourier_tent_eq_fejerK {T : ℝ} (hT : 0 < T) (v : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
      (fejerK T v : ℂ) := by
  have hsplit : ∫ t in (-T)..T,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
      (∫ t in (-T)..0, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I)) +
      (∫ t in (0 : ℝ)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I)) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm <;>
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hneg_part : ∫ t in (-T)..0,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
      ∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (-((t : ℂ) * (v : ℂ) * Complex.I)) := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
      (f := fun t : ℝ => ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I))
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hT.le] at ht
    rw [abs_neg, abs_of_nonneg ht.1]
    congr 2; push_cast; ring
  have hpos_part : ∫ t in (0 : ℝ)..T,
        ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
      ∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hT.le] at ht
    rw [abs_of_nonneg ht.1]
  rw [hsplit, hneg_part, hpos_part,
    ← intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hcomb : ∀ t : ℝ,
      ((1 - t / T : ℝ) : ℂ) * Complex.exp (-((t : ℂ) * (v : ℂ) * Complex.I)) +
      ((1 - t / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) =
      ((2 * (1 - t / T) * Real.cos (t * v) : ℝ) : ℂ) := fun t => by
    have hcos : Complex.exp ((t : ℂ) * (v : ℂ) * Complex.I) +
        Complex.exp (-((t : ℂ) * (v : ℂ) * Complex.I)) = (2 * Real.cos (t * v) : ℂ) := by
      have h1 : (t : ℂ) * (v : ℂ) * Complex.I = ((t * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h1, Complex.exp_mul_I, show -(((t * v : ℝ) : ℂ) * Complex.I) =
          ((- (t * v) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
      simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    push_cast at hcos ⊢
    linear_combination ((1 : ℂ) - (t : ℂ) / (T : ℂ)) * hcos
  simp_rw [hcomb, intervalIntegral.integral_ofReal]
  rw [← Complex.ofReal_mul]
  congr 1
  by_cases hv : v = 0
  · subst hv
    simp only [mul_zero, Real.cos_zero, mul_one, fejerK, ↓reduceIte]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun x : ℝ => 2 * (x - x ^ 2 / (2 * T))) (2 * (1 - t / T)) t := fun t _ => by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * T)) ((2 * t ^ 1) / (2 * T)) t :=
        ((hasDerivAt_pow 2 t).div_const (2 * T))
      have h2 := ((hasDerivAt_id t).sub h1).const_mul 2
      refine h2.congr_deriv ?_
      field_simp [hT.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    field_simp [Real.pi_pos.ne', hT.ne']; ring
  · simp only [fejerK, if_neg hv]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun x : ℝ => 2 * ((1 - x / T) * Real.sin (x * v) / v -
          Real.cos (x * v) / (T * v ^ 2)))
          (2 * (1 - t / T) * Real.cos (t * v)) t := fun t _ => by
      have hxv : HasDerivAt (fun x : ℝ => x * v) v t := by
        simpa using (hasDerivAt_id t).mul_const v
      have h1 : HasDerivAt (fun x : ℝ => 1 - x / T) (-(1 / T)) t := by
        simpa using ((hasDerivAt_id t).div_const T).const_sub (1 : ℝ)
      have hsin : HasDerivAt (fun x : ℝ => Real.sin (x * v)) (Real.cos (t * v) * v) t :=
        hxv.sin
      have hcos : HasDerivAt (fun x : ℝ => Real.cos (x * v)) (-Real.sin (t * v) * v) t :=
        hxv.cos
      have hprod := ((h1.mul hsin).div_const v).sub (hcos.div_const (T * v ^ 2))
      refine (hprod.const_mul 2).congr_deriv ?_
      field_simp [hT.ne', hv]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [zero_mul, Real.sin_zero, Real.cos_zero, mul_comm T v]
    field_simp [Real.pi_pos.ne', hT.ne', hv]; ring

/-- Exact Fourier transform of fejerK at frequency γ ∈ [-T, T] without evaluating fejerConst. -/
private lemma integral_exp_mul_fejerK {T γ : ℝ} (hT : 0 < T) (hγ : |γ| ≤ T) :
    ∫ v : ℝ, Complex.exp (-((γ : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ) =
      (((2 * fejerConst / Real.pi) * (1 - |γ| / T) : ℝ) : ℂ) := by
  have hcos_int : Integrable (fun v : ℝ => Real.cos (γ * v) * fejerK T v) := by
    refine (integrable_fejerK hT).mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (measurable_fejerK T).aestronglyMeasurable) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerK_nonneg hT v)]
    exact mul_le_of_le_one_left (fejerK_nonneg hT v) (Real.abs_cos_le_one _)
  have hsin_int : Integrable (fun v : ℝ => Real.sin (γ * v) * fejerK T v) := by
    refine (integrable_fejerK hT).mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (measurable_fejerK T).aestronglyMeasurable) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerK_nonneg hT v)]
    exact mul_le_of_le_one_left (fejerK_nonneg hT v) (Real.abs_sin_le_one _)
  have hsin_zero : ∫ v : ℝ, Real.sin (γ * v) * fejerK T v = 0 := by
    have hodd := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding (fun v : ℝ => Real.sin (γ * v) * fejerK T v)
    have hneg : (fun v : ℝ => Real.sin (γ * (-v)) * fejerK T (-v)) =
        fun v => -(Real.sin (γ * v) * fejerK T v) := by
      ext v; rw [mul_neg, Real.sin_neg, fejerK_neg]; ring
    change ∫ v : ℝ, Real.sin (γ * (-v)) * fejerK T (-v) = ∫ v : ℝ, Real.sin (γ * v) * fejerK T v at hodd
    rw [hneg, integral_neg] at hodd
    linarith
  have hsplit : ∀ v : ℝ,
      Complex.exp (-((γ : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ) =
      ((Real.cos (γ * v) * fejerK T v : ℝ) : ℂ) -
        Complex.I * ((Real.sin (γ * v) * fejerK T v : ℝ) : ℂ) := fun v => by
    have h1 : -((γ : ℂ) * (v : ℂ) * Complex.I) = ((-(γ * v) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [hsplit]
  have hcos_C : Integrable (fun v : ℝ => ((Real.cos (γ * v) * fejerK T v : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hcos_int
  have hsin_C : Integrable (fun v : ℝ => Complex.I * ((Real.sin (γ * v) * fejerK T v : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.integrable_comp hsin_int).const_mul Complex.I
  have hcos_ofR : ∫ v : ℝ, ((Real.cos (γ * v) * fejerK T v : ℝ) : ℂ) =
      ((∫ v : ℝ, Real.cos (γ * v) * fejerK T v : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hcos_int
  have hsin_ofR : ∫ v : ℝ, ((Real.sin (γ * v) * fejerK T v : ℝ) : ℂ) =
      ((∫ v : ℝ, Real.sin (γ * v) * fejerK T v : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm hsin_int
  rw [integral_sub hcos_C hsin_C, integral_const_mul, hcos_ofR, hsin_ofR,
    hsin_zero, Complex.ofReal_zero, mul_zero, sub_zero]
  congr 1
  -- Even function on ℝ equals 2 * ∫_{Ioi 0}
  have heven : ∫ v : ℝ, Real.cos (γ * v) * fejerK T v =
      2 * ∫ v in Set.Ioi (0 : ℝ), Real.cos (γ * v) * fejerK T v := by
    have hIic : ∫ v in Set.Iic (0 : ℝ), Real.cos (γ * v) * fejerK T v =
        ∫ v in Set.Ioi (0 : ℝ), Real.cos (γ * v) * fejerK T v := by
      rw [integral_Iic_eq_integral_Iio]
      have h1 := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (MeasurableEquiv.neg ℝ).measurableEmbedding
        (fun v : ℝ => Set.indicator (Set.Iio (0 : ℝ)) (fun x => Real.cos (γ * x) * fejerK T x) v)
      change ∫ v : ℝ, Set.indicator (Set.Iio (0 : ℝ)) (fun x => Real.cos (γ * x) * fejerK T x) (-v) =
        ∫ v : ℝ, Set.indicator (Set.Iio (0 : ℝ)) (fun x => Real.cos (γ * x) * fejerK T x) v at h1
      rw [integral_indicator measurableSet_Iio] at h1
      have h2 : (fun v : ℝ => Set.indicator (Set.Iio (0 : ℝ))
          (fun x => Real.cos (γ * x) * fejerK T x) (-v)) =
          Set.indicator (Set.Ioi (0 : ℝ)) (fun x => Real.cos (γ * x) * fejerK T x) := by
        ext v
        by_cases hv : 0 < v
        · simp [hv, mul_neg, Real.cos_neg, fejerK_neg]
        · have hv' : ¬ (-v < 0) := by linarith
          simp [hv, hv']
      rw [h2, integral_indicator measurableSet_Ioi] at h1
      exact h1.symm
    have hunion : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := Set.Iic_union_Ioi
    rw [← setIntegral_univ, ← hunion,
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hcos_int.integrableOn hcos_int.integrableOn, hIic]
    ring
  rw [heven]
  -- Replace γ with |γ| since cos(|γ| v) = cos(γ v)
  set a : ℝ := |γ|
  have ha0 : 0 ≤ a := abs_nonneg γ
  have haT : a ≤ T := hγ
  have hcos_a : ∀ v : ℝ, Real.cos (γ * v) = Real.cos (a * v) := fun v => by
    rcases le_or_gt 0 γ with h | h
    · simp [a, abs_of_nonneg h]
    · simp [a, abs_of_neg h, neg_mul, Real.cos_neg]
  have htrig : ∀ v ∈ Set.Ioi (0 : ℝ),
      Real.cos (γ * v) * fejerK T v =
      (1 / (Real.pi * T)) *
        ((1 / 2) * ((1 - Real.cos ((T + a) * v)) / v ^ 2) +
         (1 / 2) * ((1 - Real.cos ((T - a) * v)) / v ^ 2) -
         (1 - Real.cos (a * v)) / v ^ 2) := by
    intro v hv
    have hvne : v ≠ 0 := (Set.mem_Ioi.mp hv).ne'
    rw [hcos_a v]
    dsimp [fejerK]
    rw [if_neg hvne]
    have hc1 := Real.cos_add (T * v) (a * v)
    have hc2 := Real.cos_sub (T * v) (a * v)
    have he1 : (T + a) * v = T * v + a * v := by ring
    have he2 : (T - a) * v = T * v - a * v := by ring
    rw [he1, he2, hc1, hc2]
    field_simp [Real.pi_pos.ne', hT.ne', hvne]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi htrig, integral_const_mul]
  have hint_scale : ∀ c : ℝ, 0 ≤ c →
      IntegrableOn (fun v : ℝ => (1 - Real.cos (c * v)) / v ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro c hc
    rcases hc.eq_or_lt with rfl | hcpos
    · simp
    · have h1 := ((integrable_fejerK hcpos).integrableOn (s := Set.Ioi (0 : ℝ))).const_mul (Real.pi * c)
      refine IntegrableOn.congr_fun h1 (fun v hv => ?_) measurableSet_Ioi
      have hvne : v ≠ 0 := (Set.mem_Ioi.mp hv).ne'
      dsimp [fejerK]
      rw [if_neg hvne]
      field_simp [Real.pi_pos.ne', hcpos.ne']
  have hi1 := (hint_scale (T + a) (by linarith)).const_mul (1 / 2 : ℝ)
  have hi2 := (hint_scale (T - a) (by linarith)).const_mul (1 / 2 : ℝ)
  have hi12 : IntegrableOn (fun v : ℝ =>
      (1 / 2 : ℝ) * ((1 - Real.cos ((T + a) * v)) / v ^ 2) +
      (1 / 2 : ℝ) * ((1 - Real.cos ((T - a) * v)) / v ^ 2)) (Set.Ioi (0 : ℝ)) := hi1.add hi2
  have hi3 := hint_scale a ha0
  rw [integral_sub hi12 hi3, integral_add hi1 hi2,
    integral_const_mul, integral_const_mul,
    integral_one_sub_cos_mul_div_sq (by linarith),
    integral_one_sub_cos_mul_div_sq (by linarith),
    integral_one_sub_cos_mul_div_sq ha0]
  field_simp [Real.pi_pos.ne', hT.ne']
  ring

private lemma integral_fejerK {T : ℝ} (hT : 0 < T) :
    ∫ v : ℝ, fejerK T v = 2 * fejerConst / Real.pi := by
  have h := integral_exp_mul_fejerK hT (γ := 0) (by simpa using hT.le)
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
    abs_zero, zero_div, sub_zero, mul_one] at h
  have hof : ∫ v : ℝ, (fejerK T v : ℂ) = ((∫ v : ℝ, fejerK T v : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm (integrable_fejerK hT)
  rw [hof] at h
  exact Complex.ofReal_injective h

/- ### Step 4: Riemann-Lebesgue lemma on [-T, T] -/

private lemma tendsto_integral_exp_Icc {T : ℝ} (hT : 0 < T) (f : ℝ → ℂ) :
    Tendsto (fun x : ℝ => ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * f t)
      atTop (𝓝 0) := by
  let g : ℝ → ℂ := Set.indicator (Set.Ioc (-T) T) f
  have hRL := Real.tendsto_integral_exp_smul_cocompact g
  have hcomp : Tendsto (fun x : ℝ => -(x / (2 * Real.pi))) atTop (cocompact ℝ) := by
    have hbot : Tendsto (fun x : ℝ => -(x / (2 * Real.pi))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by positivity))
    exact hbot.mono_right atBot_le_cocompact
  refine (hRL.comp hcomp).congr fun x => ?_
  dsimp only [Function.comp_apply]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp [g]
  by_cases ht : t ∈ Set.Ioc (-T) T
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Circle.smul_def, Real.fourierChar_apply,
      smul_eq_mul]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    push_cast; field_simp [hpi]
  · simp [ht]

/- ### Step 5: Laplace-Mellin representation, Tonelli extension, and local factorization -/

private lemma integral_ofReal_eq {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    ∫ x, (f x : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) :=
  Complex.ofRealCLM.integral_comp_comm hf

private lemma hasDerivAt_neg_mul_const (s c : ℂ) :
    HasDerivAt (fun w : ℂ => -(w * c)) (-c) s := by
  simpa using ((hasDerivAt_id s).mul_const c).fun_neg

/-- Prime-power sum J(⌊e^u⌋) in logarithmic variable u. -/
noncomputable def jExp (u : ℝ) : ℝ := JVal ⌊Real.exp u⌋₊

private lemma measurable_jExp : Measurable jExp :=
  (measurable_of_countable JVal).comp (Nat.measurable_floor.comp Real.continuous_exp.measurable)

private lemma abs_jExp_le (u : ℝ) : |jExp u| ≤ Real.exp u := by
  dsimp [jExp]
  exact (abs_JVal_le _).trans (Nat.floor_le (Real.exp_pos u).le)

private lemma integrableOn_jExp_pow_exp (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun u : ℝ => |jExp u| * u ^ k * Real.exp (-σ * u)) (Set.Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => |jExp u| * u ^ k * Real.exp (-σ * u))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((measurable_jExp.abs.mul (measurable_id.pow_const k)).mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  have hδ : 0 < (σ - 1) / 2 := by linarith
  have hdom : IntegrableOn (fun u : ℝ => ((k ! : ℝ) / ((σ - 1) / 2) ^ k) * Real.exp (-((σ - 1) / 2) * u))
      (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := (Set.mem_Ioi.mp hu).le
  rw [Real.norm_of_nonneg (by positivity)]
  have hpow_le : (((σ - 1) / 2) * u) ^ k / (k ! : ℝ) ≤ Real.exp (((σ - 1) / 2) * u) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have hu_le : u ^ k ≤ ((k ! : ℝ) / ((σ - 1) / 2) ^ k) * Real.exp (((σ - 1) / 2) * u) := by
    rw [mul_pow] at hpow_le
    have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hdk : (0 : ℝ) < ((σ - 1) / 2) ^ k := by positivity
    rw [div_le_iff₀ hfac] at hpow_le
    rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
    nlinarith
  calc
    |jExp u| * u ^ k * Real.exp (-σ * u)
        ≤ Real.exp u * (((k ! : ℝ) / ((σ - 1) / 2) ^ k) * Real.exp (((σ - 1) / 2) * u)) *
            Real.exp (-σ * u) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul (abs_jExp_le u) hu_le (by positivity) (Real.exp_pos u).le)
            (Real.exp_pos _).le
    _ = ((k ! : ℝ) / ((σ - 1) / 2) ^ k) *
          (Real.exp u * Real.exp (((σ - 1) / 2) * u) * Real.exp (-σ * u)) := by ring
    _ = ((k ! : ℝ) / ((σ - 1) / 2) ^ k) * Real.exp (-((σ - 1) / 2) * u) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

private lemma L4_eq_exp_mul_laplace_jExp {s : ℂ} (hs : 1 < s.re) :
    L4 s = Complex.exp (s * ∫ u in Set.Ioi (0 : ℝ), (jExp u : ℂ) * Complex.exp (-(s * (u : ℂ)))) := by
  rw [L4_eq_exp_mul_integral hs]
  congr 2
  have hsub := integral_comp_exp_Ioi (fun t : ℝ => (JVal ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at hsub
  rw [← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  dsimp [jExp]
  rw [Complex.ofReal_exp,
    show Complex.exp (u : ℂ) ^ (-(s + 1)) = Complex.exp (-(s + 1) * (u : ℂ)) by
      rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        show Complex.log (Complex.exp (u : ℂ)) = (u : ℂ) by
          rw [← Complex.ofReal_exp, ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
        , mul_comm]]
  have : Complex.exp (u : ℂ) * ((JVal ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-(s + 1) * (u : ℂ))) =
      (JVal ⌊Real.exp u⌋₊ : ℂ) * (Complex.exp (u : ℂ) * Complex.exp (-(s + 1) * (u : ℂ))) := by ring
  rw [this, ← Complex.exp_add]
  congr 2; ring

private lemma hasDerivAt_laplace_jExp {s0 : ℂ} (hs0 : 1 < s0.re) :
    HasDerivAt (fun s : ℂ => ∫ u in Set.Ioi (0 : ℝ), (jExp u : ℂ) * Complex.exp (-(s * (u : ℂ))))
      (-(∫ u in Set.Ioi (0 : ℝ), ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s0 * (u : ℂ))))) s0 := by
  set δ : ℝ := (s0.re - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let σ0 : ℝ := 1 + δ
  have hσ0 : 1 < σ0 := by dsimp [σ0]; linarith
  have hre_ge : ∀ s ∈ Metric.ball s0 δ, σ0 ≤ s.re := by
    intro s hs
    have h1 : |s.re - s0.re| ≤ ‖s - s0‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - s0)
    have h2 : ‖s - s0‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
    dsimp [σ0, δ] at *; linarith
  let F : ℂ → ℝ → ℂ := fun s u => (jExp u : ℂ) * Complex.exp (-(s * (u : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun s u => -(((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))))
  have hF_meas : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Set.Ioi (0 : ℝ))) := fun s =>
    ((Complex.continuous_ofReal.measurable.comp measurable_jExp).mul (by fun_prop)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' s0) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (((Complex.continuous_ofReal.measurable.comp (measurable_id.mul measurable_jExp)).mul
      (by fun_prop)).neg).aestronglyMeasurable
  have hF_int : IntegrableOn (F s0) (Set.Ioi (0 : ℝ)) := by
    refine (integrableOn_jExp_pow_exp 0 hs0).mono' (hF_meas s0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, neg_re, mul_re,
      ofReal_re, ofReal_im, mul_zero, sub_zero, pow_zero, mul_one, neg_mul]
  have hdiff := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := fun u => |jExp u| * u ^ 1 * Real.exp (-σ0 * u))
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s hs
      have hu0 : 0 ≤ u := (Set.mem_Ioi.mp hu).le
      have hre := hre_ge s hs
      dsimp [F']
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0,
        Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, pow_one]
      have hexp : Real.exp (-(s.re * u)) ≤ Real.exp (-σ0 * u) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc
        u * |jExp u| * Real.exp (-(s.re * u)) = |jExp u| * u * Real.exp (-(s.re * u)) := by ring
        _ ≤ |jExp u| * u * Real.exp (-σ0 * u) := mul_le_mul_of_nonneg_left hexp (by positivity))
    (integrableOn_jExp_pow_exp 1 hσ0)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ s _
      dsimp [F, F']
      have h1 := hasDerivAt_neg_mul_const s (u : ℂ)
      have h2 := h1.cexp.const_mul (jExp u : ℂ)
      refine h2.congr_deriv ?_
      push_cast; ring)).2
  simpa [F', integral_neg] using hdiff


private lemma logDeriv_finset_prod {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ)
    (hF : ∀ i ∈ s, DifferentiableAt ℂ (F i) z) (hne : ∀ i ∈ s, F i z ≠ 0) :
    deriv (fun w => ∏ i ∈ s, F i w) z / (∏ i ∈ s, F i z) =
      ∑ i ∈ s, deriv (F i) z / F i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hFa := hF a (Finset.mem_insert_self a s)
    have hFs : DifferentiableAt ℂ (fun w => ∏ i ∈ s, F i w) z :=
      DifferentiableAt.fun_finsetProd fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hnea := hne a (Finset.mem_insert_self a s)
    have hnes : (∏ i ∈ s, F i z) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hne i (Finset.mem_insert_of_mem hi)
    have hprod_eq : (fun w => ∏ i ∈ insert a s, F i w) =
        fun w => F a w * (∏ i ∈ s, F i w) := by
      ext w; exact Finset.prod_insert ha
    rw [hprod_eq, Finset.prod_insert ha, Finset.sum_insert ha,
      deriv_fun_mul hFa hFs, add_div,
      mul_div_mul_right _ _ hnes, mul_div_mul_left _ _ hnea,
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
         (fun i hi => hne i (Finset.mem_insert_of_mem hi))]

private lemma intervalIntegrable_abs_log_abs_sub (a b c : ℝ) :
    IntervalIntegrable (fun t : ℝ => abs (Real.log |t - c|)) volume a b := by
  have h1 : IntervalIntegrable (fun u : ℝ => Real.log u) volume (a - c) (b - c) :=
    intervalIntegral.intervalIntegrable_log'
  have h2 : IntervalIntegrable (fun u : ℝ => |Real.log u|) volume (a - c) (b - c) := h1.abs
  have h3 := h2.comp_sub_right c
  simp only [sub_add_cancel] at h3
  refine h3.congr_ae ?_
  filter_upwards with t
  simp [Real.log_abs]

set_option maxHeartbeats 1600000 in
private theorem fejer_explicit_formula_upper
    (hJ : ∀ᶠ n : ℕ in atTop, JVal n ≤ 4 * (Real.sqrt n / Real.log n))
    (hRH : ∀ s : ℂ, 1 / 2 < s.re → L4 s ≠ 0)
    (T : ℝ) (Z : Finset ℝ) (hT : 2 ≤ T)
    (hZ : ∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0) :
    ∀ᶠ k : ℕ in atTop,
      (∑ g ∈ Z, let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (-g / T) : ℂ)
                ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
                  ((1 - g / T) * (-(v.re / 2 + g * v.im)) / (1 / 4 + g ^ 2))) ≤ 3 := by
  classical
  have hTpos : 0 < T := by linarith
  -- Step 6a: Global holomorphic logarithm logL4 on Hhalf = {s | 1/2 < s.re}
  let Hhalf : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  have hH_open : IsOpen Hhalf := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hH_conv : Convex ℝ Hhalf := convex_halfSpace_re_gt (1 / 2)
  have h2_mem : (2 : ℂ) ∈ Hhalf := by simp [Hhalf]; norm_num
  obtain ⟨r2, hr2pos, hr2eq, _⟩ := L4_real_pos (by norm_num : (0 : ℝ) < 2)
  have hL4_2_eq : L4 (2 : ℂ) = (r2 : ℂ) := by simpa using hr2eq
  have hv0 : Complex.exp ((Real.log r2 : ℝ) : ℂ) = L4 (2 : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr2pos, hL4_2_eq]
  obtain ⟨logL4, hlogL4_2, hlogL4_deriv, hlogL4_exp⟩ :=
    exists_holomorphic_log_on_convex hH_open hH_conv h2_mem
      L4_differentiable.differentiableOn hRH ((Real.log r2 : ℝ) : ℂ) hv0
  have hlogL4_diff : DifferentiableOn ℂ logL4 Hhalf := fun s hs =>
    (hlogL4_deriv s hs).differentiableAt.differentiableWithinAt
  -- Identify logL4 s = s * ∫_{Ioi 0} jExp u * exp(-s*u) for Re(s) > 1
  have hlogL4_eq_lap : ∀ s : ℂ, 1 < s.re →
      logL4 s = s * ∫ u in Set.Ioi (0 : ℝ), (jExp u : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
    let F : ℂ → ℂ := fun s => s * ∫ u in Set.Ioi (0 : ℝ), (jExp u : ℂ) * Complex.exp (-(s * (u : ℂ)))
    have hH1_open : IsOpen {s : ℂ | 1 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    have hH1_conv : Convex ℝ {s : ℂ | 1 < s.re} := convex_halfSpace_re_gt 1
    have hF_diff : DifferentiableOn ℂ F {s : ℂ | 1 < s.re} := fun s hs =>
      ((hasDerivAt_id s).mul (hasDerivAt_laplace_jExp hs)).differentiableAt.differentiableWithinAt
    have hF_deriv : ∀ s : ℂ, 1 < s.re → HasDerivAt F (deriv L4 s / L4 s) s := by
      intro s hs
      have h1 : HasDerivAt (fun w => Complex.exp (F w)) (Complex.exp (F s) * deriv F s) s :=
        ((hF_diff.differentiableAt (hH1_open.mem_nhds hs)).hasDerivAt).cexp
      have h2 : HasDerivAt (fun w => Complex.exp (F w)) (deriv L4 s) s := by
        refine (L4_differentiable s).hasDerivAt.congr_of_eventuallyEq ?_
        filter_upwards [hH1_open.mem_nhds hs] with w hw
        exact (L4_eq_exp_mul_laplace_jExp hw).symm
      have heq := h1.unique h2
      rw [← L4_eq_exp_mul_laplace_jExp hs] at heq
      have hne := hRH s (by linarith)
      have hdv : deriv F s = deriv L4 s / L4 s := by
        field_simp [hne]; linear_combination heq
      rw [← hdv]
      exact (hF_diff.differentiableAt (hH1_open.mem_nhds hs)).hasDerivAt
    have hdiff_zero : ∀ s ∈ {s : ℂ | 1 < s.re},
        HasDerivAt (fun w => logL4 w - F w) 0 s := fun s hs => by
      have hsre : 1 < s.re := hs
      have h1 := (hlogL4_deriv s (show 1 / 2 < s.re by linarith)).sub (hF_deriv s hsre)
      rwa [sub_self] at h1
    have hF2 : F (2 : ℂ) = logL4 (2 : ℂ) := by
      have hint_real : IntegrableOn (fun u : ℝ => jExp u * Real.exp (-2 * u)) (Set.Ioi (0 : ℝ)) := by
        refine (integrableOn_jExp_pow_exp 0 (by norm_num : (1 : ℝ) < 2)).mono'
          ((measurable_jExp.mul (by fun_prop)).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_zero, mul_one]
      have hF2_real : F (2 : ℂ) = ((2 * ∫ u in Set.Ioi (0 : ℝ), jExp u * Real.exp (-2 * u) : ℝ) : ℂ) := by
        dsimp [F]
        have heq_fn : (fun u : ℝ => (jExp u : ℂ) * Complex.exp (-((2 : ℂ) * (u : ℂ)))) =
            fun u : ℝ => ((jExp u * Real.exp (-2 * u) : ℝ) : ℂ) := by
          ext u; rw [Complex.ofReal_mul, Complex.ofReal_exp]; congr 2; push_cast; ring
        rw [heq_fn, integral_ofReal_eq hint_real]
        simp
      have hexp2 := L4_eq_exp_mul_laplace_jExp (s := (2 : ℂ)) (by simp)
      change L4 (2 : ℂ) = Complex.exp (F (2 : ℂ)) at hexp2
      rw [hF2_real, ← Complex.ofReal_exp, hL4_2_eq] at hexp2
      have hreal_eq : Real.exp (2 * ∫ u in Set.Ioi (0 : ℝ), jExp u * Real.exp (-2 * u)) = r2 :=
        Complex.ofReal_injective hexp2.symm
      have hlog_eq : 2 * ∫ u in Set.Ioi (0 : ℝ), jExp u * Real.exp (-2 * u) = Real.log r2 := by
        rw [← hreal_eq, Real.log_exp]
      rw [hF2_real, hlog_eq, hlogL4_2]
    intro s hs
    have hconst := hH1_conv.is_const_of_fderivWithin_eq_zero
      (f := fun w => logL4 w - F w)
      (fun w hw => (hdiff_zero w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [fderivWithin_of_isOpen hH1_open hw, (hdiff_zero w hw).hasFDerivAt.fderiv]; simp)
      hs (by simp : (1 : ℝ) < (2 : ℂ).re)
    rw [hF2, sub_self] at hconst
    exact sub_eq_zero.mp hconst
  -- Differentiate logL4 s / s = ∫_{Ioi 0} jExp u * exp(-s*u) on Re(s) > 1
  have huJ_eq : ∀ s : ℂ, 1 < s.re →
      ∫ u in Set.Ioi (0 : ℝ), ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
        -(deriv L4 s / (s * L4 s)) + logL4 s / s ^ 2 := by
    intro s hs
    have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    have h1 := hasDerivAt_laplace_jExp hs
    have h2 : HasDerivAt (fun w : ℂ => logL4 w / w)
        ((deriv L4 s / L4 s * s - logL4 s * 1) / s ^ 2) s :=
      (hlogL4_deriv s (by change 1 / 2 < s.re; linarith)).div (hasDerivAt_id s) hsne
    have h2' : HasDerivAt (fun w : ℂ => ∫ u in Set.Ioi (0 : ℝ), (jExp u : ℂ) * Complex.exp (-(w * (u : ℂ))))
        ((deriv L4 s / L4 s * s - logL4 s * 1) / s ^ 2) s := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs] with w hw
      have hwre : 1 < w.re := hw
      have hwne : w ≠ 0 := fun h => by rw [h, zero_re] at hwre; linarith
      rw [hlogL4_eq_lap w hwre, mul_div_cancel_left₀ _ hwne]
    have heq := h1.unique h2'
    have hLne := hRH s (by linarith)
    have hneg : ∫ u in Set.Ioi (0 : ℝ), ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
        -((deriv L4 s / L4 s * s - logL4 s * 1) / s ^ 2) := by
      linear_combination -heq
    rw [hneg]
    field_simp [hsne, hLne]; ring
  -- Step 6b: Non-negative regularized function Gfun on Ioi u1 and Tonelli extension to Hhalf
  obtain ⟨N0_raw, hN0_raw⟩ := Filter.eventually_atTop.mp hJ
  let N0 : ℕ := max N0_raw 3
  have hN0_3 : 3 ≤ N0 := le_max_right _ _
  have hN0_J : ∀ n : ℕ, N0 ≤ n → JVal n ≤ 4 * (Real.sqrt n / Real.log n) :=
    fun n hn => hN0_raw n (le_trans (le_max_left _ _) hn)
  let u1 : ℝ := max (Real.log (N0 : ℝ)) 40
  have hu1_ge40 : 40 ≤ u1 := le_max_right _ _
  have hu1_pos : 0 < u1 := by linarith
  let Gfun : ℝ → ℝ := fun u => (41 / 10 : ℝ) * Real.exp (u / 2) - u * jExp u
  have hG_meas : Measurable Gfun :=
    (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_id.div_const 2))).sub
      (measurable_id.mul measurable_jExp)
  have hG_nonneg : ∀ u ∈ Set.Ioi u1, 0 ≤ Gfun u := by
    intro u hu
    have hu40 : 40 ≤ u := le_trans hu1_ge40 (Set.mem_Ioi.mp hu).le
    have hupos : 0 < u := by linarith
    have hN0_le_exp : (N0 : ℝ) ≤ Real.exp u := by
      have h1 : Real.log (N0 : ℝ) ≤ u := le_trans (le_max_left _ _) (Set.mem_Ioi.mp hu).le
      have hN0pos : (0 : ℝ) < (N0 : ℝ) := by positivity
      simpa [Real.exp_log hN0pos] using Real.exp_le_exp.mpr h1
    have hfl_ge : N0 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor hN0_le_exp
    have hJhi := hN0_J ⌊Real.exp u⌋₊ hfl_ge
    have hfl_pos : (0 : ℝ) < (⌊Real.exp u⌋₊ : ℝ) := by
      have : (3 : ℝ) ≤ (⌊Real.exp u⌋₊ : ℝ) := by exact_mod_cast (le_trans hN0_3 hfl_ge)
      linarith
    have hsqrt_le : Real.sqrt (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp (u / 2) := by
      have h1 : (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
      have h2 := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
        rw [show Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) by
          rw [← Real.exp_add]; congr 1; ring, Real.sqrt_mul_self (Real.exp_pos _).le]
      rwa [h3] at h2
    have hfl_gt_half : Real.exp u / 2 ≤ (⌊Real.exp u⌋₊ : ℝ) := by
      have h1 : Real.exp u - 1 ≤ (⌊Real.exp u⌋₊ : ℝ) := (Nat.sub_one_lt_floor (Real.exp u)).le
      have h2 : (2 : ℝ) ≤ Real.exp u := by
        have := Real.add_one_le_exp u
        linarith
      linarith
    have hlog_ge : (40 / 41 : ℝ) * u ≤ Real.log (⌊Real.exp u⌋₊ : ℝ) := by
      have h1 := Real.log_le_log (by positivity : 0 < Real.exp u / 2) hfl_gt_half
      rw [Real.log_div (Real.exp_pos u).ne' two_ne_zero, Real.log_exp] at h1
      have hlog2 : Real.log 2 < 40 / 41 := by
        have h := Real.log_two_lt_d9
        linarith
      linarith
    have hlog_pos : 0 < Real.log (⌊Real.exp u⌋₊ : ℝ) := by linarith
    have hfrac : 4 * (Real.sqrt (⌊Real.exp u⌋₊ : ℝ) / Real.log (⌊Real.exp u⌋₊ : ℝ)) ≤
        (41 / 10 : ℝ) * Real.exp (u / 2) / u := by
      calc
        4 * (Real.sqrt (⌊Real.exp u⌋₊ : ℝ) / Real.log (⌊Real.exp u⌋₊ : ℝ))
            ≤ 4 * (Real.exp (u / 2) / ((40 / 41 : ℝ) * u)) :=
              mul_le_mul_of_nonneg_left
                (div_le_div₀ (Real.exp_pos _).le hsqrt_le (by positivity) hlog_ge) (by norm_num)
        _ = (41 / 10 : ℝ) * Real.exp (u / 2) / u := by field_simp [hupos.ne']; ring
    dsimp [Gfun, jExp]
    have hmul := mul_le_mul_of_nonneg_left (le_trans hJhi hfrac) hupos.le
    rw [mul_div_cancel₀ _ hupos.ne'] at hmul
    linarith
  -- Analytic right-hand side Phi(s) on Hhalf
  let Phi : ℂ → ℂ := fun s =>
    (deriv L4 s / (s * L4 s)) - logL4 s / s ^ 2 +
      (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ)))) +
      (41 / 10 : ℂ) * (Complex.exp (-((s - 1 / 2) * (u1 : ℂ))) / (s - 1 / 2))
  have hint_fin_diff : Differentiable ℂ
      (fun s : ℂ => ∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ)))) := by
    intro s0
    let F : ℂ → ℝ → ℂ := fun s u => ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ)))
    let F' : ℂ → ℝ → ℂ := fun s u => -(((u ^ 2 * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))))
    have hmeas_F : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Set.Ioc 0 u1)) := fun s =>
      ((Complex.continuous_ofReal.measurable.comp (measurable_id.mul measurable_jExp)).mul
        (by fun_prop)).aestronglyMeasurable
    have hmeas_F' : AEStronglyMeasurable (F' s0) (volume.restrict (Set.Ioc 0 u1)) :=
      (((Complex.continuous_ofReal.measurable.comp ((measurable_id.pow_const 2).mul measurable_jExp)).mul
        (by fun_prop)).neg).aestronglyMeasurable
    let B : ℝ := u1 ^ 2 * Real.exp u1 * Real.exp ((‖s0‖ + 1) * u1)
    have hF_int : IntegrableOn (F s0) (Set.Ioc 0 u1) := by
      refine (integrableOn_const (C := u1 * Real.exp u1 * Real.exp (‖s0‖ * u1))
        (hs := measure_Ioc_lt_top.ne)).mono' (hmeas_F s0) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 ≤ u := hu.1.le
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0, Complex.norm_exp,
        neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      have hre_le : -(s0.re * u) ≤ ‖s0‖ * u1 := by
        have h1 : -s0.re ≤ ‖s0‖ := by
          have := (abs_le.mp (Complex.abs_re_le_norm s0)).1; linarith
        nlinarith [hu.2, norm_nonneg s0]
      exact mul_le_mul (mul_le_mul hu.2 ((abs_jExp_le u).trans (Real.exp_le_exp.mpr hu.2))
        (abs_nonneg _) hu1_pos.le) (Real.exp_le_exp.mpr hre_le) (Real.exp_pos _).le (by positivity)
    have hdiff := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
      (bound := fun _ => B)
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
      (Filter.Eventually.of_forall hmeas_F) hF_int hmeas_F'
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu s hs
        have hu0 : 0 ≤ u := hu.1.le
        have hsnorm : ‖s‖ ≤ ‖s0‖ + 1 := by
          have h1 : ‖s - s0‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
          calc ‖s‖ = ‖(s - s0) + s0‖ := by ring_nf
            _ ≤ ‖s - s0‖ + ‖s0‖ := norm_add_le _ _
            _ ≤ ‖s0‖ + 1 := by linarith
        dsimp [F', B]
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg u), Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
          mul_zero, sub_zero]
        have hre_le : -(s.re * u) ≤ (‖s0‖ + 1) * u1 := by
          have h1 : -s.re ≤ ‖s‖ := by
            have := (abs_le.mp (Complex.abs_re_le_norm s)).1; linarith
          nlinarith [hu.2, norm_nonneg s]
        exact mul_le_mul
          (mul_le_mul (pow_le_pow_left₀ hu0 hu.2 2) ((abs_jExp_le u).trans (Real.exp_le_exp.mpr hu.2))
            (abs_nonneg _) (sq_nonneg u1))
          (Real.exp_le_exp.mpr hre_le) (Real.exp_pos _).le (by positivity))
      (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u _ s _
        dsimp [F, F']
        have h1 := hasDerivAt_neg_mul_const s (u : ℂ)
        have h2 := h1.cexp.const_mul ((u * jExp u : ℝ) : ℂ)
        refine h2.congr_deriv ?_
        push_cast; ring)).2
    exact hdiff.differentiableAt
  have hPhi_diff : DifferentiableOn ℂ Phi Hhalf := by
    intro s hs
    have hsre : 1 / 2 < s.re := hs
    have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hsre; linarith
    have hs_half_ne : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hLne := hRH s hsre
    have h1 : DifferentiableAt ℂ (fun w => deriv L4 w / (w * L4 w)) s :=
      (L4_differentiable.deriv s).div ((differentiableAt_id).mul (L4_differentiable s))
        (mul_ne_zero hsne hLne)
    have h2 : DifferentiableAt ℂ (fun w => logL4 w / w ^ 2) s :=
      (hlogL4_diff.differentiableAt (hH_open.mem_nhds hs)).div (differentiableAt_id.pow 2)
        (pow_ne_zero 2 hsne)
    have h3 : DifferentiableAt ℂ
        (fun w => (41 / 10 : ℂ) * (Complex.exp (-((w - 1 / 2) * (u1 : ℂ))) / (w - 1 / 2))) s := by
      refine (differentiableAt_const _).mul ?_
      refine ((((differentiableAt_id.sub (differentiableAt_const _)).mul
        (differentiableAt_const _)).neg).cexp).div
        (differentiableAt_id.sub (differentiableAt_const _)) hs_half_ne
    exact (((h1.sub h2).add (hint_fin_diff s)).add h3).differentiableWithinAt
  -- For Re(s) > 1, Phi s = ∫_{Ioi u1} Gfun u * exp(-s*u)
  have hPhi_eq_G_gt1 : ∀ s : ℂ, 1 < s.re →
      Phi s = ∫ u in Set.Ioi u1, (Gfun u : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
    intro s hs
    have hint_uJ : IntegrableOn (fun u : ℝ => ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))))
        (Set.Ioi (0 : ℝ)) := by
      refine (integrableOn_jExp_pow_exp 1 hs).mono'
        (((Complex.continuous_ofReal.measurable.comp (measurable_id.mul measurable_jExp)).mul
          (by fun_prop)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := (Set.mem_Ioi.mp hu).le
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0, Complex.norm_exp,
        neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, pow_one, neg_mul]
      linarith [mul_comm u |jExp u|]
    have hsplit : ∫ u in Set.Ioi (0 : ℝ), ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
        (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ)))) +
        (∫ u in Set.Ioi u1, ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ)))) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hu1_pos.le,
        setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hint_uJ.mono_set Set.Ioc_subset_Ioi_self)
          (hint_uJ.mono_set (Set.Ioi_subset_Ioi hu1_pos.le))]
    have hexp_int : ∫ u in Set.Ioi u1,
        ((41 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
        (41 / 10 : ℂ) * (Complex.exp (-((s - 1 / 2) * (u1 : ℂ))) / (s - 1 / 2)) := by
      have hcongr : ∀ u : ℝ,
          (((41 / 10 : ℝ) * Real.exp (u / 2) : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
          (41 / 10 : ℂ) * Complex.exp ((-(s - 1 / 2)) * (u : ℂ)) := fun u => by
        rw [Complex.ofReal_mul, Complex.ofReal_exp]
        push_cast
        rw [mul_assoc, ← Complex.exp_add]
        congr 2; ring
      have hcongr' : Set.EqOn
          (fun u : ℝ => ((41 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))))
          (fun u : ℝ => (41 / 10 : ℂ) * Complex.exp ((-(s - 1 / 2)) * (u : ℂ))) (Set.Ioi u1) := by
        intro u _; simpa using hcongr u
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr', integral_const_mul,
        integral_exp_mul_complex_Ioi (by simp; linarith) u1]
      congr 1
      have hsne : s - 1 / 2 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      field_simp [hsne]
    have hint_exp_half : IntegrableOn
        (fun u : ℝ => ((41 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))))
        (Set.Ioi u1) := by
      have h1 := (integrableOn_exp_mul_complex_Ioi (a := -(s - 1 / 2)) (by simp; linarith) u1).const_mul
        (41 / 10 : ℂ)
      refine IntegrableOn.congr_fun h1 (fun u _ => ?_) measurableSet_Ioi
      have : (41 / 10 : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ)) =
          ((41 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
        rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
        push_cast; congr 2; ring
      simpa using this
    have hG_split : (fun u : ℝ => (Gfun u : ℂ) * Complex.exp (-(s * (u : ℂ)))) =
        fun u : ℝ => ((41 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))) -
          ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
      ext u; dsimp [Gfun]; push_cast; ring
    rw [hG_split, integral_sub hint_exp_half (hint_uJ.mono_set (Set.Ioi_subset_Ioi hu1_pos.le)),
      hexp_int]
    dsimp [Phi]
    have h3 := huJ_eq s hs
    rw [hsplit] at h3
    linear_combination h3
  -- Iterated derivatives of Phi at s = 2 via induction on k
  have hG_pow_int : ∀ (k : ℕ) {σ : ℝ}, 1 < σ →
      IntegrableOn (fun u : ℝ => |Gfun u| * u ^ k * Real.exp (-σ * u)) (Set.Ioi u1) := by
    intro k σ hσ
    have h1 := (integrableOn_jExp_pow_exp (k + 1) hσ).mono_set (Set.Ioi_subset_Ioi hu1_pos.le)
    have h2 : IntegrableOn (fun u : ℝ => (41 / 10 : ℝ) * Real.exp (u / 2) * u ^ k * Real.exp (-σ * u))
        (Set.Ioi u1) := by
      have hδ : 0 < (σ - 1 / 2) / 2 := by linarith
      have hdom : IntegrableOn
          (fun u : ℝ => (41 / 10 : ℝ) * ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) *
            Real.exp (-((σ - 1 / 2) / 2) * u)) (Set.Ioi u1) :=
        (integrableOn_exp_mul_Ioi (by linarith) u1).const_mul _
      refine hdom.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
      rw [Real.norm_of_nonneg (by positivity)]
      have hpow_le : (((σ - 1 / 2) / 2) * u) ^ k / (k ! : ℝ) ≤ Real.exp (((σ - 1 / 2) / 2) * u) :=
        Real.pow_div_factorial_le_exp _ (by positivity) k
      have hu_le : u ^ k ≤ ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) * Real.exp (((σ - 1 / 2) / 2) * u) := by
        rw [mul_pow] at hpow_le
        have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
        have hdk : (0 : ℝ) < ((σ - 1 / 2) / 2) ^ k := by positivity
        rw [div_le_iff₀ hfac] at hpow_le
        rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
        nlinarith
      calc
        (41 / 10 : ℝ) * Real.exp (u / 2) * u ^ k * Real.exp (-σ * u)
            ≤ (41 / 10 : ℝ) * Real.exp (u / 2) *
                (((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) * Real.exp (((σ - 1 / 2) / 2) * u)) *
                Real.exp (-σ * u) := by
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hu_le (by positivity)) (Real.exp_pos _).le
        _ = (41 / 10 : ℝ) * ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) *
              (Real.exp (u / 2) * Real.exp (((σ - 1 / 2) / 2) * u) * Real.exp (-σ * u)) := by ring
        _ = (41 / 10 : ℝ) * ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) *
              Real.exp (-((σ - 1 / 2) / 2) * u) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
    refine (h1.add h2).mono' ((hG_meas.abs.mul (measurable_id.pow_const k)).mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
    rw [Real.norm_of_nonneg (by positivity)]
    have habs : |Gfun u| ≤ u * |jExp u| + (41 / 10 : ℝ) * Real.exp (u / 2) := by
      dsimp [Gfun]
      calc
        |(41 / 10 : ℝ) * Real.exp (u / 2) - u * jExp u|
            ≤ |(41 / 10 : ℝ) * Real.exp (u / 2)| + |u * jExp u| := abs_sub _ _
        _ = u * |jExp u| + (41 / 10 : ℝ) * Real.exp (u / 2) := by
              rw [abs_of_pos (mul_pos (by norm_num) (Real.exp_pos (u / 2))), abs_mul, abs_of_nonneg hu0]; ring
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs (pow_nonneg hu0 k))
      (Real.exp_pos (-σ * u)).le
    have hlhs : (u * |jExp u| + (41 / 10 : ℝ) * Real.exp (u / 2)) * u ^ k * Real.exp (-σ * u) =
        |jExp u| * u ^ (k + 1) * Real.exp (-σ * u) +
          (41 / 10 : ℝ) * Real.exp (u / 2) * u ^ k * Real.exp (-σ * u) := by rw [pow_succ]; ring
    exact hmul.trans_eq hlhs
  have hPhi_iterDeriv : ∀ (k : ℕ) (s : ℂ), 1 < s.re →
      iteratedDeriv k Phi s =
        (-1 : ℂ) ^ k * ∫ u in Set.Ioi u1, (Gfun u : ℂ) * (u : ℂ) ^ k * Complex.exp (-(s * (u : ℂ))) := by
    intro k
    induction k with
    | zero =>
      intro s hs; simp [iteratedDeriv_zero, hPhi_eq_G_gt1 s hs]
    | succ k ih =>
      intro s0 hs0
      rw [iteratedDeriv_succ]
      set δ : ℝ := (s0.re - 1) / 2
      have hδ : 0 < δ := by dsimp [δ]; linarith
      let σ0 : ℝ := 1 + δ
      have hσ0 : 1 < σ0 := by dsimp [σ0]; linarith
      have hre_ge : ∀ s ∈ Metric.ball s0 δ, σ0 ≤ s.re := by
        intro s hs
        have h1 : |s.re - s0.re| ≤ ‖s - s0‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - s0)
        have h2 : ‖s - s0‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
        dsimp [σ0, δ] at *; linarith
      let F : ℂ → ℝ → ℂ := fun s u => (Gfun u : ℂ) * (u : ℂ) ^ k * Complex.exp (-(s * (u : ℂ)))
      let F' : ℂ → ℝ → ℂ := fun s u => -((Gfun u : ℂ) * (u : ℂ) ^ (k + 1) * Complex.exp (-(s * (u : ℂ))))
      have hF_meas : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Set.Ioi u1)) := fun s =>
        (((Complex.continuous_ofReal.measurable.comp hG_meas).mul (by fun_prop)).mul
          (by fun_prop)).aestronglyMeasurable
      have hF'_meas : AEStronglyMeasurable (F' s0) (volume.restrict (Set.Ioi u1)) :=
        ((((Complex.continuous_ofReal.measurable.comp hG_meas).mul (by fun_prop)).mul
          (by fun_prop)).neg).aestronglyMeasurable
      have hF_int : IntegrableOn (F s0) (Set.Ioi u1) := by
        refine (hG_pow_int k hs0).mono' (hF_meas s0) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
        dsimp [F]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hu0, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
          mul_zero, sub_zero, neg_mul]
      have hdiff := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
        (bound := fun u => |Gfun u| * u ^ (k + 1) * Real.exp (-σ0 * u))
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
        (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s hs
          have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
          have hre := hre_ge s hs
          dsimp [F']
          rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
            Complex.norm_real, Real.norm_of_nonneg hu0, Complex.norm_exp, neg_re, mul_re,
            ofReal_re, ofReal_im, mul_zero, sub_zero, neg_mul]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity))
        (hG_pow_int (k + 1) hσ0)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ s _
          dsimp [F, F']
          have h1 := hasDerivAt_neg_mul_const s (u : ℂ)
          have h2 := h1.cexp.const_mul ((Gfun u : ℂ) * (u : ℂ) ^ k)
          refine h2.congr_deriv ?_
          rw [pow_succ]; ring)).2
      have hcongr : deriv (iteratedDeriv k Phi) s0 =
          deriv (fun s => (-1 : ℂ) ^ k * ∫ u in Set.Ioi u1, F s u) s0 := by
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs0] with w hw
        exact ih w hw
      rw [hcongr, (hdiff.const_mul ((-1 : ℂ) ^ k)).deriv]
      dsimp [F']
      rw [integral_neg, pow_succ]; ring
  -- Tonelli theorem: Gfun u * exp(-σ * u) is integrable on Ioi u1 for ALL σ > 1/2!
  have hG_int_half : ∀ σ : ℝ, 1 / 2 < σ →
      IntegrableOn (fun u : ℝ => Gfun u * Real.exp (-σ * u)) (Set.Ioi u1) := by
    intro σ hσ
    by_cases hσ1 : 1 < σ
    · refine (hG_pow_int 0 hσ1).mono' ((hG_meas.mul (by fun_prop)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_of_nonneg (mul_nonneg (hG_nonneg u hu) (Real.exp_pos _).le),
        abs_of_nonneg (hG_nonneg u hu), pow_zero, mul_one]
    · push Not at hσ1
      have h2σ : 0 ≤ 2 - σ := by linarith
      have hball_sub : Metric.ball (2 : ℂ) (3 / 2) ⊆ Hhalf := by
        intro z hz
        have h1 : |z.re - (2 : ℂ).re| ≤ ‖z - 2‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - 2)
        have h2 : ‖z - 2‖ < 3 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
        change 1 / 2 < z.re; simp at h3; linarith
      have hσ_mem : (σ : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
        rw [Metric.mem_ball, dist_eq_norm, show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        linarith
      have hts := (Complex.hasSum_taylorSeries_on_ball (hPhi_diff.mono hball_sub) hσ_mem).summable
      have hre_sum : Summable (fun k : ℕ =>
          ((2 - σ) ^ k / (k ! : ℝ)) * ∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u)) := by
        refine (Complex.reCLM.summable hts).congr fun k => ?_
        have hiter := hPhi_iterDeriv k (2 : ℂ) (by simp)
        have hint_k : IntegrableOn (fun u : ℝ => Gfun u * u ^ k * Real.exp (-2 * u)) (Set.Ioi u1) := by
          refine (hG_pow_int k (by norm_num : (1 : ℝ) < 2)).mono'
            (((hG_meas.mul (measurable_id.pow_const k)).mul (by fun_prop)).aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
          rw [Real.norm_of_nonneg (by positivity [hG_nonneg u hu]), abs_of_nonneg (hG_nonneg u hu)]
        have hofR : ∫ u in Set.Ioi u1, (Gfun u : ℂ) * (u : ℂ) ^ k * Complex.exp (-((2 : ℂ) * (u : ℂ))) =
            ((∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u) : ℝ) : ℂ) := by
          have hfn : (fun u : ℝ => (Gfun u : ℂ) * (u : ℂ) ^ k * Complex.exp (-((2 : ℂ) * (u : ℂ)))) =
              fun u : ℝ => ((Gfun u * u ^ k * Real.exp (-2 * u) : ℝ) : ℂ) := by
            ext u; rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
            congr 2; push_cast; ring
          rw [hfn, integral_ofReal_eq hint_k]
        rw [hiter, hofR, smul_eq_mul, smul_eq_mul]
        have hsub : ((σ : ℂ) - 2) ^ k * (-1 : ℂ) ^ k = (((2 - σ) ^ k : ℝ) : ℂ) := by
          rw [← mul_pow]; push_cast; congr 1; ring
        have hterm : ((k ! : ℂ)⁻¹ * (((σ : ℂ) - 2) ^ k * ((-1 : ℂ) ^ k *
            ((∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u) : ℝ) : ℂ)))) =
            ((((2 - σ) ^ k / (k ! : ℝ)) *
              ∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u) : ℝ) : ℂ) := by
          have : (k ! : ℂ)⁻¹ * (((σ : ℂ) - 2) ^ k * ((-1 : ℂ) ^ k *
              ((∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u) : ℝ) : ℂ))) =
              (((σ : ℂ) - 2) ^ k * (-1 : ℂ) ^ k) * (k ! : ℂ)⁻¹ *
              ((∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u) : ℝ) : ℂ) := by ring
          rw [this, hsub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, div_eq_mul_inv]
        change (Complex.reCLM _ ) = _
        rw [hterm, Complex.reCLM_apply, Complex.ofReal_re]
      have hlint : ∫⁻ u in Set.Ioi u1, ENNReal.ofReal (Gfun u * Real.exp (-σ * u)) < ⊤ := by
        have hpoint : ∀ u ∈ Set.Ioi u1,
            ENNReal.ofReal (Gfun u * Real.exp (-σ * u)) =
            ∑' k : ℕ, ENNReal.ofReal
              (((2 - σ) ^ k / (k ! : ℝ)) * (Gfun u * u ^ k * Real.exp (-2 * u))) := by
          intro u hu
          have hG0 := hG_nonneg u hu
          have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
          have hhs : HasSum (fun k : ℕ =>
              ((2 - σ) ^ k / (k ! : ℝ)) * (Gfun u * u ^ k * Real.exp (-2 * u)))
              (Gfun u * Real.exp (-σ * u)) := by
            have hexp := (Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp ((2 - σ) * u))
            have hmul := hexp.mul_right (Gfun u * Real.exp (-2 * u))
            have hlim : Real.exp ((2 - σ) * u) * (Gfun u * Real.exp (-2 * u)) = Gfun u * Real.exp (-σ * u) := by
              rw [← mul_assoc, mul_comm (Real.exp ((2 - σ) * u)), mul_assoc, ← Real.exp_add]
              congr 2; ring
            rw [hlim] at hmul
            refine hmul.congr_fun fun k => ?_
            rw [mul_pow]; ring
          rw [← hhs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hhs.summable]
        rw [setLIntegral_congr_fun measurableSet_Ioi hpoint,
          lintegral_tsum (fun k => (by fun_prop : Measurable fun u =>
            ENNReal.ofReal (((2 - σ) ^ k / (k ! : ℝ)) * (Gfun u * u ^ k * Real.exp (-2 * u)))).aemeasurable)]
        have hterm_eq : ∀ k : ℕ,
            ∫⁻ u in Set.Ioi u1, ENNReal.ofReal
              (((2 - σ) ^ k / (k ! : ℝ)) * (Gfun u * u ^ k * Real.exp (-2 * u))) =
            ENNReal.ofReal (((2 - σ) ^ k / (k ! : ℝ)) *
              ∫ u in Set.Ioi u1, Gfun u * u ^ k * Real.exp (-2 * u)) := by
          intro k
          have hint_k : IntegrableOn (fun u : ℝ => Gfun u * u ^ k * Real.exp (-2 * u)) (Set.Ioi u1) := by
            refine (hG_pow_int k (by norm_num : (1 : ℝ) < 2)).mono'
              (((hG_meas.mul (measurable_id.pow_const k)).mul (by fun_prop)).aestronglyMeasurable) ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
            rw [Real.norm_of_nonneg (by positivity [hG_nonneg u hu]), abs_of_nonneg (hG_nonneg u hu)]
          rw [← ofReal_integral_eq_lintegral_ofReal (hint_k.const_mul _)]
          · rw [integral_const_mul]
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
            have := hG_nonneg u hu
            positivity
        simp_rw [hterm_eq]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by
          refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun u hu => ?_)
          have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
          have := hG_nonneg u hu
          positivity) hre_sum]
        exact ENNReal.ofReal_lt_top
      refine ⟨(hG_meas.mul (by fun_prop)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal]
      · exact hlint
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_nonneg (hG_nonneg u hu) (Real.exp_pos _).le
  -- Analytic continuation of Phi s = ∫_{Ioi u1} Gfun u * exp(-s*u) to ALL of Hhalf!
  have hPhi_eq_G : ∀ s ∈ Hhalf,
      Phi s = ∫ u in Set.Ioi u1, (Gfun u : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
    let Psi : ℂ → ℂ := fun s => ∫ u in Set.Ioi u1, (Gfun u : ℂ) * Complex.exp (-(s * (u : ℂ)))
    have hPsi_diff : DifferentiableOn ℂ Psi Hhalf := by
      intro s0 hs0
      have hs0re : 1 / 2 < s0.re := hs0
      set δ : ℝ := (s0.re - 1 / 2) / 3
      have hδ : 0 < δ := by dsimp [δ]; linarith
      let σ1 : ℝ := 1 / 2 + δ
      let σ2 : ℝ := 1 / 2 + 2 * δ
      have hσ1 : 1 / 2 < σ1 := by dsimp [σ1]; linarith
      have hre_ge : ∀ s ∈ Metric.ball s0 δ, σ2 ≤ s.re := by
        intro s hs
        have h1 : |s.re - s0.re| ≤ ‖s - s0‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - s0)
        have h2 : ‖s - s0‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
        dsimp [σ2, δ] at *; linarith
      let F : ℂ → ℝ → ℂ := fun s u => (Gfun u : ℂ) * Complex.exp (-(s * (u : ℂ)))
      let F' : ℂ → ℝ → ℂ := fun s u => -((Gfun u : ℂ) * (u : ℂ) * Complex.exp (-(s * (u : ℂ))))
      have hF_meas : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Set.Ioi u1)) := fun s =>
        ((Complex.continuous_ofReal.measurable.comp hG_meas).mul (by fun_prop)).aestronglyMeasurable
      have hF'_meas : AEStronglyMeasurable (F' s0) (volume.restrict (Set.Ioi u1)) :=
        ((((Complex.continuous_ofReal.measurable.comp hG_meas).mul (by fun_prop)).mul
          (by fun_prop)).neg).aestronglyMeasurable
      have hF_int : IntegrableOn (F s0) (Set.Ioi u1) := by
        refine (hG_int_half s0.re hs0re).mono' (hF_meas s0) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        dsimp [F]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hG_nonneg u hu), Complex.norm_exp,
          neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_mul]
      have hdom : IntegrableOn (fun u : ℝ => (1 / δ) * (Gfun u * Real.exp (-σ1 * u))) (Set.Ioi u1) :=
        (hG_int_half σ1 hσ1).const_mul (1 / δ)
      have hdiff := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
        (bound := fun u => (1 / δ) * (Gfun u * Real.exp (-σ1 * u)))
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
        (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s hs
          have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
          have hG0 := hG_nonneg u hu
          have hre := hre_ge s hs
          dsimp [F']
          rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hG0,
            Complex.norm_real, Real.norm_of_nonneg hu0, Complex.norm_exp, neg_re, mul_re,
            ofReal_re, ofReal_im, mul_zero, sub_zero]
          have hdu : δ * u ≤ Real.exp (δ * u) := by linarith [Real.add_one_le_exp (δ * u)]
          have hu_le : u ≤ (1 / δ) * Real.exp (δ * u) := by
            rw [one_div_mul_eq_div, le_div_iff₀ hδ]; linarith
          have hexp_le : Real.exp (-(s.re * u)) ≤ Real.exp (-σ2 * u) :=
            Real.exp_le_exp.mpr (by nlinarith)
          calc
            Gfun u * u * Real.exp (-(s.re * u))
                ≤ Gfun u * ((1 / δ) * Real.exp (δ * u)) * Real.exp (-σ2 * u) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hu_le hG0) hexp_le (Real.exp_pos _).le (by positivity)
            _ = (1 / δ) * (Gfun u * (Real.exp (δ * u) * Real.exp (-σ2 * u))) := by ring
            _ = (1 / δ) * (Gfun u * Real.exp (-σ1 * u)) := by
                  rw [← Real.exp_add]; congr 3; dsimp [σ1, σ2]; ring)
        hdom
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ s _
          dsimp [F, F']
          have h1 := hasDerivAt_neg_mul_const s (u : ℂ)
          have h2 := h1.cexp.const_mul (Gfun u : ℂ)
          refine h2.congr_deriv ?_; ring)).2
      exact hdiff.differentiableAt.differentiableWithinAt
    have han1 : AnalyticOnNhd ℂ Phi Hhalf := hPhi_diff.analyticOnNhd hH_open
    have han2 : AnalyticOnNhd ℂ Psi Hhalf := hPsi_diff.analyticOnNhd hH_open
    have hev : Phi =ᶠ[𝓝 (2 : ℂ)] Psi := by
      refine Filter.eventually_of_mem
        ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)) ?_
      intro s hs; exact hPhi_eq_G_gt1 s hs
    exact fun s hs => han1.eqOn_of_preconnected_of_eventuallyEq han2 hH_conv.isPreconnected h2_mem hev hs
  -- Step 6c: Local factorization of L4 on a convex open rectangle containing [1/2 - iT, 1/2 + iT]
  let SZ : Finset ℝ := Z ∪ Z.image Neg.neg
  let mult : ℝ → ℕ := fun g => (analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat
  have hL4_ord_ne_top : ∀ z : ℂ, analyticOrderAt L4 z ≠ ⊤ := by
    intro z htop
    have hev := analyticOrderAt_eq_top.mp htop
    have han : AnalyticOnNhd ℂ L4 Set.univ := L4_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ (2 : ℂ))
    exact L4_real_ne_zero (by norm_num : (0 : ℝ) < 2) (by simpa using h0)
  have hL4_ord_conj : ∀ g : ℝ,
      analyticOrderAt L4 (1 / 2 - (g : ℂ) * Complex.I) =
      analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I) := by
    intro g
    set z : ℂ := 1 / 2 + (g : ℂ) * Complex.I
    set zc : ℂ := 1 / 2 - (g : ℂ) * Complex.I
    have hzc : starRingEnd ℂ z = zc := by
      dsimp [z, zc]
      simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hzc' : starRingEnd ℂ zc = z := by rw [← hzc, Complex.conj_conj]
    have hfin := hL4_ord_ne_top z
    obtain ⟨f, hf_an, hfz, hfeq⟩ := (L4_differentiable.analyticAt z).analyticOrderAt_ne_top.mp hfin
    let n := analyticOrderNatAt L4 z
    have hn_eq : analyticOrderAt L4 z = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt hfin).symm
    let fc : ℂ → ℂ := fun w => starRingEnd ℂ (f (starRingEnd ℂ w))
    have hfc_an : AnalyticAt ℂ fc zc := by
      have hdiff_on : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w :=
        (hf_an.eventually_analyticAt).mono fun w hw => hw.differentiableAt
      obtain ⟨U, hUsub, hUopen, hzU⟩ := eventually_nhds_iff.mp hdiff_on
      have hUc_open : IsOpen (starRingEnd ℂ ⁻¹' U) := hUopen.preimage Complex.continuous_conj
      have hzcU : zc ∈ starRingEnd ℂ ⁻¹' U := by change starRingEnd ℂ zc ∈ U; rwa [hzc']
      have hdiff_c : DifferentiableOn ℂ fc (starRingEnd ℂ ⁻¹' U) := fun w hw =>
        (differentiableAt_conj_comp (hUsub _ hw)).differentiableWithinAt
      exact (DifferentiableOn.analyticOnNhd hdiff_c hUc_open) zc hzcU
    have hfcz : fc zc ≠ 0 := by
      dsimp [fc]; rw [hzc']; exact (map_ne_zero (starRingEnd ℂ)).mpr hfz
    have hfeqc : ∀ᶠ w in 𝓝 zc, L4 w = (w - zc) ^ n • fc w := by
      have hnh : Filter.Tendsto (starRingEnd ℂ) (𝓝 zc) (𝓝 z) := by
        simpa [hzc'] using Complex.continuous_conj.tendsto zc
      filter_upwards [hnh hfeq] with w hw
      have h1 := congrArg (starRingEnd ℂ) hw
      rw [← L4_conj, Complex.conj_conj, smul_eq_mul, map_mul, map_pow, map_sub,
        Complex.conj_conj, hzc] at h1
      simpa [fc, smul_eq_mul] using h1
    rw [hn_eq, (L4_differentiable.analyticAt zc).analyticOrderAt_eq_natCast]
    exact ⟨fc, hfc_an, hfcz, hfeqc⟩
  have hmult_neg : ∀ g : ℝ, mult (-g) = mult g := fun g => by
    dsimp [mult]
    rw [show (1 / 2 : ℂ) + ((-g : ℝ) : ℂ) * Complex.I = 1 / 2 - (g : ℂ) * Complex.I by
      push_cast; ring, hL4_ord_conj]
  have hSZ_mem : ∀ g : ℝ, g ∈ SZ ↔ |g| ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0 := by
    intro g
    constructor
    · intro hg
      rcases Finset.mem_union.mp hg with hgZ | hgN
      · obtain ⟨hg0, hgT, hLz⟩ := (hZ g).mp hgZ
        exact ⟨by rwa [abs_of_pos hg0], hLz⟩
      · obtain ⟨g', hg'Z, rfl⟩ := Finset.mem_image.mp hgN
        obtain ⟨hg0, hgT, hLz⟩ := (hZ g').mp hg'Z
        refine ⟨by rw [abs_neg, abs_of_pos hg0]; exact hgT, ?_⟩
        have hzc : starRingEnd ℂ (1 / 2 + (g' : ℂ) * Complex.I) =
            1 / 2 + ((-g' : ℝ) : ℂ) * Complex.I := by
          simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        rw [← hzc, L4_conj, hLz, map_zero]
    · rintro ⟨hgT, hLz⟩
      rcases lt_trichotomy g 0 with hlt | rfl | hgt
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-g, ?_, neg_neg g⟩)
        rw [hZ]
        have hzc : starRingEnd ℂ (1 / 2 + (g : ℂ) * Complex.I) =
            1 / 2 + ((-g : ℝ) : ℂ) * Complex.I := by
          simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        exact ⟨by linarith, by rw [abs_of_neg hlt] at hgT; exact hgT, by rw [← hzc, L4_conj, hLz, map_zero]⟩
      · exfalso
        have hhalf : L4 (1 / 2 : ℂ) ≠ 0 := by
          simpa using L4_real_ne_zero (by norm_num : (0 : ℝ) < 1 / 2)
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at hLz
        exact hhalf hLz
      · refine Finset.mem_union_left _ ((hZ g).mpr ⟨hgt, by rwa [abs_of_pos hgt] at hgT, hLz⟩)
  have hZ_disj : Disjoint Z (Z.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro g hgZ hgN
    obtain ⟨hg0, _, _⟩ := (hZ g).mp hgZ
    obtain ⟨g', hg'Z, rfl⟩ := Finset.mem_image.mp hgN
    obtain ⟨hg'0, _, _⟩ := (hZ g').mp hg'Z
    linarith
  -- Factored polynomial QZ(s) = ∏_{g ∈ SZ} (s - (1/2 + g*I))^{mult g}
  let QZ : ℂ → ℂ := fun s => ∏ g ∈ SZ, (s - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g
  have hQZ_diff : Differentiable ℂ QZ := fun s =>
    DifferentiableAt.fun_finsetProd fun g _ =>
      ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
  have hQZ_ord : ∀ t ∈ Set.Icc (-T) T,
      analyticOrderAt QZ (1 / 2 + (t : ℂ) * Complex.I) =
      analyticOrderAt L4 (1 / 2 + (t : ℂ) * Complex.I) := by
    intro t ht
    set z : ℂ := 1 / 2 + (t : ℂ) * Complex.I
    have han_fac : ∀ g ∈ SZ,
        AnalyticAt ℂ (fun w : ℂ => (w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) z :=
      fun g _ => (analyticAt_id.sub analyticAt_const).pow _
    rw [analyticOrderAt_finset_prod_aux SZ _ z han_fac]
    have hfac_ord : ∀ g ∈ SZ,
        analyticOrderAt (fun w : ℂ => (w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) z =
        if g = t then (mult t : ℕ∞) else 0 := by
      intro g _
      have hlin : AnalyticAt ℂ (fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I)) z := by fun_prop
      change analyticOrderAt ((fun w : ℂ => w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) z = _
      rw [analyticOrderAt_pow hlin]
      by_cases hgt : g = t
      · subst hgt
        rw [if_pos rfl]
        have h1 : analyticOrderAt (fun w : ℂ => w - z) z = ((1 : ℕ) : ℕ∞) := by
          have hlin' : AnalyticAt ℂ (fun w : ℂ => w - z) z := by fun_prop
          rw [hlin'.analyticOrderAt_eq_natCast]
          exact ⟨fun _ => 1, analyticAt_const, one_ne_zero,
            Filter.Eventually.of_forall fun w => by simp [smul_eq_mul]⟩
        rw [h1, Nat.cast_one, nsmul_eq_mul, mul_one]
      · rw [if_neg hgt]
        have hne : z - (1 / 2 + (g : ℂ) * Complex.I) ≠ 0 := by
          intro h0
          have := congrArg Complex.im h0
          simp [z] at this; exact hgt (by linarith)
        rw [hlin.analyticOrderAt_eq_zero.mpr hne, smul_zero]
    rw [Finset.sum_congr rfl hfac_ord]
    by_cases htSZ : t ∈ SZ
    · rw [Finset.sum_ite_eq' SZ t (fun _ => (mult t : ℕ∞)), if_pos htSZ]
      dsimp [mult]
      exact ENat.natCast_toNat (hL4_ord_ne_top z)
    · rw [Finset.sum_ite_eq' SZ t (fun _ => (mult t : ℕ∞)), if_neg htSZ]
      have hLne : L4 z ≠ 0 := by
        intro h0
        exact htSZ ((hSZ_mem t).mpr ⟨abs_le.mpr ht, h0⟩)
      exact ((L4_differentiable.analyticAt z).analyticOrderAt_eq_zero.mpr hLne).symm
  -- Local quotient Hreg near every point of K = {1/2 + t*I | t ∈ [-T, T]}
  let Kseg : Set ℂ := (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I) '' Set.Icc (-T) T
  have hHreg_loc : ∀ z0 ∈ Kseg, ∃ U : Set ℂ, IsOpen U ∧ z0 ∈ U ∧
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧ ∀ z ∈ U, q z ≠ 0 ∧ L4 z = QZ z * q z := by
    rintro z0 ⟨t, ht, rfl⟩
    set z0 : ℂ := 1 / 2 + (t : ℂ) * Complex.I
    have hord_eq := hQZ_ord t ht
    have hfinL := hL4_ord_ne_top z0
    have hfinQ : analyticOrderAt QZ z0 ≠ ⊤ := hord_eq ▸ hfinL
    obtain ⟨f, hf_an, hfz, hfeq⟩ := (L4_differentiable.analyticAt z0).analyticOrderAt_ne_top.mp hfinL
    obtain ⟨g, hg_an, hgz, hgeq⟩ := (hQZ_diff.analyticAt z0).analyticOrderAt_ne_top.mp hfinQ
    have hneq_ord : analyticOrderNatAt QZ z0 = analyticOrderNatAt L4 z0 := by
      have h1 := Nat.cast_analyticOrderNatAt hfinQ
      have h2 := Nat.cast_analyticOrderNatAt hfinL
      rw [hord_eq] at h1
      exact Nat.cast_injective (h1.trans h2.symm)
    let q : ℂ → ℂ := fun z => f z / g z
    have hq_an : AnalyticAt ℂ q z0 := hf_an.div hg_an hgz
    have hq_ev : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ q z ∧ q z ≠ 0 ∧ L4 z = QZ z * q z := by
      filter_upwards [hq_an.eventually_analyticAt, hq_an.continuousAt.eventually_ne (div_ne_zero hfz hgz),
        hg_an.continuousAt.eventually_ne hgz, hfeq, hgeq] with z hqa hqnz hgnz hfz' hgz'
      refine ⟨hqa.differentiableAt, hqnz, ?_⟩
      rw [hfz', hgz', hneq_ord, smul_eq_mul, smul_eq_mul]
      dsimp [q]; field_simp [hgnz]
    obtain ⟨U, hUsub, hUopen, hz0U⟩ := eventually_nhds_iff.mp hq_ev
    exact ⟨U, hUopen, hz0U, q, fun z hz => (hUsub z hz).1.differentiableWithinAt,
      fun z hz => ⟨(hUsub z hz).2.1, (hUsub z hz).2.2⟩⟩
  -- Build global open neighborhood of Kseg and Hreg on it
  have hHreg_global : ∃ U : Set ℂ, IsOpen U ∧ Kseg ⊆ U ∧
      ∃ Hreg : ℂ → ℂ, DifferentiableOn ℂ Hreg U ∧ ∀ z ∈ U, Hreg z ≠ 0 ∧ L4 z = QZ z * Hreg z := by
    have hU_each : ∀ z0 : Kseg, ∃ U : Set ℂ, IsOpen U ∧ (z0 : ℂ) ∈ U ∧
        ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧ ∀ z ∈ U, q z ≠ 0 ∧ L4 z = QZ z * q z :=
      fun z0 => hHreg_loc z0.1 z0.2
    let Uc : Kseg → Set ℂ := fun z0 => (hU_each z0).choose
    let qc : Kseg → ℂ → ℂ := fun z0 => (hU_each z0).choose_spec.2.2.choose
    let U : Set ℂ := ⋃ z0 : Kseg, Uc z0
    have hUopen : IsOpen U := isOpen_iUnion fun z0 => (hU_each z0).choose_spec.1
    have hKsub : Kseg ⊆ U := fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, (hU_each ⟨z, hz⟩).choose_spec.2.1⟩
    have hQ_nz_ev : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, QZ w ≠ 0 := by
      intro z
      have hanQ : AnalyticOnNhd ℂ QZ Set.univ := hQZ_diff.differentiableOn.analyticOnNhd isOpen_univ
      by_contra hnot
      have hfreq : ∃ᶠ w in 𝓝[≠] z, QZ w = 0 := by simpa [Filter.not_eventually] using hnot
      have h0 := hanQ.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ z) hfreq (Set.mem_univ (2 : ℂ))
      have hQZ2 : QZ (2 : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g _ => pow_ne_zero _ (by
        intro h; have := congrArg Complex.re h; simp at this; norm_num at this)
      exact hQZ2 h0
    have hagree : ∀ (a b : Kseg) (z : ℂ), z ∈ Uc a → z ∈ Uc b → qc a z = qc b z := by
      intro a b z hza hzb
      have hUa := (hU_each a).choose_spec.1
      have hUb := (hU_each b).choose_spec.1
      have hqa := (hU_each a).choose_spec.2.2.choose_spec
      have hqb := (hU_each b).choose_spec.2.2.choose_spec
      have hev : ∀ᶠ w in 𝓝[≠] z, qc a w = qc b w := by
        filter_upwards [nhdsWithin_le_nhds ((hUa.inter hUb).mem_nhds ⟨hza, hzb⟩), hQ_nz_ev z] with w hw hQw
        exact mul_left_cancel₀ hQw ((hqa.2 w hw.1).2.symm.trans (hqb.2 w hw.2).2)
      have hca : ContinuousAt (qc a) z := (hqa.1.differentiableAt (hUa.mem_nhds hza)).continuousAt
      have hcb : ContinuousAt (qc b) z := (hqb.1.differentiableAt (hUb.mem_nhds hzb)).continuousAt
      exact tendsto_nhds_unique (hca.tendsto.mono_left nhdsWithin_le_nhds)
        ((hcb.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun _ h => h.symm))
    let Hreg : ℂ → ℂ := fun z => if hz : z ∈ U then qc (Set.mem_iUnion.mp hz).choose z else 1
    have hHreg_eq : ∀ (a : Kseg) (z : ℂ), z ∈ Uc a → Hreg z = qc a z := by
      intro a z hza
      have hzU : z ∈ U := Set.mem_iUnion.mpr ⟨a, hza⟩
      simp only [Hreg, dif_pos hzU]
      exact hagree _ a z (Set.mem_iUnion.mp hzU).choose_spec hza
    refine ⟨U, hUopen, hKsub, Hreg, ?_, ?_⟩
    · intro z hz
      obtain ⟨a, hza⟩ := Set.mem_iUnion.mp hz
      have hUa := (hU_each a).choose_spec.1
      have hqa := (hU_each a).choose_spec.2.2.choose_spec.1
      exact ((hqa.differentiableAt (hUa.mem_nhds hza)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hUa.mem_nhds hza) (hHreg_eq a))).differentiableWithinAt
    · intro z hz
      obtain ⟨a, hza⟩ := Set.mem_iUnion.mp hz
      rw [hHreg_eq a z hza]
      exact (hU_each a).choose_spec.2.2.choose_spec.2 z hza
  obtain ⟨Ureg, hUreg_open, hKseg_sub, Hreg, hHreg_diff, hHreg_spec⟩ := hHreg_global
  have hKseg_comp : IsCompact Kseg := isCompact_Icc.image (by fun_prop)
  obtain ⟨r_th, hr_th_pos, hthick_sub⟩ :=
    hKseg_comp.exists_thickening_subset_open hUreg_open hKseg_sub
  let δ : ℝ := min (1 / 4) (r_th / 2)
  have hδpos : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ_le : δ ≤ 1 / 4 := min_le_left _ _
  let Rect : Set ℂ := {s : ℂ | 1 / 2 - δ < s.re ∧ s.re < 1 / 2 + δ ∧ -(T + δ) < s.im ∧ s.im < T + δ}
  have hRect_sub : Rect ⊆ Ureg := by
    intro s hs
    refine hthick_sub ?_
    rw [Metric.mem_thickening_iff]
    let t0 : ℝ := max (-T) (min T s.im)
    have ht0 : t0 ∈ Set.Icc (-T) T := ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    refine ⟨1 / 2 + (t0 : ℂ) * Complex.I, ⟨t0, ht0, rfl⟩, ?_⟩
    have him : |s.im - t0| < δ := by
      dsimp [t0]
      rcases le_or_gt s.im (-T) with h1 | h1
      · rw [min_eq_right (by linarith), max_eq_left h1, abs_of_nonpos (by linarith)]; linarith [hs.2.2.1]
      · rcases le_or_gt s.im T with h2 | h2
        · rw [min_eq_right h2, max_eq_right h1.le, sub_self, abs_zero]; exact hδpos
        · rw [min_eq_left h2.le, max_eq_right (by linarith), abs_of_pos (by linarith)]; linarith [hs.2.2.2]
    have hre : |s.re - 1 / 2| < δ := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2.1]⟩
    have hdist : dist s (1 / 2 + (t0 : ℂ) * Complex.I) ≤ |s.re - 1 / 2| + |s.im - t0| := by
      rw [dist_eq_norm]
      have hdecomp : s - (1 / 2 + (t0 : ℂ) * Complex.I) =
          ((s.re - 1 / 2 : ℝ) : ℂ) + ((s.im - t0 : ℝ) : ℂ) * Complex.I :=
        Complex.ext (by simp) (by simp)
      rw [hdecomp]
      calc
        ‖((s.re - 1 / 2 : ℝ) : ℂ) + ((s.im - t0 : ℝ) : ℂ) * Complex.I‖
            ≤ ‖((s.re - 1 / 2 : ℝ) : ℂ)‖ + ‖((s.im - t0 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |s.re - 1 / 2| + |s.im - t0| := by
              rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs]
    have hδr : 2 * δ ≤ r_th := by have := min_le_right (1 / 4 : ℝ) (r_th / 2); linarith
    linarith
  have hRect_eq : Rect = {s : ℂ | 1 / 2 - δ < s.re} ∩ {s : ℂ | s.re < 1 / 2 + δ} ∩
      ({s : ℂ | -(T + δ) < s.im} ∩ {s : ℂ | s.im < T + δ}) := by ext s; simp [Rect]; tauto
  have hRect_open : IsOpen Rect := by
    rw [hRect_eq]
    exact ((continuous_re.isOpen_preimage _ isOpen_Ioi).inter
      (continuous_re.isOpen_preimage _ isOpen_Iio)).inter
      ((continuous_im.isOpen_preimage _ isOpen_Ioi).inter
        (continuous_im.isOpen_preimage _ isOpen_Iio))
  have hRect_conv : Convex ℝ Rect := by
    rw [hRect_eq]
    exact ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  have hRect_half_mem : (1 / 2 : ℂ) ∈ Rect := by
    refine ⟨by simp; linarith, by simp; linarith, by simp; linarith, by simp; linarith⟩
  have hHreg_half_ne : Hreg (1 / 2 : ℂ) ≠ 0 := (hHreg_spec _ (hRect_sub hRect_half_mem)).1
  obtain ⟨logH, _, hlogH_deriv, _⟩ := exists_holomorphic_log_on_convex hRect_open hRect_conv
    hRect_half_mem (hHreg_diff.mono hRect_sub) (fun z hz => (hHreg_spec z (hRect_sub hz)).1)
    (Complex.log (Hreg (1 / 2 : ℂ))) (Complex.exp_log hHreg_half_ne)
  -- Express logL4 and -L4'/(s*L4) on Rect ∩ Hhalf
  have hRH_open : IsOpen (Rect ∩ Hhalf) := hRect_open.inter hH_open
  have hRH_conv : Convex ℝ (Rect ∩ Hhalf) := hRect_conv.inter hH_conv
  have hpt_mem : ((1 / 2 + δ / 2 : ℝ) : ℂ) ∈ Rect ∩ Hhalf := by
    refine ⟨⟨by simp; linarith, by simp; linarith, by simp; linarith, by simp; linarith⟩,
      show 1 / 2 < (((1 / 2 + δ / 2 : ℝ) : ℂ)).re by simp; linarith⟩
  have hlogDeriv_split : ∀ s ∈ Rect ∩ Hhalf,
      deriv L4 s / L4 s =
        (∑ g ∈ SZ, (mult g : ℂ) / (s - (1 / 2 + (g : ℂ) * Complex.I))) +
        deriv Hreg s / Hreg s := by
    intro s hs
    have hsU := hRect_sub hs.1
    have hsH : 1 / 2 < s.re := hs.2
    have hHne : Hreg s ≠ 0 := (hHreg_spec s hsU).1
    have hfac_ne : ∀ g ∈ SZ, s - (1 / 2 + (g : ℂ) * Complex.I) ≠ 0 := fun g _ h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hQne : QZ s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g hg => pow_ne_zero _ (hfac_ne g hg)
    have hL_eq_ev : L4 =ᶠ[𝓝 s] fun w => QZ w * Hreg w :=
      Filter.eventually_of_mem (hUreg_open.mem_nhds hsU) fun w hw => (hHreg_spec w hw).2
    have hderiv_L : deriv L4 s = deriv QZ s * Hreg s + QZ s * deriv Hreg s := by
      rw [hL_eq_ev.deriv_eq,
        deriv_fun_mul (hQZ_diff s) (hHreg_diff.differentiableAt (hUreg_open.mem_nhds hsU))]
    rw [hderiv_L, (hHreg_spec s hsU).2, add_div, mul_div_mul_right _ _ hHne,
      mul_div_mul_left _ _ hQne]
    congr 1
    rw [logDeriv_finset_prod SZ (fun g w => (w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g) s
      (fun g _ => (differentiableAt_id.sub (differentiableAt_const _)).pow _)
      (fun g hg => pow_ne_zero _ (hfac_ne g hg))]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hd : HasDerivAt (fun w : ℂ => (w - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g)
        ((mult g : ℂ) * (s - (1 / 2 + (g : ℂ) * Complex.I)) ^ (mult g - 1)) s := by
      simpa using ((hasDerivAt_id s).sub_const (1 / 2 + (g : ℂ) * Complex.I)).fun_pow (mult g)
    rw [hd.deriv]
    rcases Nat.eq_zero_or_pos (mult g) with hm0 | hmpos
    · simp [hm0]
    · have hne := hfac_ne g hg
      have hpow : (s - (1 / 2 + (g : ℂ) * Complex.I)) ^ mult g =
          (s - (1 / 2 + (g : ℂ) * Complex.I)) ^ (mult g - 1) * (s - (1 / 2 + (g : ℂ) * Complex.I)) := by
        rw [← pow_succ, Nat.sub_add_cancel hmpos]
      rw [hpow, ← div_div, mul_div_cancel_right₀ _ (pow_ne_zero (mult g - 1) hne)]
  -- Constant c0 relating logL4 to ∑ mult g * log(s - ρ_g) + logH on Rect ∩ Hhalf
  let logSum : ℂ → ℂ := fun s => ∑ g ∈ SZ, (mult g : ℂ) * Complex.log (s - (1 / 2 + (g : ℂ) * Complex.I))
  let c0 : ℂ := logL4 ((1 / 2 + δ / 2 : ℝ) : ℂ) - (logSum ((1 / 2 + δ / 2 : ℝ) : ℂ) + logH ((1 / 2 + δ / 2 : ℝ) : ℂ))
  have hlogL4_split : ∀ s ∈ Rect ∩ Hhalf, logL4 s = logSum s + logH s + c0 := by
    have hdiff0 : ∀ s ∈ Rect ∩ Hhalf,
        HasDerivAt (fun w => logL4 w - (logSum w + logH w)) 0 s := by
      intro s hs
      have hlogSum_d : HasDerivAt logSum
          (∑ g ∈ SZ, (mult g : ℂ) / (s - (1 / 2 + (g : ℂ) * Complex.I))) s := by
        have hsum := HasDerivAt.fun_sum (u := SZ)
          (A := fun g w => (mult g : ℂ) * Complex.log (w - (1 / 2 + (g : ℂ) * Complex.I)))
          (A' := fun g => (mult g : ℂ) / (s - (1 / 2 + (g : ℂ) * Complex.I))) (x := s) fun g _ => by
            have hre_pos : 0 < (s - (1 / 2 + (g : ℂ) * Complex.I)).re := by
              have : 1 / 2 < s.re := hs.2; simp; linarith
            have hd := ((hasDerivAt_id s).sub_const (1 / 2 + (g : ℂ) * Complex.I)).clog (Or.inl hre_pos)
            simpa [div_eq_mul_inv] using hd.const_mul (mult g : ℂ)
        exact hsum
      have h1 := (hlogL4_deriv s hs.2).sub (hlogSum_d.add (hlogH_deriv s hs.1))
      rw [hlogDeriv_split s hs, sub_self] at h1
      exact h1
    intro s hs
    have hconst := hRH_conv.is_const_of_fderivWithin_eq_zero
      (f := fun w => logL4 w - (logSum w + logH w))
      (fun w hw => (hdiff0 w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [fderivWithin_of_isOpen hRH_open hw, (hdiff0 w hw).hasFDerivAt.fderiv]; simp)
      hs hpt_mem
    dsimp [c0]; linear_combination hconst
  -- Smooth remainder R1 on Rect
  let R1 : ℂ → ℂ := fun s =>
    -(∑ g ∈ SZ, (mult g : ℂ) / ((1 / 2 + (g : ℂ) * Complex.I) * s)) + deriv Hreg s / (s * Hreg s)
  have hR1_cont : ContinuousOn R1 Rect := by
    have hne0 : ∀ s ∈ Rect, s ≠ 0 := fun s hs h0 => by
      have := hs.1; rw [h0, zero_re] at this; linarith
    have hHdiff : DifferentiableOn ℂ Hreg Rect := hHreg_diff.mono hRect_sub
    have h1 : ContinuousOn (fun s => ∑ g ∈ SZ, (mult g : ℂ) / ((1 / 2 + (g : ℂ) * Complex.I) * s)) Rect :=
      continuousOn_finsetSum SZ fun g _ =>
        continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun s hs =>
          mul_ne_zero (fun h => by have := congrArg Complex.re h; simp at this) (hne0 s hs)
    have h2 : ContinuousOn (fun s => deriv Hreg s / (s * Hreg s)) Rect :=
      (hHdiff.deriv hRect_open).continuousOn.div
        (continuousOn_id.mul hHdiff.continuousOn) fun s hs =>
          mul_ne_zero (hne0 s hs) (hHreg_spec s (hRect_sub hs)).1
    exact h1.neg.add h2
  have hpos_logDeriv_split : ∀ s ∈ Rect ∩ Hhalf,
      deriv L4 s / (s * L4 s) =
        (∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          (1 / (s - (1 / 2 + (g : ℂ) * Complex.I)))) + R1 s := by
    intro s hs
    have hsne : s ≠ 0 := fun h0 => by have : 1 / 2 < s.re := hs.2; rw [h0, zero_re] at this; linarith
    have hLne := hRH s hs.2
    have hld := hlogDeriv_split s hs
    rw [show deriv L4 s / (s * L4 s) = (deriv L4 s / L4 s) / s by field_simp [hsne, hLne],
      hld, add_div, Finset.sum_div]
    dsimp [R1]
    have hpf : ∑ g ∈ SZ, (mult g : ℂ) / (s - (1 / 2 + (g : ℂ) * Complex.I)) / s =
        (∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          (1 / (s - (1 / 2 + (g : ℂ) * Complex.I)))) -
        (∑ g ∈ SZ, (mult g : ℂ) / ((1 / 2 + (g : ℂ) * Complex.I) * s)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      set ρ : ℂ := 1 / 2 + (g : ℂ) * Complex.I
      have hρ : ρ ≠ 0 := fun h => by have := congrArg Complex.re h; simp [ρ] at this
      have hsub : s - ρ ≠ 0 := fun h => by
        have h1 : s.re - 1 / 2 = 0 := by simpa [ρ] using congrArg Complex.re h
        have h2 : 1 / 2 < s.re := hs.2
        linarith
      field_simp [hρ, hsub, hsne]; ring
    rw [hpf]
    have hHne : Hreg s ≠ 0 := (hHreg_spec s (hRect_sub hs.1)).1
    have hdivH : deriv Hreg s / Hreg s / s = deriv Hreg s / (s * Hreg s) := by
      field_simp [hsne, hHne]
    rw [hdivH]; ring
  -- Step 6d: Fejer convolution at fixed x > u1 + 1 and ε ∈ (0, δ/2], then ε ↓ 0!
  let fBdry : ℝ → ℂ := fun t =>
    R1 (1 / 2 + (t : ℂ) * Complex.I) -
      ((∑ g ∈ SZ, (mult g : ℂ) * Complex.log (((t - g : ℝ) : ℂ) * Complex.I)) +
        logH (1 / 2 + (t : ℂ) * Complex.I) + c0) / (1 / 2 + (t : ℂ) * Complex.I) ^ 2
  let C_fin : ℝ := (2 / (Real.pi * T)) * (u1 * u1 * Real.exp u1)
  have hmain_x : ∀ x : ℝ, u1 + 1 < x →
      0 ≤ (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
              ∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re +
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
              (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re +
          C_fin / (x - u1) ^ 2 +
          (41 / 10 : ℝ) * (2 * fejerConst / Real.pi) := by
    intro x hx
    -- Evaluate the Fejer integral along the sequence ε n = δ / (2 * (n + 1)) → 0
    let eps : ℕ → ℝ := fun n => δ / (2 * ((n : ℝ) + 1))
    have heps_pos : ∀ n : ℕ, 0 < eps n := fun n => by dsimp [eps]; positivity
    have heps_le : ∀ n : ℕ, eps n ≤ δ / 2 := fun n => by
      dsimp [eps]
      refine div_le_div_of_nonneg_left hδpos.le (by positivity) ?_
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have heps_tend : Tendsto eps atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h2 := tendsto_const_nhds (x := δ / 2) |>.div_atTop h1
      refine h2.congr fun n => ?_
      dsimp [eps]; rw [div_div]
    have hrect_mem : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (-T) T →
        (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ∈ Rect ∩ Hhalf := fun n t ht => by
      have he1 := heps_pos n
      have he2 := heps_le n
      refine ⟨⟨by simp; linarith, by simp; linarith, by simp; linarith [ht.1], by simp; linarith [ht.2]⟩,
        show 1 / 2 < (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I).re by simp; linarith⟩
    -- For each n, 0 ≤ Re((1/(2π)) ∫_{-T}^T (1 - |t|/T) e^{itx} Phi(1/2 + eps n + it) dt)
    have hnonneg_n : ∀ n : ℕ,
        0 ≤ (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
                ∫ u in Set.Ioi (0 : ℝ),
                  Complex.exp (-((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
                    (fejerK T (x - u) : ℂ))).re +
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) -
                  logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                    (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)).re +
            C_fin / (x - u1) ^ 2 +
            (41 / 10 : ℝ) * (2 * fejerConst / Real.pi) := by
      intro n
      set e : ℝ := eps n
      have hepos : 0 < e := heps_pos n
      -- Helper Fubini lemma: for f integrable on Set.Ioi a,
      -- (1/(2π)) ∫_{-T}^T (1 - |t|/T) e^{itx} (∫_{Ioi a} f u e^{-itu} du) dt = ∫_{Ioi a} f u K_T(x - u) du
      have hfubini : ∀ (S : Set ℝ) (hSm : MeasurableSet S) (f : ℝ → ℂ),
          IntegrableOn f S →
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
              (∫ u in S, f u * Complex.exp (-((t : ℂ) * (u : ℂ) * Complex.I))) =
          ∫ u in S, f u * (fejerK T (x - u) : ℂ) := by
        intro S hSm f hf
        rw [intervalIntegral.integral_of_le (by linarith)]
        have hmul_in : ∀ t : ℝ,
            ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
              (∫ u in S, f u * Complex.exp (-((t : ℂ) * (u : ℂ) * Complex.I))) =
            ∫ u in S, f u * (((1 - |t| / T : ℝ) : ℂ) *
              Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I)) := fun t => by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun hSm fun u _ => ?_
          have : ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
              (f u * Complex.exp (-((t : ℂ) * (u : ℂ) * Complex.I))) =
              f u * (((1 - |t| / T : ℝ) : ℂ) *
                (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                  Complex.exp (-((t : ℂ) * (u : ℂ) * Complex.I)))) := by ring
          rw [this, ← Complex.exp_add]; congr 3; push_cast; ring
        simp_rw [hmul_in]
        have hprod_int : Integrable (Function.uncurry fun (t u : ℝ) =>
            f u * (((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I)))
            ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict S)) := by
          have hmeas_prod : AEStronglyMeasurable
              (Function.uncurry fun (t u : ℝ) =>
                f u * (((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * ((x - u : ℝ) : ℂ) * Complex.I)))
              ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict S)) := by
            have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2)
                ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict S)) :=
              hf.aestronglyMeasurable.comp_snd
            have h2 : Continuous (fun p : ℝ × ℝ =>
                ((1 - |p.1| / T : ℝ) : ℂ) * Complex.exp ((p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I)) := by
              fun_prop
            exact h1.mul h2.aestronglyMeasurable
          have hdom_prod : Integrable (Function.uncurry fun (_t u : ℝ) => ‖f u‖)
              ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict S)) := by
            have hfin_Ioc : volume (Set.Ioc (-T) T) < ⊤ := measure_Ioc_lt_top
            have hc1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (-T) T) volume :=
              integrableOn_const (hs := hfin_Ioc.ne)
            exact (hc1.mul_prod hf.norm).congr (Filter.Eventually.of_forall fun p => by simp [Function.uncurry])
          refine hdom_prod.mono' hmeas_prod ?_
          have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-T) T)), t ∈ Set.Ioc (-T) T :=
            ae_restrict_mem measurableSet_Ioc
          have hfst : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict S)),
              p.1 ∈ Set.Ioc (-T) T :=
            Measure.quasiMeasurePreserving_fst.ae hae
          filter_upwards [hfst] with p hp
          dsimp [Function.uncurry]
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            show (p.1 : ℂ) * ((x - p.2 : ℝ) : ℂ) * Complex.I = ((p.1 * (x - p.2) : ℝ) : ℂ) * Complex.I by
              push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have hwt : |1 - |p.1| / T| ≤ 1 := by
            have habs : |p.1| ≤ T := abs_le.mpr ⟨hp.1.le, hp.2⟩
            have hdiv : |p.1| / T ≤ 1 := (div_le_one hTpos).mpr habs
            rw [abs_of_nonneg (by linarith)]
            linarith [div_nonneg (abs_nonneg p.1) hTpos.le]
          exact mul_le_of_le_one_right (norm_nonneg _) hwt
        rw [integral_integral_swap hprod_int, ← integral_const_mul]
        refine setIntegral_congr_fun hSm fun u _ => ?_
        rw [integral_const_mul, ← mul_assoc, mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)), mul_assoc]
        congr 1
        rw [← intervalIntegral.integral_of_le (by linarith)]
        exact fourier_tent_eq_fejerK hTpos (x - u)
      -- 1. LHS via Gfun is non-negative real!
      have hG_int_e : IntegrableOn (fun u : ℝ => (Gfun u : ℂ) * Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))))
          (Set.Ioi u1) := by
        refine (hG_int_half (1 / 2 + e) (by linarith)).mono'
          (((Complex.continuous_ofReal.measurable.comp hG_meas).mul (by fun_prop)).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hG_nonneg u hu),
          ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
          Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul]
      have hLHS_fub := hfubini (Set.Ioi u1) measurableSet_Ioi
        (fun u => (Gfun u : ℂ) * Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ)))) hG_int_e
      have hLHS_eq_Phi : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            Phi (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) =
          ∫ u in Set.Ioi u1, (Gfun u : ℂ) * Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))) *
            (fejerK T (x - u) : ℂ) := by
        rw [← hLHS_fub]
        congr 1
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [hPhi_eq_G _ (show 1 / 2 < (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I).re by simp; linarith)]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
      have hLHS_re_nonneg : 0 ≤ (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            Phi (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I)).re := by
        rw [hLHS_eq_Phi]
        have hint_real : IntegrableOn (fun u : ℝ => Gfun u * Real.exp (-(1 / 2 + e) * u) * fejerK T (x - u))
            (Set.Ioi u1) := by
          refine ((hG_int_half (1 / 2 + e) (by linarith)).mul_const (T / (2 * Real.pi))).mono'
            (((hG_meas.mul (by fun_prop)).mul
              ((measurable_fejerK T).comp (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          have hG0 := hG_nonneg u hu
          have hK0 := fejerK_nonneg hTpos (x - u)
          rw [Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (fejerK_le_const hTpos (x - u)) (by positivity)
        have hfn : (fun u : ℝ => (Gfun u : ℂ) * Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))) *
            (fejerK T (x - u) : ℂ)) =
            fun u : ℝ => ((Gfun u * Real.exp (-(1 / 2 + e) * u) * fejerK T (x - u) : ℝ) : ℂ) := by
          ext u
          rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp]
          congr 3; push_cast; ring
        rw [hfn, integral_ofReal_eq hint_real, Complex.ofReal_re]
        exact setIntegral_nonneg measurableSet_Ioi fun u hu =>
          mul_nonneg (mul_nonneg (hG_nonneg u hu) (Real.exp_pos _).le) (fejerK_nonneg hTpos _)
      -- 2. Decompose Phi(1/2 + e + t*I) on [-T, T] into 4 pieces and integrate each
      let wt : ℝ → ℂ := fun t => ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
      have hwt_cont : Continuous wt := by dsimp [wt]; fun_prop
      have hpiece_eq : ∀ t ∈ Set.uIcc (-T) T,
          wt t * Phi (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) =
          (∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)))) +
          wt t * (R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) -
              logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) /
                (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) ^ 2) +
          wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) +
          (41 / 10 : ℂ) * (wt t * (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
              ((e : ℂ) + (t : ℂ) * Complex.I))) := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        have hmem := hrect_mem n t ht
        dsimp [Phi]
        rw [hpos_logDeriv_split _ hmem]
        have hsub1 : (1 / 2 : ℂ) + (e : ℂ) + (t : ℂ) * Complex.I - 1 / 2 =
            (e : ℂ) + (t : ℂ) * Complex.I := by ring
        rw [hsub1]
        have hsum_mul : wt t * ∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (1 / (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I - (1 / 2 + (g : ℂ) * Complex.I))) =
            ∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          have hsubg : 1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I - (1 / 2 + (g : ℂ) * Complex.I) =
              (e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [hsubg]; ring
        linear_combination hsum_mul
      -- Integrability of each piece on [-T, T] (all are continuous on [-T, T] since e > 0!)
      have hi_pole : ∀ g ∈ SZ, IntervalIntegrable
          (fun t : ℝ => wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))) volume (-T) T := by
        intro g _
        refine Continuous.intervalIntegrable ?_ (-T) T
        refine hwt_cont.mul (continuous_const.div (by fun_prop) fun t => ?_)
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hi_poles : IntervalIntegrable
          (fun t : ℝ => ∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
            (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)))) volume (-T) T := by
        have hsum_eq : (fun t : ℝ => ∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
            (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)))) =
            ∑ g ∈ SZ, fun t : ℝ => ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))) := by
          ext t; simp
        rw [hsum_eq]
        exact IntervalIntegrable.sum SZ fun g hg => (hi_pole g hg).const_mul _
      have hi_smooth : IntervalIntegrable
          (fun t : ℝ => wt t * (R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) -
            logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) /
              (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) ^ 2)) volume (-T) T := by
        refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
        have hmap : ContinuousOn (fun t : ℝ => (1 / 2 : ℂ) + (e : ℂ) + (t : ℂ) * Complex.I) (Set.Icc (-T) T) := by
          fun_prop
        have hR1c : ContinuousOn (fun t : ℝ => R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc (-T) T) :=
          hR1_cont.comp hmap fun t ht => (hrect_mem n t ht).1
        have hlogc : ContinuousOn (fun t : ℝ => logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc (-T) T) :=
          hlogL4_diff.continuousOn.comp hmap fun t ht => (hrect_mem n t ht).2
        refine hwt_cont.continuousOn.mul (hR1c.sub (hlogc.div (hmap.pow 2) fun t _ h0 => ?_))
        have := congrArg Complex.re (eq_zero_of_pow_eq_zero h0); simp at this; linarith
      have hi_fin : IntervalIntegrable
          (fun t : ℝ => wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))) volume (-T) T :=
        Continuous.intervalIntegrable
          (hwt_cont.mul (hint_fin_diff.continuous.comp (by fun_prop))) (-T) T
      have hi_11 : IntervalIntegrable
          (fun t : ℝ => (41 / 10 : ℂ) * (wt t * (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
            ((e : ℂ) + (t : ℂ) * Complex.I)))) volume (-T) T := by
        refine (Continuous.intervalIntegrable ?_ (-T) T).const_mul _
        refine hwt_cont.mul ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ)))).div (by fun_prop) fun t h0 => ?_)
        have := congrArg Complex.re h0; simp at this; linarith
      -- Evaluate each piece by Fubini!
      have hpole_eval : ∀ g ∈ SZ,
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)) =
          ∫ u in Set.Ioi (0 : ℝ),
            Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) * (fejerK T (x - u) : ℂ) := by
        intro g _
        have hint_g : IntegrableOn
            (fun u : ℝ => Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I))
            (Set.Ioi (0 : ℝ)) := by
          refine (integrableOn_exp_mul_Ioi (a := -e) (by linarith) 0).mono' (by fun_prop) ?_
          filter_upwards with u
          rw [Complex.norm_exp]; simp [neg_mul]
        rw [← hfubini (Set.Ioi 0) measurableSet_Ioi _ hint_g]
        congr 1
        refine intervalIntegral.integral_congr fun t _ => ?_
        congr 1
        have heq_exp : (fun u : ℝ => Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
            Complex.exp (-((t : ℂ) * (u : ℂ) * Complex.I))) =
            fun u : ℝ => Complex.exp ((-((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)) * (u : ℂ)) := by
          ext u; rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [heq_exp, integral_exp_mul_complex_Ioi (by simp; linarith) 0]
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        have hne : (e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        field_simp [hne]
      have hfin_eval : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))‖ ≤
          C_fin / (x - u1) ^ 2 := by
        have hint_fin_e : IntegrableOn
            (fun u : ℝ => ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))))
            (Set.Ioc 0 u1) := by
          refine (integrableOn_const (C := u1 * Real.exp u1) (hs := measure_Ioc_lt_top.ne)).mono'
            (((Complex.continuous_ofReal.measurable.comp (measurable_id.mul measurable_jExp)).mul
              (by fun_prop)).aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          have hu0 : 0 ≤ u := hu.1.le
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0,
            Complex.norm_exp, neg_re, mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          have hexp1 : Real.exp (-((1 / 2 + e) * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          have hmul1 : u * |jExp u| ≤ u1 * Real.exp u1 :=
            mul_le_mul hu.2 ((abs_jExp_le u).trans (Real.exp_le_exp.mpr hu.2)) (abs_nonneg _) hu1_pos.le
          exact (mul_le_of_le_one_right (by positivity) hexp1).trans hmul1
        have hfub_fin := hfubini (Set.Ioc 0 u1) measurableSet_Ioc _ hint_fin_e
        have heq_f : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) =
            ∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))) * (fejerK T (x - u) : ℂ) := by
          rw [← hfub_fin]
          congr 1
          refine intervalIntegral.integral_congr fun t _ => ?_
          congr 1
          refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
          rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
        rw [heq_f]
        calc
          ‖∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))) * (fejerK T (x - u) : ℂ)‖
              ≤ ∫ u in Set.Ioc (0 : ℝ) u1, ‖((u * jExp u : ℝ) : ℂ) *
                  Complex.exp (-(((1 / 2 + e : ℝ) : ℂ) * (u : ℂ))) * (fejerK T (x - u) : ℂ)‖ :=
                norm_integral_le_integral_norm _
          _ ≤ ∫ _u in Set.Ioc (0 : ℝ) u1, (u1 * Real.exp u1) * (2 / (Real.pi * T * (x - u1) ^ 2)) := by
                refine setIntegral_mono_on
                  ((hint_fin_e.norm.mul_const (T / (2 * Real.pi))).mono'
                    ((hint_fin_e.aestronglyMeasurable.mul
                      ((Complex.continuous_ofReal.measurable.comp
                        ((measurable_fejerK T).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)).norm)
                    (by
                      filter_upwards with u
                      rw [norm_norm, norm_mul, Complex.norm_real,
                        Real.norm_of_nonneg (fejerK_nonneg hTpos _)]
                      exact mul_le_mul_of_nonneg_left (fejerK_le_const hTpos _) (norm_nonneg _)))
                  (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun u hu => ?_
                have hu0 : 0 ≤ u := hu.1.le
                have hxu : x - u1 ≤ x - u := by linarith [hu.2]
                have hxu_pos : 0 < x - u1 := by linarith
                rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
                  abs_of_nonneg hu0, Complex.norm_exp, neg_re, mul_re, Complex.norm_real,
                  Real.norm_of_nonneg (fejerK_nonneg hTpos _)]
                simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
                have hexp1 : Real.exp (-((1 / 2 + e) * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
                have hmul1 : u * |jExp u| * Real.exp (-((1 / 2 + e) * u)) ≤ u1 * Real.exp u1 := by
                  have h0 := mul_le_mul hu.2 ((abs_jExp_le u).trans (Real.exp_le_exp.mpr hu.2))
                    (abs_nonneg _) hu1_pos.le
                  exact (mul_le_of_le_one_right (by positivity) hexp1).trans h0
                have hK_le : fejerK T (x - u) ≤ 2 / (Real.pi * T * (x - u1) ^ 2) :=
                  (fejerK_le_tail hTpos (by linarith)).trans
                    (div_le_div_of_nonneg_left (by norm_num) (by positivity)
                      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxu_pos.le hxu 2) (by positivity)))
                exact mul_le_mul hmul1 hK_le (fejerK_nonneg hTpos _) (by positivity)
          _ = C_fin / (x - u1) ^ 2 := by
                rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc, sub_zero,
                  ENNReal.toReal_ofReal hu1_pos.le]
                dsimp [C_fin]; field_simp [Real.pi_pos.ne', hTpos.ne']
      have h11_eval : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, (41 / 10 : ℂ) * (wt t *
            (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
              ((e : ℂ) + (t : ℂ) * Complex.I)))).re ≤
          (41 / 10 : ℝ) * (2 * fejerConst / Real.pi) := by
        have hint_e : IntegrableOn (fun u : ℝ => Complex.exp (-((e : ℂ) * (u : ℂ)))) (Set.Ioi u1) := by
          refine (integrableOn_exp_mul_Ioi (a := -e) (by linarith) u1).mono' (by fun_prop) ?_
          filter_upwards with u; rw [Complex.norm_exp]; simp [neg_mul]
        have hfub_11 := hfubini (Set.Ioi u1) measurableSet_Ioi _ hint_e
        have heq_11 : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, (41 / 10 : ℂ) * (wt t *
              (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
                ((e : ℂ) + (t : ℂ) * Complex.I))) =
            (41 / 10 : ℂ) * ∫ u in Set.Ioi u1, Complex.exp (-((e : ℂ) * (u : ℂ))) * (fejerK T (x - u) : ℂ) := by
          rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)),
            mul_assoc, ← hfub_11]
          congr 2
          refine intervalIntegral.integral_congr fun t _ => ?_
          congr 1
          have heq_exp : (fun u : ℝ => Complex.exp (-((e : ℂ) * (u : ℂ))) *
              Complex.exp (-((t : ℂ) * (u : ℂ) * Complex.I))) =
              fun u : ℝ => Complex.exp ((-((e : ℂ) + (t : ℂ) * Complex.I)) * (u : ℂ)) := by
            ext u; rw [← Complex.exp_add]; congr 1; ring
          rw [heq_exp, integral_exp_mul_complex_Ioi (by simp; linarith) u1]
          have hne : (e : ℂ) + (t : ℂ) * Complex.I ≠ 0 := fun h => by
            have := congrArg Complex.re h; simp at this; linarith
          field_simp [hne]
        rw [heq_11]
        have hint_re11 : IntegrableOn (fun u : ℝ => Real.exp (-e * u) * fejerK T (x - u)) (Set.Ioi u1) := by
          refine ((integrable_fejerK hTpos).comp_sub_left x).integrableOn.mono'
            ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
              ((measurable_fejerK T).comp (measurable_const.sub measurable_id))).aestronglyMeasurable ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
          rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (fejerK_nonneg hTpos _))]
          exact mul_le_of_le_one_left (fejerK_nonneg hTpos _) (Real.exp_le_one_iff.mpr (by nlinarith))
        have hfn : (fun u : ℝ => Complex.exp (-((e : ℂ) * (u : ℂ))) * (fejerK T (x - u) : ℂ)) =
            fun u : ℝ => ((Real.exp (-e * u) * fejerK T (x - u) : ℝ) : ℂ) := by
          ext u; rw [Complex.ofReal_mul, Complex.ofReal_exp]; congr 2; push_cast; ring
        rw [hfn, integral_ofReal_eq hint_re11]
        have hre_val : ((41 / 10 : ℂ) * ((∫ u in Set.Ioi u1, Real.exp (-e * u) * fejerK T (x - u) : ℝ) : ℂ)).re =
            (41 / 10 : ℝ) * ∫ u in Set.Ioi u1, Real.exp (-e * u) * fejerK T (x - u) := by
          simp
        rw [hre_val]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc
          ∫ u in Set.Ioi u1, Real.exp (-e * u) * fejerK T (x - u)
              ≤ ∫ u in Set.Ioi u1, fejerK T (x - u) := by
                refine setIntegral_mono_on hint_re11
                  ((integrable_fejerK hTpos).comp_sub_left x).integrableOn measurableSet_Ioi fun u hu => ?_
                have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
                exact mul_le_of_le_one_left (fejerK_nonneg hTpos _) (Real.exp_le_one_iff.mpr (by nlinarith))
          _ ≤ ∫ u : ℝ, fejerK T (x - u) :=
                setIntegral_le_integral ((integrable_fejerK hTpos).comp_sub_left x)
                  (Filter.Eventually.of_forall fun u => fejerK_nonneg hTpos _)
          _ = ∫ v : ℝ, fejerK T v := integral_sub_left_eq_self (fejerK T) volume x
          _ = 2 * fejerConst / Real.pi := integral_fejerK hTpos
      -- Combine all 4 pieces!
      have hdecomp : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (-T)..T, wt t * Phi (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I)) =
          (∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (∫ u in Set.Ioi (0 : ℝ),
                Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) * (fejerK T (x - u) : ℂ))) +
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, wt t * (R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) -
              logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) /
                (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) ^ 2)) +
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))) +
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, (41 / 10 : ℂ) * (wt t *
              (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
                ((e : ℂ) + (t : ℂ) * Complex.I)))) := by
        rw [intervalIntegral.integral_congr hpiece_eq,
          intervalIntegral.integral_add ((hi_poles.add hi_smooth).add hi_fin) hi_11,
          intervalIntegral.integral_add (hi_poles.add hi_smooth) hi_fin,
          intervalIntegral.integral_add hi_poles hi_smooth,
          intervalIntegral.integral_finsetSum fun g hg => (hi_pole g hg).const_mul _]
        have hpoles_simp : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∑ g ∈ SZ, ∫ t in (-T)..T, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)))) =
            ∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              ∫ u in Set.Ioi (0 : ℝ),
                Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
                  (fejerK T (x - u) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [intervalIntegral.integral_const_mul, ← mul_assoc,
            mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)), mul_assoc, hpole_eval g hg]
        rw [mul_add, mul_add, mul_add, hpoles_simp]
      rw [hdecomp] at hLHS_re_nonneg
      simp only [Complex.add_re] at hLHS_re_nonneg
      have hfin_re : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))).re ≤
          C_fin / (x - u1) ^ 2 := by
        have h1 := (abs_le.mp (Complex.abs_re_le_norm (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))))).2
        linarith [hfin_eval]
      dsimp only [wt] at hLHS_re_nonneg hfin_re h11_eval
      linarith
    -- Now take n → ∞ (eps n → 0) by Dominated Convergence on both the pole integrals and the smooth+log integral!
    have htend_poles : Tendsto (fun n : ℕ =>
        (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          ∫ u in Set.Ioi (0 : ℝ),
            Complex.exp (-((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
              (fejerK T (x - u) : ℂ))).re) atTop
        (𝓝 (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
          ∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re) := by
      simp_rw [Complex.re_sum]
      refine tendsto_finsetSum SZ fun g _ => ?_
      have ht_int : Tendsto (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ),
            Complex.exp (-((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
              (fejerK T (x - u) : ℂ)) atTop
          (𝓝 (∫ u in Set.Ioi (0 : ℝ),
            Complex.exp ((g : ℂ) * (u : ℂ) * Complex.I) * (fejerK T (x - u) : ℂ))) := by
        refine tendsto_integral_of_dominated_convergence (fun u => fejerK T (x - u))
          (fun n => (by fun_prop : Continuous fun u : ℝ =>
            Complex.exp (-((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I)).aestronglyMeasurable.mul
            ((Complex.continuous_ofReal.measurable.comp
              ((measurable_fejerK T).comp (measurable_const.sub measurable_id))).aestronglyMeasurable))
          ((integrable_fejerK hTpos).comp_sub_left x).integrableOn
          (fun n => by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have hu0 : 0 ≤ u := (Set.mem_Ioi.mp hu).le
            rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (fejerK_nonneg hTpos _)]
            have hre : (-((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I).re = -(eps n * u) := by
              simp
            rw [hre]
            exact mul_le_of_le_one_left (fejerK_nonneg hTpos _) (Real.exp_le_one_iff.mpr (by nlinarith [heps_pos n])))
          (by
            filter_upwards with u
            have h1 : Tendsto (fun n : ℕ => -((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I)
                atTop (𝓝 ((g : ℂ) * (u : ℂ) * Complex.I)) := by
              have hc : Tendsto (fun n : ℕ => (eps n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
                simpa only [Function.comp_def, Complex.ofReal_zero] using
                  (Complex.continuous_ofReal.tendsto 0).comp heps_tend
              simpa using (hc.mul_const (u : ℂ)).neg.add_const ((g : ℂ) * (u : ℂ) * Complex.I)
            exact ((Complex.continuous_exp.tendsto _).comp h1).mul_const _)
      -- Change variable v = x - u in the limit integral
      have hchg : ∫ u in Set.Ioi (0 : ℝ),
            Complex.exp ((g : ℂ) * (u : ℂ) * Complex.I) * (fejerK T (x - u) : ℂ) =
          Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
            ∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ) := by
        rw [← integral_const_mul, ← integral_indicator measurableSet_Ioi,
          ← integral_indicator measurableSet_Iio]
        have hsub := integral_sub_left_eq_self
          (fun v : ℝ => Set.indicator (Set.Iio x)
            (fun w => Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
              (Complex.exp (-((g : ℂ) * (w : ℂ) * Complex.I)) * (fejerK T w : ℂ))) v) volume x
        rw [← hsub]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        by_cases hu : 0 < u
        · have hu' : u ∈ Set.Ioi (0 : ℝ) := hu
          have hxu' : x - u ∈ Set.Iio x := by change x - u < x; linarith
          rw [Set.indicator_of_mem hu', Set.indicator_of_mem hxu', ← mul_assoc, ← Complex.exp_add]
          congr 2; push_cast; ring
        · have hu' : u ∉ Set.Ioi (0 : ℝ) := hu
          have hxu' : x - u ∉ Set.Iio x := by change ¬ (x - u < x); linarith
          rw [Set.indicator_of_notMem hu', Set.indicator_of_notMem hxu']
      rw [hchg] at ht_int
      have hmul := ht_int.const_mul ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I))
      have hre_t := (Complex.continuous_re.tendsto _).comp hmul
      simpa only [Function.comp_def, mul_assoc] using hre_t
    have htend_smooth : Tendsto (fun n : ℕ =>
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) -
              logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)).re) atTop
        (𝓝 ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re)) := by
      -- Uniform bound on compact box Kbox = [1/2, 1/2 + δ/2] × [-T, T] ⊆ Rect
      let Kbox : Set ℂ := (fun p : ℝ × ℝ => (1 / 2 + p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        (Set.Icc (0 : ℝ) (δ / 2) ×ˢ Set.Icc (-T) T)
      have hKbox_sub : Kbox ⊆ Rect := by
        rintro _ ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩
        refine ⟨by simp; linarith [ha.1], by simp; linarith [ha.2],
          by simp; linarith [ht.1], by simp; linarith [ht.2]⟩
      have hKbox_comp : IsCompact Kbox :=
        (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
      obtain ⟨MR1, hMR1⟩ := hKbox_comp.exists_bound_of_continuousOn (hR1_cont.mono hKbox_sub)
      have hlogH_diff : DifferentiableOn ℂ logH Rect :=
        fun z hz => (hlogH_deriv z hz).differentiableAt.differentiableWithinAt
      have hlogH_cont : ContinuousOn logH Rect := hlogH_diff.continuousOn
      obtain ⟨MlogH, hMlogH⟩ := hKbox_comp.exists_bound_of_continuousOn (hlogH_cont.mono hKbox_sub)
      let Mdom : ℝ := 2 * T + δ + 1
      have hMdom1 : 1 ≤ Mdom := by dsimp [Mdom]; linarith
      let bound_t : ℝ → ℝ := fun t =>
        max 0 MR1 + 4 * ((∑ g ∈ SZ, (mult g : ℝ) * (abs (Real.log |t - g|) + Real.log (2 * Mdom) + Real.pi)) +
          max 0 MlogH + ‖c0‖)
      have hbound_int : IntegrableOn bound_t (Set.Ioc (-T) T) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
        have hsum_int : IntervalIntegrable
            (fun t : ℝ => ∑ g ∈ SZ, (mult g : ℝ) * (abs (Real.log |t - g|) + Real.log (2 * Mdom) + Real.pi))
            volume (-T) T := by
          have hsum_eq : (fun t : ℝ => ∑ g ∈ SZ, (mult g : ℝ) * (abs (Real.log |t - g|) + Real.log (2 * Mdom) + Real.pi)) =
              ∑ g ∈ SZ, fun t : ℝ => (mult g : ℝ) * (abs (Real.log |t - g|) + Real.log (2 * Mdom) + Real.pi) := by
            ext t; simp
          rw [hsum_eq]
          refine IntervalIntegrable.sum SZ fun g _ => ?_
          exact (((intervalIntegrable_abs_log_abs_sub (-T) T g).add intervalIntegrable_const).add
            intervalIntegrable_const).const_mul (mult g : ℝ)
        exact intervalIntegrable_const.add (((hsum_int.add intervalIntegrable_const).add
          intervalIntegrable_const).const_mul 4)
      have ht_int : Tendsto (fun n : ℕ => ∫ t in Set.Ioc (-T) T,
            ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
              (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) -
                logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                  (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)) atTop
          (𝓝 (∫ t in Set.Ioc (-T) T, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (((1 - |t| / T : ℝ) : ℂ) * fBdry t))) := by
        refine tendsto_integral_of_dominated_convergence bound_t (fun n => ?_) hbound_int (fun n => ?_) ?_
        · have hmap : ContinuousOn (fun t : ℝ => (1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I)
              (Set.Icc (-T) T) := by fun_prop
          have hc : ContinuousOn (fun t : ℝ =>
              ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) -
                  logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                    (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)) (Set.Icc (-T) T) := by
            refine (Continuous.continuousOn (by fun_prop)).mul
              ((hR1_cont.comp hmap fun t ht => (hrect_mem n t ht).1).sub
                ((hlogL4_diff.continuousOn.comp hmap fun t ht => (hrect_mem n t ht).2).div
                  (hmap.pow 2) fun t _ h0 => by
                    have := congrArg Complex.re (eq_zero_of_pow_eq_zero h0); simp at this; linarith [heps_pos n]))
          exact (hc.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
        · have hfin_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-T) T)), t ∉ (SZ : Set ℝ) := by
            rw [ae_iff]
            have hsub : {t : ℝ | ¬ t ∉ (SZ : Set ℝ)} ⊆ (SZ : Set ℝ) := fun t ht => by simpa using ht
            exact measure_mono_null hsub (SZ.finite_toSet.measure_zero _)
          filter_upwards [ae_restrict_mem measurableSet_Ioc, hfin_ae] with t ht hnotSZ
          have htIcc : t ∈ Set.Icc (-T) T := Set.Ioc_subset_Icc_self ht
          have hmem := hrect_mem n t htIcc
          have hmemK : (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ∈ Kbox :=
            ⟨(eps n, t), ⟨⟨(heps_pos n).le, heps_le n⟩, htIcc⟩, by push_cast; ring⟩
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have hwt1 : |1 - |t| / T| ≤ 1 := by
            have habs : |t| ≤ T := abs_le.mpr htIcc
            have hdiv : |t| / T ≤ 1 := (div_le_one hTpos).mpr habs
            rw [abs_of_nonneg (by linarith)]
            linarith [div_nonneg (abs_nonneg t) hTpos.le]
          refine (mul_le_of_le_one_left (norm_nonneg _) hwt1).trans ?_
          refine (norm_sub_le _ _).trans (add_le_add
            ((hMR1 _ hmemK).trans (le_max_right _ _)) ?_)
          rw [norm_div, norm_pow]
          have hden : (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I‖ := by
            have h1 := Complex.abs_re_le_norm ((1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I)
            simp at h1; rw [abs_of_pos (by linarith [heps_pos n])] at h1; linarith [heps_pos n]
          have hden2 : (1 / 4 : ℝ) ≤ ‖(1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
            nlinarith
          have hdiv4 : ‖logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I)‖ /
              ‖(1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 ≤
              4 * ‖logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I)‖ := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg (logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I))]
          refine hdiv4.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          rw [hlogL4_split _ hmem]
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_
            ((hMlogH _ hmemK).trans (le_max_right _ _)))) le_rfl)
          dsimp [logSum]
          refine (norm_sum_le SZ _).trans (Finset.sum_le_sum fun g hg => ?_)
          rw [norm_mul, Complex.norm_natCast]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hsub : 1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I - (1 / 2 + (g : ℂ) * Complex.I) =
              (eps n : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [hsub]
          have htne : t - g ≠ 0 := fun h0 => hnotSZ (by rw [sub_eq_zero.mp h0]; exact hg)
          have htg_le : |t - g| ≤ Mdom := by
            have h1 : |t| ≤ T := abs_le.mpr htIcc
            have h2 : |g| ≤ T := ((hSZ_mem g).mp hg).1
            dsimp [Mdom]; linarith [abs_sub t g]
          have heM : eps n ≤ Mdom := by dsimp [Mdom]; linarith [heps_le n]
          -- Note: norm_complex_log_le_of_re_pos needs u ≠ 0 inside; prove directly here!
          set z : ℂ := (eps n : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I
          have hzpos : 0 < ‖z‖ := by
            have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
            have hzre : z.re = eps n := by simp [z]
            rw [hzre, abs_of_pos (heps_pos n)] at h1
            linarith [heps_pos n]
          have hz_ge : |t - g| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
          have hz_le : ‖z‖ ≤ 2 * Mdom := by
            calc
              ‖z‖ ≤ ‖(eps n : ℂ)‖ + ‖((t - g : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
              _ = eps n + |t - g| := by
                    rw [Complex.norm_real, Real.norm_of_nonneg (heps_pos n).le, norm_mul,
                      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
              _ ≤ 2 * Mdom := by linarith
          have hlog_abs : |Real.log ‖z‖| ≤ abs (Real.log |t - g|) + Real.log (2 * Mdom) := by
            have hlog2M : 0 ≤ Real.log (2 * Mdom) := Real.log_nonneg (by linarith)
            by_cases h1 : 1 ≤ ‖z‖
            · rw [abs_of_nonneg (Real.log_nonneg h1)]
              linarith [Real.log_le_log hzpos hz_le, abs_nonneg (Real.log |t - g|)]
            · push Not at h1
              rw [abs_of_nonpos (Real.log_nonpos hzpos.le h1.le)]
              have hle := Real.log_le_log (abs_pos.mpr htne) hz_ge
              linarith [neg_le_abs (Real.log |t - g|)]
          have hdef : Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I :=
            Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im])
          rw [hdef]
          calc
            ‖(Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I‖
                ≤ ‖(Real.log ‖z‖ : ℂ)‖ + ‖(Complex.arg z : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = |Real.log ‖z‖| + |Complex.arg z| := by
                  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
                    Complex.norm_real, Real.norm_eq_abs]
            _ ≤ abs (Real.log |t - g|) + Real.log (2 * Mdom) + Real.pi := by
                  linarith [Complex.abs_arg_le_pi z]
        · have hfin_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-T) T)), t ∉ (SZ : Set ℝ) := by
            rw [ae_iff]
            have hsub : {t : ℝ | ¬ t ∉ (SZ : Set ℝ)} ⊆ (SZ : Set ℝ) := fun t ht => by simpa using ht
            exact measure_mono_null hsub (SZ.finite_toSet.measure_zero _)
          filter_upwards [ae_restrict_mem measurableSet_Ioc, hfin_ae] with t ht hnotSZ
          have htIcc : t ∈ Set.Icc (-T) T := Set.Ioc_subset_Icc_self ht
          have hbase_mem : (1 / 2 + (t : ℂ) * Complex.I) ∈ Rect :=
            ⟨by simp; linarith, by simp; linarith, by simp; linarith [htIcc.1], by simp; linarith [htIcc.2]⟩
          have hz_tend : Tendsto (fun n : ℕ => (1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I)
              atTop (𝓝 (1 / 2 + (t : ℂ) * Complex.I)) := by
            have hc : Tendsto (fun n : ℕ => (eps n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
              simpa only [Function.comp_def, Complex.ofReal_zero] using
                (Complex.continuous_ofReal.tendsto 0).comp heps_tend
            simpa using (hc.const_add (1 / 2 : ℂ)).add_const ((t : ℂ) * Complex.I)
          have hR1_tend : Tendsto (fun n : ℕ => R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I))
              atTop (𝓝 (R1 (1 / 2 + (t : ℂ) * Complex.I))) :=
            (hR1_cont.continuousAt (hRect_open.mem_nhds hbase_mem)).tendsto.comp hz_tend
          have hlogH_tend : Tendsto (fun n : ℕ => logH (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I))
              atTop (𝓝 (logH (1 / 2 + (t : ℂ) * Complex.I))) :=
            (hlogH_cont.continuousAt (hRect_open.mem_nhds hbase_mem)).tendsto.comp hz_tend
          have hlogSum_tend : Tendsto (fun n : ℕ => logSum (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I))
              atTop (𝓝 (∑ g ∈ SZ, (mult g : ℂ) * Complex.log (((t - g : ℝ) : ℂ) * Complex.I))) := by
            refine tendsto_finsetSum SZ fun g hg => ?_
            have htne : t - g ≠ 0 := fun h0 => hnotSZ (by rw [sub_eq_zero.mp h0]; exact hg)
            have hslit : (((t - g : ℝ) : ℂ) * Complex.I) ∈ Complex.slitPlane :=
              Or.inr (by simpa using htne)
            have harg_t : Tendsto (fun n : ℕ =>
                (1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I - (1 / 2 + (g : ℂ) * Complex.I))
                atTop (𝓝 (((t - g : ℝ) : ℂ) * Complex.I)) := by
              have hc : Tendsto (fun n : ℕ => (eps n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
                simpa only [Function.comp_def, Complex.ofReal_zero] using
                  (Complex.continuous_ofReal.tendsto 0).comp heps_tend
              have h0 : (0 : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I = ((t - g : ℝ) : ℂ) * Complex.I := zero_add _
              rw [← h0]
              exact (hc.add_const (((t - g : ℝ) : ℂ) * Complex.I)).congr fun n => by push_cast; ring
            exact (((hasDerivAt_id (((t - g : ℝ) : ℂ) * Complex.I)).clog hslit).continuousAt.tendsto.comp harg_t).const_mul _
          have hlogL4_tend : Tendsto (fun n : ℕ => logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I))
              atTop (𝓝 ((∑ g ∈ SZ, (mult g : ℂ) * Complex.log (((t - g : ℝ) : ℂ) * Complex.I)) +
                logH (1 / 2 + (t : ℂ) * Complex.I) + c0)) := by
            refine ((hlogSum_tend.add hlogH_tend).add_const c0).congr fun n => ?_
            exact (hlogL4_split _ (hrect_mem n t htIcc)).symm
          have hden_ne : (1 / 2 + (t : ℂ) * Complex.I) ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => by
            have := congrArg Complex.re h; simp at this)
          have htot := (hR1_tend.sub (hlogL4_tend.div (hz_tend.pow 2) hden_ne)).const_mul
            (((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
          refine htot.trans ?_
          dsimp [fBdry]; ring_nf; exact le_rfl
      simp_rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact (Complex.continuous_re.tendsto _).comp (ht_int.const_mul _)
    -- Apply ge_of_tendsto to pass to the limit n → ∞!
    have htend_rhs := ((htend_poles.add htend_smooth).add_const (C_fin / (x - u1) ^ 2)).add_const
      ((41 / 10 : ℝ) * (2 * fejerConst / Real.pi))
    exact ge_of_tendsto htend_rhs (Filter.Eventually.of_forall hnonneg_n)
  -- Step 6e: Take x = k - 1/T → ∞!
  have hx_tend : Tendsto (fun k : ℕ => (k : ℝ) - 1 / T) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + (-(1 / T))) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact h1.congr fun k => by ring
  have hRL_tend : Tendsto (fun k : ℕ =>
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (((k : ℝ) - 1 / T : ℝ) : ℂ) * Complex.I) *
          (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re) atTop (𝓝 0) := by
    have h1 := (tendsto_integral_exp_Icc hTpos (fun t => ((1 - |t| / T : ℝ) : ℂ) * fBdry t)).comp hx_tend
    have h2 := (Complex.continuous_re.tendsto ((((1 / (2 * Real.pi) : ℝ) : ℂ) * 0))).comp
      (h1.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ)))
    simpa only [Function.comp_def, mul_zero, Complex.zero_re] using h2
  have hfin_tend : Tendsto (fun k : ℕ => C_fin / (((k : ℝ) - 1 / T) - u1) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (((k : ℝ) - 1 / T) - u1) ^ 2) atTop atTop := by
      have hlin : Tendsto (fun k : ℕ => ((k : ℝ) - 1 / T) - u1) atTop atTop := by
        have h0 := hx_tend.atTop_add (tendsto_const_nhds (x := -u1))
        exact h0.congr fun k => by ring
      exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hlin
    exact tendsto_const_nhds.div_atTop h1
  have htail_tend : Tendsto (fun k : ℕ =>
      (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
        Complex.exp ((g : ℂ) * (((k : ℝ) - 1 / T : ℝ) : ℂ) * Complex.I) *
        ∫ v in Set.Ici ((k : ℝ) - 1 / T),
          Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re) atTop (𝓝 0) := by
    have hsum0 : (0 : ℝ) = ∑ _g ∈ SZ, (0 : ℝ) := by simp
    rw [hsum0]
    simp_rw [Complex.re_sum]
    refine tendsto_finsetSum SZ fun g _ => ?_
    have hnorm0 : Tendsto (fun k : ℕ =>
        ‖((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          Complex.exp ((g : ℂ) * (((k : ℝ) - 1 / T : ℝ) : ℂ) * Complex.I) *
          ∫ v in Set.Ici ((k : ℝ) - 1 / T),
            Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)‖) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun k : ℕ =>
          ‖(mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)‖ * (2 / (Real.pi * T * ((k : ℝ) - 1 / T)))) ?_ ?_
      · refine Filter.eventually_atTop.mpr ⟨2, fun k hk => ?_⟩
        set x : ℝ := (k : ℝ) - 1 / T
        have hxpos : 0 < x := by
          have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          have h1T : 1 / T ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hT
          dsimp [x]; linarith
        rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, norm_mul,
          show (g : ℂ) * (x : ℂ) * Complex.I = ((g * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [integral_Ici_eq_integral_Ioi]
        calc
          ‖∫ v in Set.Ioi x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)‖
              ≤ ∫ v in Set.Ioi x, ‖Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)‖ :=
                norm_integral_le_integral_norm _
          _ ≤ ∫ v in Set.Ioi x, (2 / (Real.pi * T)) * v ^ (-2 : ℝ) := by
                refine setIntegral_mono_on
                  (((integrable_fejerK hTpos).integrableOn).mono'
                    (((by fun_prop : Continuous fun v : ℝ =>
                      Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I))).aestronglyMeasurable.mul
                      ((Complex.continuous_ofReal.measurable.comp (measurable_fejerK T)).aestronglyMeasurable)).norm)
                    (by
                      filter_upwards with v
                      rw [norm_norm, norm_mul,
                        show -((g : ℂ) * (v : ℂ) * Complex.I) = ((-(g * v) : ℝ) : ℂ) * Complex.I by
                          push_cast; ring,
                        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
                        Real.norm_of_nonneg (fejerK_nonneg hTpos _)]))
                  ((integrableOn_Ioi_rpow_of_lt (by norm_num) hxpos).const_mul _) measurableSet_Ioi fun v hv => ?_
                have hvpos : 0 < v := hxpos.trans hv
                rw [norm_mul,
                  show -((g : ℂ) * (v : ℂ) * Complex.I) = ((-(g * v) : ℝ) : ℂ) * Complex.I by
                    push_cast; ring,
                  Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
                  Real.norm_of_nonneg (fejerK_nonneg hTpos _)]
                calc
                  fejerK T v ≤ 2 / (Real.pi * T * v ^ 2) := fejerK_le_tail hTpos hvpos.ne'
                  _ = (2 / (Real.pi * T)) * v ^ (-2 : ℝ) := by
                        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hvpos.le,
                          Real.rpow_natCast]; ring
          _ = 2 / (Real.pi * T * x) := by
                rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hxpos]
                rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
                field_simp [Real.pi_pos.ne', hTpos.ne', hxpos.ne']
      · have hlin : Tendsto (fun k : ℕ => Real.pi * T * ((k : ℝ) - 1 / T)) atTop atTop :=
          hx_tend.const_mul_atTop (by positivity)
        simpa using (tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop hlin).const_mul
          ‖(mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)‖
    exact squeeze_zero_norm (fun k => Complex.abs_re_le_norm _) hnorm0
  let errK : ℕ → ℝ := fun k =>
    -(∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
      Complex.exp ((g : ℂ) * (((k : ℝ) - 1 / T : ℝ) : ℂ) * Complex.I) *
      ∫ v in Set.Ici ((k : ℝ) - 1 / T),
        Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re +
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (((k : ℝ) - 1 / T : ℝ) : ℂ) * Complex.I) *
        (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re +
    C_fin / (((k : ℝ) - 1 / T) - u1) ^ 2
  have herr_tend : Tendsto errK atTop (𝓝 0) := by
    simpa [errK] using (htail_tend.neg.add hRL_tend).add hfin_tend
  have hC4_pos : 0 < 4 * fejerConst / Real.pi := by
    have := fejerConst_pos; positivity
  have hC2_pos : 0 < 2 * fejerConst / Real.pi := by
    have := fejerConst_pos; positivity
  have herr_small : ∀ᶠ k : ℕ in atTop, errK k ≤ 2 * fejerConst / Real.pi := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp herr_tend) (2 * fejerConst / Real.pi) hC2_pos
    refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
    have h1 := hN k hk
    rw [Real.dist_eq, sub_zero] at h1
    linarith [(abs_lt.mp h1).2]
  have hk_big : ∀ᶠ k : ℕ in atTop, u1 + 1 < (k : ℝ) - 1 / T := by
    refine Filter.eventually_atTop.mpr ⟨⌈u1 + 2⌉₊, fun k hk => ?_⟩
    have h1 : u1 + 2 ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
    have h1T : 1 / T ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hT
    linarith
  filter_upwards [herr_small, hk_big] with k hk_err hk_x
  set x : ℝ := (k : ℝ) - 1 / T
  have hineq := hmain_x x hk_x
  have hsplit_pole : (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
      Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
      ∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re =
      (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
        Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
        (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ))).re -
      (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
        Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
        ∫ v in Set.Ici x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re := by
    simp_rw [Complex.re_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hint_g : Integrable (fun v : ℝ =>
        Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)) := by
      refine (integrable_fejerK hTpos).mono'
        ((by fun_prop : Continuous fun v : ℝ =>
          Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I))).aestronglyMeasurable.mul
          (Complex.continuous_ofReal.measurable.comp (measurable_fejerK T)).aestronglyMeasurable) ?_
      filter_upwards with v
      rw [norm_mul,
        show -((g : ℂ) * (v : ℂ) * Complex.I) = ((-(g * v) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (fejerK_nonneg hTpos _)]
    have hadd : (∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)) +
        (∫ v in Set.Ici x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)) =
        (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ) := by
      rw [← setIntegral_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici hint_g.integrableOn hint_g.integrableOn,
        Set.Iio_union_Ici, setIntegral_univ, integral_exp_mul_fejerK hTpos ((hSZ_mem g).mp hg).1]
    have hsub : ∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ) =
        (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ) -
        ∫ v in Set.Ici x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ) := by
      linear_combination hadd
    rw [hsub, mul_sub, Complex.sub_re]
  have hpair_sum : (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
      Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
      (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ))).re =
      -((4 * fejerConst / Real.pi) *
        ∑ g ∈ Z, let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (-g / T) : ℂ)
          ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
            ((1 - g / T) * (-(v.re / 2 + g * v.im)) / (1 / 4 + g ^ 2))) := by
    dsimp only [SZ]
    rw [Complex.re_sum, Finset.sum_union hZ_disj, Finset.sum_image (fun a _ b _ h => neg_injective h),
      ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg0 : 0 < g := ((hZ g).mp hg).1
    have hv_eq : (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (-g / T) : ℂ) =
        Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) := by
      have hpow_c : ∀ n : ℕ, (((Circle.exp g : Circle) ^ n : Circle) : ℂ) = ((Circle.exp g : ℂ)) ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ m ih => rw [pow_succ, pow_succ, Circle.coe_mul, ih]
      rw [hpow_c k, Circle.coe_exp, Circle.coe_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; dsimp [x]; push_cast; ring
    have hterm_re : (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
        Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
        (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ)).re =
        (2 * fejerConst / Real.pi) * ((mult g : ℝ) *
          ((1 - g / T) * ((Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I)).re / 2 +
            g * (Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I)).im) / (1 / 4 + g ^ 2))) := by
      rw [abs_of_pos hg0]
      have hdiv_eq : (1 : ℂ) / (1 / 2 + (g : ℂ) * Complex.I) =
          (((1 / 2 : ℝ) : ℂ) - (g : ℂ) * Complex.I) / (((1 / 4 + g ^ 2 : ℝ) : ℂ)) := by
        have h1 : (1 / 2 : ℂ) + (g : ℂ) * Complex.I ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this
        have h2 : ((1 / 4 + g ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
        rw [div_eq_div_iff h1 h2]
        push_cast
        linear_combination (g : ℂ) ^ 2 * Complex.I_sq
      have hrew : ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
          (((2 * fejerConst / Real.pi) * (1 - g / T) : ℝ) : ℂ) =
          (((2 * fejerConst / Real.pi) * (mult g : ℝ) * (1 - g / T) / (1 / 4 + g ^ 2) : ℝ) : ℂ) *
            ((((1 / 2 : ℝ) : ℂ) - (g : ℂ) * Complex.I) * Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I)) := by
        rw [div_eq_mul_inv, (one_div (1 / 2 + (g : ℂ) * Complex.I)).symm, hdiv_eq]
        push_cast; ring
      rw [hrew, Complex.re_ofReal_mul]
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_im, Complex.sub_im,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hneg_re : (((mult (-g) : ℂ) / (1 / 2 + ((-g : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((-g : ℝ) : ℂ) * (x : ℂ) * Complex.I) *
        (((2 * fejerConst / Real.pi) * (1 - |-g| / T) : ℝ) : ℂ)).re =
        (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
          (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ)).re := by
      have hconj : starRingEnd ℂ (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
          (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ)) =
          ((mult (-g) : ℂ) / (1 / 2 + ((-g : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((-g : ℝ) : ℂ) * (x : ℂ) * Complex.I) *
          (((2 * fejerConst / Real.pi) * (1 - |-g| / T) : ℝ) : ℂ) := by
        rw [hmult_neg g, abs_neg]
        simp only [map_mul, map_div₀, map_natCast, map_add, map_one, map_ofNat,
          Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj]
        push_cast; ring
      rw [← hconj, Complex.conj_re]
    rw [hneg_re, hterm_re, hv_eq]
    dsimp [mult]; ring
  rw [hsplit_pole, hpair_sum] at hineq
  have hS_le : (4 * fejerConst / Real.pi) *
      (∑ g ∈ Z, let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (-g / T) : ℂ)
        ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (-(v.re / 2 + g * v.im)) / (1 / 4 + g ^ 2))) ≤
      (4 * fejerConst / Real.pi) * 3 := by
    have h41 : (41 / 10 : ℝ) * (2 * fejerConst / Real.pi) + 2 * fejerConst / Real.pi ≤
        (4 * fejerConst / Real.pi) * 3 := by
      have := fejerConst_pos
      have := Real.pi_pos
      have hle : (102 / 10 : ℝ) * (fejerConst / Real.pi) ≤ 12 * (fejerConst / Real.pi) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      have he1 : (41 / 10 : ℝ) * (2 * fejerConst / Real.pi) + 2 * fejerConst / Real.pi =
          (102 / 10 : ℝ) * (fejerConst / Real.pi) := by ring
      have he2 : (4 * fejerConst / Real.pi) * 3 = 12 * (fejerConst / Real.pi) := by ring
      linarith
    dsimp [errK] at hk_err
    linarith
  exact le_of_mul_le_mul_left hS_le hC4_pos

/- ### Part D: Compact-group recurrence and final contradiction -/

private lemma trig_bounds_upper {g T : ℝ} (hg : 0 < g) (hT : 0 < T) (hle : g ≤ T) :
    0 ≤ (1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2) ∧
    (1 - g / T) * (Real.cos (g / T) / 2) / (1 / 4 + g ^ 2) ≤ (1 / 2) / (1 / 4 + g ^ 2) ∧
    (1 ≤ g → g ≤ T / 2 →
      1 / (8 * T) ≤ (1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)) := by
  have h0 : 0 ≤ g / T := div_nonneg hg.le hT.le
  have h1 : g / T ≤ 1 := (div_le_one hT).mpr hle
  have hp : g / T ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcos_le1 : Real.cos (g / T) ≤ 1 := Real.cos_le_one _
  have hcos_nn : 0 ≤ Real.cos (g / T) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hp⟩
  have hsin : (g / T) / 2 ≤ Real.sin (g / T) := by
    have hcoef : (1 : ℝ) / 2 ≤ 2 / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    exact (show (g / T) / 2 ≤ 2 / Real.pi * (g / T) by
      nlinarith [mul_le_mul_of_nonneg_right hcoef h0]).trans (Real.mul_le_sin h0 hp)
  have hden : 0 < (1 : ℝ) / 4 + g ^ 2 := by positivity
  refine ⟨div_nonneg (mul_nonneg (by linarith) (mul_nonneg hg.le (by linarith))) hden.le, ?_, ?_⟩
  · refine div_le_div_of_nonneg_right ?_ hden.le
    have h1g : 1 - g / T ≤ 1 := by linarith
    have h1g_nn : 0 ≤ 1 - g / T := by linarith
    nlinarith
  · intro hg1 hhalf
    apply (le_div_iff₀ hden).mpr
    calc
      1 / (8 * T) * (1 / 4 + g ^ 2) ≤ (1 / 2) * (g * ((g / T) / 2)) := by
        field_simp
        nlinarith [sq_nonneg (g - 1)]
      _ ≤ (1 - g / T) * (g * Real.sin (g / T)) := by
        apply mul_le_mul _ _ (by positivity) (by linarith)
        · have ht : g / T ≤ 1 / 2 := (div_le_iff₀ hT).mpr (by linarith)
          linarith
        · exact mul_le_mul_of_nonneg_left hsin hg.le

end ChebyshevBiasR1H2Proof

theorem OMA.solution : OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1.H2 := by
  classical
  intro N
  by_contra hn
  have hup : ∀ᶠ n : ℕ in atTop, ChebyshevBiasR1H2Proof.JVal n ≤ 4 * (Real.sqrt n / Real.log n) := by
    filter_upwards [eventually_ge_atTop N] with n hnN
    exact le_of_not_gt fun hgt => hn ⟨n, hnN, hgt⟩
  have hRH := ChebyshevBiasR1H2Proof.landau_zero_free_upper hup
  obtain ⟨C0, hC0_nn, hC0⟩ := ChebyshevBiasR1H2Proof.sum_inv_sq_zeros_bounded
  let M : ℝ := 8 * (C0 / 2 + 10)
  have hM_pos : 0 < M := by dsimp [M]; linarith
  obtain ⟨T, Z, hT, hZ, hmass⟩ := ChebyshevBiasR1H2Proof.critical_line_zero_count_param M hM_pos hRH
  have hTpos : 0 < T := by linarith
  let w (g : ℝ) : ℝ :=
    ((analyticOrderAt ChebyshevBiasR1H2Proof.L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ)
  let C : Finset ℝ := Z.filter (fun g => 1 ≤ g ∧ g ≤ T / 2)
  let termPos (g : ℝ) : ℝ := (1 - g / T) * (g * Real.sin (g / T)) / (1 / 4 + g ^ 2)
  let termNeg (g : ℝ) : ℝ := (1 - g / T) * (Real.cos (g / T) / 2) / (1 / 4 + g ^ 2)
  have hpos_lower : C0 / 2 + 10 < ∑ g ∈ Z, w g * termPos g := by
    have hbound : (∑ g ∈ C, w g) / (8 * T) ≤ ∑ g ∈ C, w g * termPos g := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun g hg => ?_
      obtain ⟨hgZ, hg1, hg2⟩ := Finset.mem_filter.mp hg
      obtain ⟨hg0, hgle, _⟩ := (hZ g).mp hgZ
      have hh := (ChebyshevBiasR1H2Proof.trig_bounds_upper hg0 hTpos hgle).2.2 hg1 hg2
      simpa only [termPos, div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hh (show 0 ≤ w g by dsimp [w]; positivity)
    have hinc : ∑ g ∈ C, w g * termPos g ≤ ∑ g ∈ Z, w g * termPos g := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g hg _ => ?_
      obtain ⟨hg0, hgle, _⟩ := (hZ g).mp hg
      exact mul_nonneg (by dsimp [w]; positivity)
        (ChebyshevBiasR1H2Proof.trig_bounds_upper hg0 hTpos hgle).1
    have hlt : C0 / 2 + 10 < (∑ g ∈ C, w g) / (8 * T) :=
      (lt_div_iff₀ (by positivity)).mpr (by dsimp [M, C, w] at hmass ⊢; linarith)
    exact lt_of_lt_of_le hlt (hbound.trans hinc)
  have hneg_upper : ∑ g ∈ Z, w g * termNeg g ≤ C0 / 2 := by
    calc
      ∑ g ∈ Z, w g * termNeg g
          ≤ ∑ g ∈ Z, w g * ((1 / 2) / (1 / 4 + g ^ 2)) := by
            refine Finset.sum_le_sum fun g hg => ?_
            obtain ⟨hg0, hgle, _⟩ := (hZ g).mp hg
            exact mul_le_mul_of_nonneg_left
              (ChebyshevBiasR1H2Proof.trig_bounds_upper hg0 hTpos hgle).2.1
              (by dsimp [w]; positivity)
      _ = (1 / 2) * ∑ g ∈ Z, w g / (1 / 4 + g ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun g _ => by ring
      _ ≤ (1 / 2) * C0 := mul_le_mul_of_nonneg_left (hC0 T Z hT hZ) (by norm_num)
      _ = C0 / 2 := by ring
  let phase (z : ℝ → Circle) : ℝ :=
    ∑ g ∈ Z, let v := (z g : ℂ) * (Circle.exp (-g / T) : ℂ)
      w g * ((1 - g / T) * (-(v.re / 2 + g * v.im)) / (1 / 4 + g ^ 2))
  have hc : Continuous phase := by dsimp only [phase]; fun_prop
  have atOne : 3 < phase 1 := by
    have heq : phase 1 = (∑ g ∈ Z, w g * termPos g) - (∑ g ∈ Z, w g * termNeg g) := by
      dsimp only [phase, termPos, termNeg]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hr : (Circle.exp (-g / T) : ℂ).re = Real.cos (g / T) := by
        rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, neg_div, Real.cos_neg]
      have hi : (Circle.exp (-g / T) : ℂ).im = -Real.sin (g / T) := by
        rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im, neg_div, Real.sin_neg]
      simp only [Pi.one_apply, Circle.coe_one, one_mul, hr, hi]
      ring
    rw [heq]
    linarith
  let a (g : ℝ) : Circle := Circle.exp g
  have hrec := mapClusterPt_one_atTop_pow a
  have hnear : {z : ℝ → Circle | 3 < phase z} ∈ 𝓝 1 :=
    hc.continuousAt.eventually (lt_mem_nhds atOne)
  have often := (mapClusterPt_iff_frequently.mp hrec) _ hnear
  have tail := ChebyshevBiasR1H2Proof.fejer_explicit_formula_upper hup hRH T Z hT hZ
  obtain ⟨k, hlo, hhi⟩ := (often.and_eventually tail).exists
  exact (not_lt_of_ge hhi) hlo
