import OMAReductions.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1
import Mathlib

/-!
Under the zero-free half-plane for the Dirichlet L-function of the nontrivial real character
modulo 4, the critical-line zero count with multiplicity eventually exceeds any fixed linear
multiple of the height. We prove this by contradiction via an annulus-blocked canonical
product, a holomorphic logarithm on C, and an elementary Fourier-coefficient growth bound.
-/

open Filter Finset Real Complex MeasureTheory Topology
open scoped Nat

namespace ChebyshevBiasH2Proof

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

/- ### Step 2: Elementary Gamma growth and factorial lower bound -/

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

/- ### Step 5: Main proof of H2 by contradiction -/

set_option maxHeartbeats 1600000 in
private theorem critical_line_zero_count
    (hRH : ∀ s : ℂ, 1 / 2 < s.re → L4 s ≠ 0) :
    ∃ (T : ℝ) (Z : Finset ℝ), 2 ≤ T ∧
      (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0) ∧
      32 * T < ∑ g ∈ Z.filter (fun g => 1 ≤ g ∧ g ≤ T / 2),
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
        ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) ≤ 32 * T := by
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
  have hNcount_le : ∀ K : ℕ, Ncount K ≤ w 0 + 64 * (K : ℝ) := by
    intro K
    rcases K with _ | K
    · simp [Ncount, hw_nn 0]
    · by_cases hK0 : K = 0
      · subst hK0; simp [Ncount]
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
        have hT64 : 32 * T = 64 * ((K + 1 : ℕ) : ℝ) := by dsimp [T]; push_cast; ring
        linarith
  -- Step 5c: Tail convergence of ∑_{k ≥ K0} w k / k^2 ≤ 5 * C0 / K0
  let C0 : ℝ := w 0 + 64
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
    -- Apply hP_local on Metric.ball (1/2) (R + 1) with K0 = K_hi (since 2*(R+1) ≤ 4*X + 2 ≤ K_hi)
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

end ChebyshevBiasH2Proof

theorem OMA.solution : OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1.H2 := by
  intro hRH
  exact ChebyshevBiasH2Proof.critical_line_zero_count hRH
