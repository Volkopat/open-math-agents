import OMAReductions.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1
import Mathlib

/-!
One-sided Fejer explicit-formula bound for the Dirichlet L-function of the nontrivial real
character modulo 4 under the half-plane zero-free hypothesis.
-/

open Filter Finset Real Complex MeasureTheory Topology
open scoped Nat

namespace ChebyshevBiasH3Proof

/-- The nontrivial real Dirichlet character modulo 4 valued in complex numbers. -/
noncomputable def χ4 : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The Dirichlet L-function of χ4. -/
noncomputable def L4 : ℂ → ℂ :=
  DirichletCharacter.LFunction χ4

/-- Real-valued prime-power coefficient underlying log L(s, χ4). -/
noncomputable def aCoeff (n : ℕ) : ℝ :=
  (ZMod.χ₄ (n : ZMod 4) : ℝ) * ArithmeticFunction.vonMangoldt n / Real.log n

/-- The weighted prime-power sum appearing in the hypothesis. -/
noncomputable def JVal (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 n),
    ∑ p ∈ (Nat.primesLE n).filter (fun p => p ^ (j + 1) ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ (j + 1) / (j + 1 : ℕ)

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

private lemma L4_differentiable : Differentiable ℂ L4 :=
  DirichletCharacter.differentiable_LFunction χ4_ne_one

private lemma L4_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : L4 s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ4 (Or.inl χ4_ne_one) hs

/- ### Step 1: Alternating series, positivity on (0, ∞), conjugation symmetry, and JVal -/

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
        = -((b : ℂ) ^ (-s)) - -((a : ℂ) ^ (-s)) := by dsimp [a, b]; push_cast; ring
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
  have hbound : ∀ t ∈ Set.uIoc a b, ‖(t : ℂ) ^ (-(s + 1))‖ ≤ a ^ (-(s.re + 1)) := by
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
        _ ≤ 2 * (‖s₀‖ + δ) * ((4 * k + 1 : ℕ) : ℝ) ^ (-(δ + 1)) :=
          mul_le_mul (by linarith) hpow (by positivity) (by positivity)
  exact (hdiff_ball.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))).differentiableWithinAt

private lemma L4_eq_altSum_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    L4 s = ∑' k : ℕ, altTerm k s := by
  rw [L4, DirichletCharacter.LFunction_eq_LSeries χ4 hs]
  have hsumL : LSeriesSummable (fun n : ℕ => χ4 (n : ZMod 4)) s :=
    ZMod.LSeriesSummable_of_one_lt_re χ4 hs
  have hsumAlt : Summable (fun k : ℕ => altTerm k s) :=
    Summable.of_norm_bounded (g := fun k : ℕ => 2 * ‖s‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(s.re + 1)))
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
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> norm_num <;> omega
      have h1 : χ4 ((4 * K + 1 : ℕ) : ZMod 4) = 1 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> norm_num <;> omega
      have h2 : χ4 ((4 * K + 2 : ℕ) : ZMod 4) = 0 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> norm_num <;> omega
      have h3 : χ4 ((4 * K + 3 : ℕ) : ZMod 4) = -1 := by
        rw [χ4_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> norm_num <;> omega
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
      LSeries.term (fun n : ℕ => χ4 (n : ZMod 4)) s n) atTop
      (𝓝 (LSeries (fun n : ℕ => χ4 (n : ZMod 4)) s)) :=
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
    ∃ r : ℝ, 0 < r ∧ L4 (σ : ℂ) = (r : ℂ) := by
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
    exact (Complex.reCLM.summable hC).congr fun k => by simp [hterm k]
  refine ⟨∑' k : ℕ, (((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ)), ?_, rfl⟩
  refine hsum.tsum_pos (fun k => ?_) 0 ?_
  · have hlt : ((4 * k + 3 : ℕ) : ℝ) ^ (-σ) < ((4 * k + 1 : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_lt_rpow_of_neg (by positivity) (by norm_cast; omega) (by linarith)
    linarith
  · have hlt : ((4 * 0 + 3 : ℕ) : ℝ) ^ (-σ) < ((4 * 0 + 1 : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_lt_rpow_of_neg (by positivity) (by norm_cast) (by linarith)
    linarith

private lemma L4_real_ne_zero {σ : ℝ} (hσ : 0 < σ) : L4 (σ : ℂ) ≠ 0 := by
  obtain ⟨r, hr, heq⟩ := L4_real_pos hσ
  rw [heq]; exact Complex.ofReal_ne_zero.mpr hr.ne'

private lemma differentiableAt_conj_comp {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (starRingEnd ℂ z)) :
    DifferentiableAt ℂ (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) z := by
  have h1 := hf.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1
  have hcomp : Tendsto (fun t : ℂ => starRingEnd ℂ
      ((starRingEnd ℂ t)⁻¹ • (f (starRingEnd ℂ z + starRingEnd ℂ t) - f (starRingEnd ℂ z))))
      (𝓝[≠] (0 : ℂ)) (𝓝 (starRingEnd ℂ (deriv f (starRingEnd ℂ z)))) := by
    have ht : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (map_ne_zero (starRingEnd ℂ)).mpr ht
    exact (Complex.continuous_conj.tendsto _).comp (h1.comp ht)
  have h2 : HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w)))
      (starRingEnd ℂ (deriv f (starRingEnd ℂ z))) z := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine hcomp.congr fun t => ?_
    simp only [smul_eq_mul, map_mul, map_inv₀, map_sub, map_add, Complex.conj_conj]
  exact h2.differentiableAt

private lemma L4_conj (s : ℂ) : L4 (starRingEnd ℂ s) = starRingEnd ℂ (L4 s) := by
  have hconj_diff : Differentiable ℂ (fun z => starRingEnd ℂ (L4 (starRingEnd ℂ z))) :=
    fun z => differentiableAt_conj_comp (L4_differentiable (starRingEnd ℂ z))
  have han1 : AnalyticOnNhd ℂ L4 Set.univ := L4_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have han2 : AnalyticOnNhd ℂ (fun z => starRingEnd ℂ (L4 (starRingEnd ℂ z))) Set.univ :=
    hconj_diff.differentiableOn.analyticOnNhd isOpen_univ
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

/- ### Step 3: Fejer kernel K_T and its exact cosine transform -/

/-- The normalized Fejer kernel K_T(v) = (1 - cos(T*v)) / (π * T * v^2). -/
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
  -- Replace γ with |γ| since cos(|γ|*v) = cos(γ*v)
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

/- ### Step 6: Main proof of H3 -/

set_option maxHeartbeats 1600000 in
private theorem fejer_explicit_formula
    (hJ : ∀ᶠ n : ℕ in atTop, -(Real.sqrt n / Real.log n) ≤ JVal n)
    (hRH : ∀ s : ℂ, 1 / 2 < s.re → L4 s ≠ 0)
    (T : ℝ) (Z : Finset ℝ) (hT : 2 ≤ T)
    (hZ : ∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L4 (1 / 2 + (g : ℂ) * Complex.I) = 0) :
    ∀ᶠ k : ℕ in atTop,
      (∑ g ∈ Z, let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g / T) : ℂ)
                ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
                  ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2))) ≤ 2 := by
  classical
  have hTpos : 0 < T := by linarith
  -- Step 6a: Global holomorphic logarithm logL4 on Hhalf = {s | 1/2 < s.re}
  let Hhalf : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  have hH_open : IsOpen Hhalf := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hH_conv : Convex ℝ Hhalf := convex_halfSpace_re_gt (1 / 2)
  have h2_mem : (2 : ℂ) ∈ Hhalf := by simp [Hhalf]; norm_num
  obtain ⟨r2, hr2pos, hr2eq⟩ := L4_real_pos (by norm_num : (0 : ℝ) < 2)
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
  have hN0_J : ∀ n : ℕ, N0 ≤ n → -(Real.sqrt n / Real.log n) ≤ JVal n :=
    fun n hn => hN0_raw n (le_trans (le_max_left _ _) hn)
  let u1 : ℝ := max (Real.log (N0 : ℝ)) 10
  have hu1_ge10 : 10 ≤ u1 := le_max_right _ _
  have hu1_pos : 0 < u1 := by linarith
  let Gfun : ℝ → ℝ := fun u => u * jExp u + (11 / 10 : ℝ) * Real.exp (u / 2)
  have hG_meas : Measurable Gfun :=
    (measurable_id.mul measurable_jExp).add
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_id.div_const 2)))
  have hG_nonneg : ∀ u ∈ Set.Ioi u1, 0 ≤ Gfun u := by
    intro u hu
    have hu10 : 10 ≤ u := le_trans hu1_ge10 (Set.mem_Ioi.mp hu).le
    have hupos : 0 < u := by linarith
    have hN0_le_exp : (N0 : ℝ) ≤ Real.exp u := by
      have h1 : Real.log (N0 : ℝ) ≤ u := le_trans (le_max_left _ _) (Set.mem_Ioi.mp hu).le
      have hN0pos : (0 : ℝ) < (N0 : ℝ) := by positivity
      simpa [Real.exp_log hN0pos] using Real.exp_le_exp.mpr h1
    have hfl_ge : N0 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor hN0_le_exp
    have hJlow := hN0_J ⌊Real.exp u⌋₊ hfl_ge
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
    have hlog_ge : (10 / 11 : ℝ) * u ≤ Real.log (⌊Real.exp u⌋₊ : ℝ) := by
      have h1 := Real.log_le_log (by positivity : 0 < Real.exp u / 2) hfl_gt_half
      rw [Real.log_div (Real.exp_pos u).ne' two_ne_zero, Real.log_exp] at h1
      have hlog2 : Real.log 2 < 10 / 11 := by
        have h := Real.log_two_lt_d9
        linarith
      linarith
    have hlog_pos : 0 < Real.log (⌊Real.exp u⌋₊ : ℝ) := by linarith
    have hfrac : Real.sqrt (⌊Real.exp u⌋₊ : ℝ) / Real.log (⌊Real.exp u⌋₊ : ℝ) ≤
        (11 / 10 : ℝ) * Real.exp (u / 2) / u := by
      calc
        Real.sqrt (⌊Real.exp u⌋₊ : ℝ) / Real.log (⌊Real.exp u⌋₊ : ℝ)
            ≤ Real.exp (u / 2) / ((10 / 11 : ℝ) * u) :=
              div_le_div₀ (Real.exp_pos _).le hsqrt_le (by positivity) hlog_ge
        _ = (11 / 10 : ℝ) * Real.exp (u / 2) / u := by field_simp [hupos.ne']
    dsimp [Gfun, jExp]
    have hmul := mul_le_mul_of_nonneg_left (le_trans (neg_le_neg hfrac) hJlow) hupos.le
    rw [mul_neg, mul_div_cancel₀ _ hupos.ne'] at hmul
    linarith
  -- Analytic right-hand side Phi(s) on Hhalf
  let Phi : ℂ → ℂ := fun s =>
    -(deriv L4 s / (s * L4 s)) + logL4 s / s ^ 2 -
      (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ)))) +
      (11 / 10 : ℂ) * (Complex.exp (-((s - 1 / 2) * (u1 : ℂ))) / (s - 1 / 2))
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
    have h1 : DifferentiableAt ℂ (fun w => -(deriv L4 w / (w * L4 w))) s :=
      (((L4_differentiable.deriv s).div ((differentiableAt_id).mul (L4_differentiable s))
        (mul_ne_zero hsne hLne)).neg)
    have h2 : DifferentiableAt ℂ (fun w => logL4 w / w ^ 2) s :=
      (hlogL4_diff.differentiableAt (hH_open.mem_nhds hs)).div (differentiableAt_id.pow 2)
        (pow_ne_zero 2 hsne)
    have h3 : DifferentiableAt ℂ
        (fun w => (11 / 10 : ℂ) * (Complex.exp (-((w - 1 / 2) * (u1 : ℂ))) / (w - 1 / 2))) s := by
      refine (differentiableAt_const _).mul ?_
      refine ((((differentiableAt_id.sub (differentiableAt_const _)).mul
        (differentiableAt_const _)).neg).cexp).div
        (differentiableAt_id.sub (differentiableAt_const _)) hs_half_ne
    exact (((h1.add h2).sub (hint_fin_diff s)).add h3).differentiableWithinAt
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
        ((11 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
        (11 / 10 : ℂ) * (Complex.exp (-((s - 1 / 2) * (u1 : ℂ))) / (s - 1 / 2)) := by
      have hcongr : ∀ u : ℝ,
          (((11 / 10 : ℝ) * Real.exp (u / 2) : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) =
          (11 / 10 : ℂ) * Complex.exp ((-(s - 1 / 2)) * (u : ℂ)) := fun u => by
        rw [Complex.ofReal_mul, Complex.ofReal_exp]
        push_cast
        rw [mul_assoc, ← Complex.exp_add]
        congr 2; ring
      have hcongr' : Set.EqOn
          (fun u : ℝ => ((11 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))))
          (fun u : ℝ => (11 / 10 : ℂ) * Complex.exp ((-(s - 1 / 2)) * (u : ℂ))) (Set.Ioi u1) := by
        intro u _; simpa using hcongr u
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr', integral_const_mul,
        integral_exp_mul_complex_Ioi (by simp; linarith) u1]
      congr 1
      have hsne : s - 1 / 2 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      field_simp [hsne]
    have hint_exp_half : IntegrableOn
        (fun u : ℝ => ((11 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))))
        (Set.Ioi u1) := by
      have h1 := (integrableOn_exp_mul_complex_Ioi (a := -(s - 1 / 2)) (by simp; linarith) u1).const_mul
        (11 / 10 : ℂ)
      refine IntegrableOn.congr_fun h1 (fun u _ => ?_) measurableSet_Ioi
      have : (11 / 10 : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ)) =
          ((11 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
        rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
        push_cast; congr 2; ring
      simpa using this
    have hG_split : (fun u : ℝ => (Gfun u : ℂ) * Complex.exp (-(s * (u : ℂ)))) =
        fun u : ℝ => ((u * jExp u : ℝ) : ℂ) * Complex.exp (-(s * (u : ℂ))) +
          ((11 / 10 : ℝ) * Real.exp (u / 2) : ℂ) * Complex.exp (-(s * (u : ℂ))) := by
      ext u; dsimp [Gfun]; push_cast; ring
    rw [hG_split, integral_add (hint_uJ.mono_set (Set.Ioi_subset_Ioi hu1_pos.le)) hint_exp_half,
      hexp_int]
    dsimp [Phi]
    have h3 := huJ_eq s hs
    rw [hsplit] at h3
    linear_combination -h3
  -- Iterated derivatives of Phi at s = 2 via induction on k
  have hG_pow_int : ∀ (k : ℕ) {σ : ℝ}, 1 < σ →
      IntegrableOn (fun u : ℝ => |Gfun u| * u ^ k * Real.exp (-σ * u)) (Set.Ioi u1) := by
    intro k σ hσ
    have h1 := (integrableOn_jExp_pow_exp (k + 1) hσ).mono_set (Set.Ioi_subset_Ioi hu1_pos.le)
    have h2 : IntegrableOn (fun u : ℝ => (11 / 10 : ℝ) * Real.exp (u / 2) * u ^ k * Real.exp (-σ * u))
        (Set.Ioi u1) := by
      have hδ : 0 < (σ - 1 / 2) / 2 := by linarith
      have hdom : IntegrableOn
          (fun u : ℝ => (11 / 10 : ℝ) * ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) *
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
        (11 / 10 : ℝ) * Real.exp (u / 2) * u ^ k * Real.exp (-σ * u)
            ≤ (11 / 10 : ℝ) * Real.exp (u / 2) *
                (((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) * Real.exp (((σ - 1 / 2) / 2) * u)) *
                Real.exp (-σ * u) := by
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hu_le (by positivity)) (Real.exp_pos _).le
        _ = (11 / 10 : ℝ) * ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) *
              (Real.exp (u / 2) * Real.exp (((σ - 1 / 2) / 2) * u) * Real.exp (-σ * u)) := by ring
        _ = (11 / 10 : ℝ) * ((k ! : ℝ) / ((σ - 1 / 2) / 2) ^ k) *
              Real.exp (-((σ - 1 / 2) / 2) * u) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
    refine (h1.add h2).mono' ((hG_meas.abs.mul (measurable_id.pow_const k)).mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_trans hu1_pos.le (Set.mem_Ioi.mp hu).le
    rw [Real.norm_of_nonneg (by positivity)]
    have habs : |Gfun u| ≤ u * |jExp u| + (11 / 10 : ℝ) * Real.exp (u / 2) := by
      dsimp [Gfun]
      calc
        |u * jExp u + (11 / 10 : ℝ) * Real.exp (u / 2)|
            ≤ |u * jExp u| + |(11 / 10 : ℝ) * Real.exp (u / 2)| := abs_add_le _ _
        _ = u * |jExp u| + (11 / 10 : ℝ) * Real.exp (u / 2) := by
              rw [abs_mul, abs_of_nonneg hu0, abs_of_pos (mul_pos (by norm_num) (Real.exp_pos (u / 2)))]
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs (pow_nonneg hu0 k))
      (Real.exp_pos (-σ * u)).le
    have hlhs : (u * |jExp u| + (11 / 10 : ℝ) * Real.exp (u / 2)) * u ^ k * Real.exp (-σ * u) =
        |jExp u| * u ^ (k + 1) * Real.exp (-σ * u) +
          (11 / 10 : ℝ) * Real.exp (u / 2) * u ^ k * Real.exp (-σ * u) := by rw [pow_succ]; ring
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
    (∑ g ∈ SZ, (mult g : ℂ) / ((1 / 2 + (g : ℂ) * Complex.I) * s)) - deriv Hreg s / (s * Hreg s)
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
    exact h1.sub h2
  have hneg_logDeriv_split : ∀ s ∈ Rect ∩ Hhalf,
      -(deriv L4 s / (s * L4 s)) =
        -(∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
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
    R1 (1 / 2 + (t : ℂ) * Complex.I) +
      ((∑ g ∈ SZ, (mult g : ℂ) * Complex.log (((t - g : ℝ) : ℂ) * Complex.I)) +
        logH (1 / 2 + (t : ℂ) * Complex.I) + c0) / (1 / 2 + (t : ℂ) * Complex.I) ^ 2
  let C_fin : ℝ := (2 / (Real.pi * T)) * (u1 * u1 * Real.exp u1)
  have hmain_x : ∀ x : ℝ, u1 + 1 < x →
      0 ≤ -(∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
              ∫ v in Set.Iio x, Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re +
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
              (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re +
          C_fin / (x - u1) ^ 2 +
          (11 / 10 : ℝ) * (2 * fejerConst / Real.pi) := by
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
        0 ≤ -(∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
                ∫ u in Set.Ioi (0 : ℝ),
                  Complex.exp (-((eps n : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
                    (fejerK T (x - u) : ℂ))).re +
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t in (-T)..T, ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) +
                  logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                    (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)).re +
            C_fin / (x - u1) ^ 2 +
            (11 / 10 : ℝ) * (2 * fejerConst / Real.pi) := by
      intro n
      set e : ℝ := eps n
      have hepos : 0 < e := heps_pos n
      -- Helper Fubini lemma: for f integrable on Set.Ioi a,
      -- (1/(2π)) ∫_{-T}^T (1-|t|/T) e^{itx} (∫_{Ioi a} f u e^{-itu} du) dt = ∫_{Ioi a} f u K_T(x-u) du
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
          -(∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)))) +
          wt t * (R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) +
              logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) /
                (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) ^ 2) -
          wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) +
          (11 / 10 : ℂ) * (wt t * (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
              ((e : ℂ) + (t : ℂ) * Complex.I))) := by
        intro t ht
        rw [Set.uIcc_of_le (by linarith)] at ht
        have hmem := hrect_mem n t ht
        dsimp [Phi]
        rw [hneg_logDeriv_split _ hmem]
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
        linear_combination -hsum_mul
      -- Integrability of each piece on [-T, T] (all are continuous on [-T, T] since e > 0!)
      have hi_pole : ∀ g ∈ SZ, IntervalIntegrable
          (fun t : ℝ => wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))) volume (-T) T := by
        intro g _
        refine Continuous.intervalIntegrable ?_ (-T) T
        refine hwt_cont.mul (continuous_const.div (by fun_prop) fun t => ?_)
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hi_poles : IntervalIntegrable
          (fun t : ℝ => -(∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
            (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))))) volume (-T) T := by
        have hsum_eq : (fun t : ℝ => -(∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
            (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))))) =
            -(∑ g ∈ SZ, fun t : ℝ => ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I)))) := by
          ext t; simp
        rw [hsum_eq]
        exact (IntervalIntegrable.sum SZ fun g hg => (hi_pole g hg).const_mul _).neg
      have hi_smooth : IntervalIntegrable
          (fun t : ℝ => wt t * (R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) +
            logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) /
              (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) ^ 2)) volume (-T) T := by
        refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) ?_
        have hmap : ContinuousOn (fun t : ℝ => (1 / 2 : ℂ) + (e : ℂ) + (t : ℂ) * Complex.I) (Set.Icc (-T) T) := by
          fun_prop
        have hR1c : ContinuousOn (fun t : ℝ => R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc (-T) T) :=
          hR1_cont.comp hmap fun t ht => (hrect_mem n t ht).1
        have hlogc : ContinuousOn (fun t : ℝ => logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc (-T) T) :=
          hlogL4_diff.continuousOn.comp hmap fun t ht => (hrect_mem n t ht).2
        refine hwt_cont.continuousOn.mul (hR1c.add (hlogc.div (hmap.pow 2) fun t _ h0 => ?_))
        have := congrArg Complex.re (eq_zero_of_pow_eq_zero h0); simp at this; linarith
      have hi_fin : IntervalIntegrable
          (fun t : ℝ => wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))) volume (-T) T :=
        Continuous.intervalIntegrable
          (hwt_cont.mul (hint_fin_diff.continuous.comp (by fun_prop))) (-T) T
      have hi_11 : IntervalIntegrable
          (fun t : ℝ => (11 / 10 : ℂ) * (wt t * (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
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
          ∫ t in (-T)..T, (11 / 10 : ℂ) * (wt t *
            (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
              ((e : ℂ) + (t : ℂ) * Complex.I)))).re ≤
          (11 / 10 : ℝ) * (2 * fejerConst / Real.pi) := by
        have hint_e : IntegrableOn (fun u : ℝ => Complex.exp (-((e : ℂ) * (u : ℂ)))) (Set.Ioi u1) := by
          refine (integrableOn_exp_mul_Ioi (a := -e) (by linarith) u1).mono' (by fun_prop) ?_
          filter_upwards with u; rw [Complex.norm_exp]; simp [neg_mul]
        have hfub_11 := hfubini (Set.Ioi u1) measurableSet_Ioi _ hint_e
        have heq_11 : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, (11 / 10 : ℂ) * (wt t *
              (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
                ((e : ℂ) + (t : ℂ) * Complex.I))) =
            (11 / 10 : ℂ) * ∫ u in Set.Ioi u1, Complex.exp (-((e : ℂ) * (u : ℂ))) * (fejerK T (x - u) : ℂ) := by
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
        have hre_val : ((11 / 10 : ℂ) * ((∫ u in Set.Ioi u1, Real.exp (-e * u) * fejerK T (x - u) : ℝ) : ℂ)).re =
            (11 / 10 : ℝ) * ∫ u in Set.Ioi u1, Real.exp (-e * u) * fejerK T (x - u) := by
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
          -(∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (∫ u in Set.Ioi (0 : ℝ),
                Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) * (fejerK T (x - u) : ℂ))) +
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, wt t * (R1 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) +
              logL4 (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) /
                (1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) ^ 2)) -
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
              Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))) +
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, (11 / 10 : ℂ) * (wt t *
              (Complex.exp (-(((e : ℂ) + (t : ℂ) * Complex.I) * (u1 : ℂ))) /
                ((e : ℂ) + (t : ℂ) * Complex.I)))) := by
        rw [intervalIntegral.integral_congr hpiece_eq,
          intervalIntegral.integral_add ((hi_poles.add hi_smooth).sub hi_fin) hi_11,
          intervalIntegral.integral_sub (hi_poles.add hi_smooth) hi_fin,
          intervalIntegral.integral_add hi_poles hi_smooth,
          intervalIntegral.integral_neg,
          intervalIntegral.integral_finsetSum fun g hg => (hi_pole g hg).const_mul _]
        have hpoles_simp : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (-(∑ g ∈ SZ, ∫ t in (-T)..T, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              (wt t * (1 / ((e : ℂ) + ((t - g : ℝ) : ℂ) * Complex.I))))) =
            -(∑ g ∈ SZ, ((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
              ∫ u in Set.Ioi (0 : ℝ),
                Complex.exp (-((e : ℂ) * (u : ℂ)) + (g : ℂ) * (u : ℂ) * Complex.I) *
                  (fejerK T (x - u) : ℂ)) := by
          rw [mul_neg, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [intervalIntegral.integral_const_mul, ← mul_assoc,
            mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)), mul_assoc, hpole_eval g hg]
        rw [mul_add, mul_sub, mul_add, hpoles_simp]
      rw [hdecomp] at hLHS_re_nonneg
      simp only [Complex.add_re, Complex.sub_re, Complex.neg_re] at hLHS_re_nonneg
      have hfin_re : -(((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))).re ≤
          C_fin / (x - u1) ^ 2 := by
        have h1 := (abs_le.mp (Complex.abs_re_le_norm (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, wt t * (∫ u in Set.Ioc (0 : ℝ) u1, ((u * jExp u : ℝ) : ℂ) *
            Complex.exp (-((1 / 2 + (e : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))))))).1
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
            (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) +
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
              (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) +
                logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                  (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)) atTop
          (𝓝 (∫ t in Set.Ioc (-T) T, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (((1 - |t| / T : ℝ) : ℂ) * fBdry t))) := by
        refine tendsto_integral_of_dominated_convergence bound_t (fun n => ?_) hbound_int (fun n => ?_) ?_
        · have hmap : ContinuousOn (fun t : ℝ => (1 / 2 : ℂ) + (eps n : ℂ) + (t : ℂ) * Complex.I)
              (Set.Icc (-T) T) := by fun_prop
          have hc : ContinuousOn (fun t : ℝ =>
              ((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                (R1 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) +
                  logL4 (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) /
                    (1 / 2 + (eps n : ℂ) + (t : ℂ) * Complex.I) ^ 2)) (Set.Icc (-T) T) := by
            refine (Continuous.continuousOn (by fun_prop)).mul
              ((hR1_cont.comp hmap fun t ht => (hrect_mem n t ht).1).add
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
          refine (norm_add_le _ _).trans (add_le_add
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
          have htot := (hR1_tend.add (hlogL4_tend.div (hz_tend.pow 2) hden_ne)).const_mul
            (((1 - |t| / T : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
          refine htot.trans ?_
          dsimp [fBdry]; ring_nf; exact le_rfl
      simp_rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact (Complex.continuous_re.tendsto _).comp (ht_int.const_mul _)
    -- Apply ge_of_tendsto to pass to the limit n → ∞!
    have htend_rhs := ((htend_poles.neg.add htend_smooth).add_const (C_fin / (x - u1) ^ 2)).add_const
      ((11 / 10 : ℝ) * (2 * fejerConst / Real.pi))
    exact ge_of_tendsto htend_rhs (Filter.Eventually.of_forall hnonneg_n)
  -- Step 6e: Take x = k + 1/T → ∞!
  -- Split ∫_{Iio x} = ∫_ℝ - ∫_{Ici x}, apply integral_exp_mul_fejerK and Riemann-Lebesgue!
  have hRL_tend : Tendsto (fun k : ℕ =>
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (((k : ℝ) + 1 / T : ℝ) : ℂ) * Complex.I) *
          (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re) atTop (𝓝 0) := by
    have h1 := (tendsto_integral_exp_Icc hTpos (fun t => ((1 - |t| / T : ℝ) : ℂ) * fBdry t)).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := 1 / T)))
    have h2 := (Complex.continuous_re.tendsto ((((1 / (2 * Real.pi) : ℝ) : ℂ) * 0))).comp
      (h1.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ)))
    simpa only [Function.comp_def, mul_zero, Complex.zero_re] using h2
  have hfin_tend : Tendsto (fun k : ℕ => C_fin / (((k : ℝ) + 1 / T) - u1) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (((k : ℝ) + 1 / T) - u1) ^ 2) atTop atTop := by
      have hlin : Tendsto (fun k : ℕ => ((k : ℝ) + 1 / T) - u1) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_add tendsto_const_nhds
      exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hlin
    exact tendsto_const_nhds.div_atTop h1
  have htail_tend : Tendsto (fun k : ℕ =>
      (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
        Complex.exp ((g : ℂ) * (((k : ℝ) + 1 / T : ℝ) : ℂ) * Complex.I) *
        ∫ v in Set.Ici ((k : ℝ) + 1 / T),
          Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re) atTop (𝓝 0) := by
    have hsum0 : (0 : ℝ) = ∑ _g ∈ SZ, (0 : ℝ) := by simp
    rw [hsum0]
    simp_rw [Complex.re_sum]
    refine tendsto_finsetSum SZ fun g _ => ?_
    have hnorm0 : Tendsto (fun k : ℕ =>
        ‖((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
          Complex.exp ((g : ℂ) * (((k : ℝ) + 1 / T : ℝ) : ℂ) * Complex.I) *
          ∫ v in Set.Ici ((k : ℝ) + 1 / T),
            Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ)‖) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun k : ℕ =>
          ‖(mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)‖ * (2 / (Real.pi * T * ((k : ℝ) + 1 / T)))) ?_ ?_
      · refine Filter.eventually_atTop.mpr ⟨1, fun k hk => ?_⟩
        set x : ℝ := (k : ℝ) + 1 / T
        have hxpos : 0 < x := by dsimp [x]; positivity
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
      · have hlin : Tendsto (fun k : ℕ => Real.pi * T * ((k : ℝ) + 1 / T)) atTop atTop :=
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by positivity)
        simpa using (tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop hlin).const_mul
          ‖(mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)‖
    exact squeeze_zero_norm (fun k => Complex.abs_re_le_norm _) hnorm0
  -- Combine all error terms tending to 0!
  let errK : ℕ → ℝ := fun k =>
    (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
      Complex.exp ((g : ℂ) * (((k : ℝ) + 1 / T : ℝ) : ℂ) * Complex.I) *
      ∫ v in Set.Ici ((k : ℝ) + 1 / T),
        Complex.exp (-((g : ℂ) * (v : ℂ) * Complex.I)) * (fejerK T v : ℂ))).re +
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in (-T)..T, Complex.exp ((t : ℂ) * (((k : ℝ) + 1 / T : ℝ) : ℂ) * Complex.I) *
        (((1 - |t| / T : ℝ) : ℂ) * fBdry t)).re +
    C_fin / (((k : ℝ) + 1 / T) - u1) ^ 2
  have herr_tend : Tendsto errK atTop (𝓝 0) := by
    simpa [errK] using (htail_tend.add hRL_tend).add hfin_tend
  have hC4_pos : 0 < 4 * fejerConst / Real.pi := by
    have := fejerConst_pos; positivity
  have herr_small : ∀ᶠ k : ℕ in atTop, errK k ≤ 4 * fejerConst / Real.pi := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp herr_tend) (4 * fejerConst / Real.pi) hC4_pos
    refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
    have h1 := hN k hk
    rw [Real.dist_eq, sub_zero] at h1
    linarith [(abs_lt.mp h1).2]
  have hk_big : ∀ᶠ k : ℕ in atTop, u1 + 1 < (k : ℝ) + 1 / T := by
    refine Filter.eventually_atTop.mpr ⟨⌈u1 + 2⌉₊, fun k hk => ?_⟩
    have h1 : u1 + 2 ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
    linarith [show (0 : ℝ) < 1 / T by positivity]
  filter_upwards [herr_small, hk_big] with k hk_err hk_x
  set x : ℝ := (k : ℝ) + 1 / T
  have hineq := hmain_x x hk_x
  -- Rewrite ∫_{Iio x} = ∫_ℝ - ∫_{Ici x} for each g ∈ SZ
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
  -- Pair +g and -g in SZ = Z ∪ Z.image Neg.neg
  have hpair_sum : (∑ g ∈ SZ, (((mult g : ℂ) / (1 / 2 + (g : ℂ) * Complex.I)) *
      Complex.exp ((g : ℂ) * (x : ℂ) * Complex.I) *
      (((2 * fejerConst / Real.pi) * (1 - |g| / T) : ℝ) : ℂ))).re =
      (4 * fejerConst / Real.pi) *
        ∑ g ∈ Z, let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g / T) : ℂ)
          ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
            ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2)) := by
    dsimp only [SZ]
    rw [Complex.re_sum, Finset.sum_union hZ_disj, Finset.sum_image (fun a _ b _ h => neg_injective h),
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg0 : 0 < g := ((hZ g).mp hg).1
    have hv_eq : (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g / T) : ℂ) =
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
  -- Rearrange: (4*fejerConst/π) * S ≤ (11/10)*(2*fejerConst/π) + errK k ≤ (4*fejerConst/π) * 2
  have hS_le : (4 * fejerConst / Real.pi) *
      (∑ g ∈ Z, let v := (((Circle.exp g : Circle) ^ k : Circle) : ℂ) * (Circle.exp (g / T) : ℂ)
        ((analyticOrderAt L4 (1 / 2 + (g : ℂ) * Complex.I)).toNat : ℝ) *
          ((1 - g / T) * (v.re / 2 + g * v.im) / (1 / 4 + g ^ 2))) ≤
      (4 * fejerConst / Real.pi) * 2 := by
    have h11 : (11 / 10 : ℝ) * (2 * fejerConst / Real.pi) ≤ (4 * fejerConst / Real.pi) := by
      have := fejerConst_pos
      have := Real.pi_pos
      have hle : (22 / 10 : ℝ) * (fejerConst / Real.pi) ≤ 4 * (fejerConst / Real.pi) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      have he1 : (11 / 10 : ℝ) * (2 * fejerConst / Real.pi) = (22 / 10 : ℝ) * (fejerConst / Real.pi) := by ring
      have he2 : 4 * fejerConst / Real.pi = 4 * (fejerConst / Real.pi) := by ring
      linarith
    dsimp [errK] at hk_err
    linarith
  exact le_of_mul_le_mul_left hS_le hC4_pos

end ChebyshevBiasH3Proof

theorem OMA.solution : OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1.H3 := by
  intro hJ hRH T Z hT hZ
  exact ChebyshevBiasH3Proof.fejer_explicit_formula hJ hRH T Z hT hZ

