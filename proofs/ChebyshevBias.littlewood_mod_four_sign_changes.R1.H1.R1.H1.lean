import OMAReductions.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1
import Mathlib

/-!
Landau one-sided singularity argument for the Dirichlet L-function of the nontrivial real
character modulo 4.
-/

open Filter Finset Real Complex MeasureTheory Topology
open scoped Nat

namespace ChebyshevBiasH1Proof

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

/- ### Step 1: Nonvanishing of L4 on the positive real axis -/

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
  have hball_sub : Metric.ball s₀ δ ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
    have h2 : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
    change 0 < s.re
    linarith
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

private lemma L4_real_ne_zero {σ : ℝ} (hσ : 0 < σ) : L4 (σ : ℂ) ≠ 0 := by
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
  rw [ne_eq, Complex.ofReal_eq_zero]
  have hsum : Summable (fun k : ℕ => ((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ)) := by
    have hC : Summable (fun k : ℕ => altTerm k (σ : ℂ)) :=
      Summable.of_norm_bounded
        (g := fun k : ℕ => 2 * ‖(σ : ℂ)‖ * ((4 * k + 1 : ℕ) : ℝ) ^ (-(σ + 1)))
        ((summable_altTerm_bound hσ).mul_left _)
        (fun k => by simpa using norm_altTerm_le k (s := (σ : ℂ)) (by simpa using hσ))
    have hre := Complex.reCLM.summable hC
    refine hre.congr fun k => ?_
    simp [hterm k]
  have hpos : 0 < ∑' k : ℕ, (((4 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((4 * k + 3 : ℕ) : ℝ) ^ (-σ)) := by
    refine hsum.tsum_pos (fun k => ?_) 0 ?_
    · have hlt : ((4 * k + 3 : ℕ) : ℝ) ^ (-σ) < ((4 * k + 1 : ℕ) : ℝ) ^ (-σ) :=
        Real.rpow_lt_rpow_of_neg (by positivity) (by norm_cast; omega) (by linarith)
      linarith
    · have hlt : ((4 * 0 + 3 : ℕ) : ℝ) ^ (-σ) < ((4 * 0 + 1 : ℕ) : ℝ) ^ (-σ) :=
        Real.rpow_lt_rpow_of_neg (by positivity) (by norm_cast) (by linarith)
      linarith
  exact hpos.ne'

/- ### Step 2: Partial sum identity and integral representation of log L4 -/

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
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      split_ifs <;> norm_num
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
    ext n
    rw [χ4_apply_nat]
    simp [aCoeff]
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
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact abs_aCoeff_le_one k
      _ = (n : ℝ) := by simp
  rw [LSeries_eq_mul_integral' (fun n => (aCoeff n : ℂ)) zero_le_one hs hO]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← Complex.ofReal_sum, JVal_eq_sum_aCoeff]

/- ### Step 3: Splitting the integral at N and the non-negative function H -/

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

/- ### Step 4: Holomorphic antiderivative and logarithm on an open disk -/

/-- Term-by-term antiderivative power series centered at c with value v0 at c. -/
noncomputable def antiderivBall (f : ℂ → ℂ) (c v0 z : ℂ) : ℂ :=
  v0 + ∑' n : ℕ, (((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f c * (z - c) ^ (n + 1)

private lemma antiderivBall_self (f : ℂ → ℂ) (c v0 : ℂ) :
    antiderivBall f c v0 c = v0 := by
  simp [antiderivBall]

private lemma antiderivBall_hasDerivAt {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (v0 : ℂ)
    {z : ℂ} (hz : z ∈ Metric.ball c R) :
    HasDerivAt (antiderivBall f c v0) (f z) z := by
  have hdist : ‖z - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  obtain ⟨r1, hzr1, hr1R⟩ := exists_between hdist
  obtain ⟨r2, hr1r2, hr2R⟩ := exists_between hr1R
  have hr1pos : 0 < r1 := lt_of_le_of_lt (norm_nonneg _) hzr1
  have hr2pos : 0 < r2 := hr1pos.trans hr1r2
  have hz2 : c + (r2 : ℂ) ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr2pos.le]
    exact hr2R
  have hsum2 : Summable (fun n : ℕ => (n ! : ℂ)⁻¹ * iteratedDeriv n f c * (r2 : ℂ) ^ n) := by
    have h := (Complex.hasSum_taylorSeries_on_ball hf hz2).summable
    refine h.congr fun n => ?_
    simp [smul_eq_mul]
    ring
  have htend0 : Tendsto (fun n : ℕ => ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (r2 : ℂ) ^ n‖)
      atTop (𝓝 0) := by
    have h := (Nat.cofinite_eq_atTop ▸ hsum2.tendsto_cofinite_zero).norm
    simpa only [norm_zero] using h
  have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ * r2 ^ n ≤ M := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend0) 1 zero_lt_one
    let b : ℕ → ℝ := fun n => ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ * r2 ^ n
    have hne_rng : (Finset.range (N + 1)).Nonempty :=
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
    refine ⟨max 1 ((Finset.range (N + 1)).sup' hne_rng b),
      le_trans zero_le_one (le_max_left _ _), fun n => ?_⟩
    by_cases hn : n < N + 1
    · exact le_trans (Finset.le_sup' b (Finset.mem_range.mpr hn)) (le_max_right _ _)
    · have h1 := hN n (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
      have h2 : ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ * r2 ^ n =
          ‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c * (r2 : ℂ) ^ n‖ := by
        symm
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr2pos.le]
      rw [h2]
      exact le_trans h1.le (le_max_left _ _)
  obtain ⟨M, hM0, hM⟩ := hbdd
  let F : ℕ → ℂ → ℂ := fun n w =>
    (((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f c * (w - c) ^ (n + 1)
  have hu_sum : Summable (fun n : ℕ => M * r1 * (r1 / r2) ^ n) :=
    (summable_geometric_of_lt_one (div_nonneg hr1pos.le hr2pos.le)
      ((div_lt_one hr2pos).mpr hr1r2)).mul_left _
  have hF_le : ∀ n : ℕ, ∀ w ∈ Metric.ball c r1,
      ‖F n w‖ ≤ M * r1 * (r1 / r2) ^ n := by
    intro n w hw
    have hw1 : ‖w - c‖ ≤ r1 := by
      have : ‖w - c‖ < r1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      exact this.le
    dsimp [F]
    rw [norm_mul, norm_mul, norm_pow]
    have hfac : ‖(((n + 1)! : ℕ) : ℂ)⁻¹‖ ≤ ‖(n ! : ℂ)⁻¹‖ := by
      rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      exact inv_anti₀ (by exact_mod_cast Nat.factorial_pos n)
        (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
    have hpow : ‖w - c‖ ^ (n + 1) ≤ r1 * r1 ^ n := by
      rw [pow_succ']
      exact mul_le_mul hw1 (pow_le_pow_left₀ (norm_nonneg _) hw1 n) (by positivity) hr1pos.le
    calc
      ‖(((n + 1)! : ℕ) : ℂ)⁻¹‖ * ‖iteratedDeriv n f c‖ * ‖w - c‖ ^ (n + 1)
          ≤ ‖(n ! : ℂ)⁻¹‖ * ‖iteratedDeriv n f c‖ * (r1 * r1 ^ n) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)) hpow
              (by positivity) (by positivity)
      _ = (‖(n ! : ℂ)⁻¹ * iteratedDeriv n f c‖ * r2 ^ n) * r1 * (r1 / r2) ^ n := by
            rw [norm_mul, div_pow]
            field_simp [hr2pos.ne']
      _ ≤ M * r1 * (r1 / r2) ^ n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hM n) hr1pos.le) (by positivity)
  have hF_diff : ∀ n : ℕ, DifferentiableOn ℂ (F n) (Metric.ball c r1) := fun n =>
    ((differentiable_const _).mul ((differentiable_id.sub_const c).pow (n + 1))).differentiableOn
  have hz_ball1 : z ∈ Metric.ball c r1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzr1
  have hdiff_sum : DifferentiableOn ℂ (fun w => ∑' n : ℕ, F n w) (Metric.ball c r1) :=
    differentiableOn_tsum_of_summable_norm hu_sum hF_diff Metric.isOpen_ball hF_le
  have hderiv_sum := hasSum_deriv_of_summable_norm hu_sum hF_diff Metric.isOpen_ball hF_le hz_ball1
  have hterm_deriv : ∀ n : ℕ, deriv (F n) z =
      (n ! : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c := by
    intro n
    have hd : HasDerivAt (F n)
        ((((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f c * (((n + 1 : ℕ) : ℂ) * (z - c) ^ n)) z := by
      have h1 := ((hasDerivAt_id z).sub_const c).pow (n + 1)
      simpa [F, mul_one] using h1.const_mul ((((n + 1)! : ℕ) : ℂ)⁻¹ * iteratedDeriv n f c)
    rw [hd.deriv]
    have hfac : (((n + 1)! : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) * (n ! : ℂ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hnf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [hfac, smul_eq_mul, smul_eq_mul]
    field_simp [hn1, hnf]
  simp_rw [hterm_deriv] at hderiv_sum
  have hval : deriv (fun w => ∑' n : ℕ, F n w) z = f z :=
    hderiv_sum.unique (Complex.hasSum_taylorSeries_on_ball hf hz)
  have hda : HasDerivAt (fun w => ∑' n : ℕ, F n w) (f z) z := by
    rw [← hval]
    exact (hdiff_sum.differentiableAt (Metric.isOpen_ball.mem_nhds hz_ball1)).hasDerivAt
  exact hda.const_add v0

private lemma exists_holomorphic_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hne : ∀ z ∈ Metric.ball c R, f z ≠ 0)
    (v0 : ℂ) (hv0 : Complex.exp v0 = f c) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball c R) ∧
      F c = v0 ∧ ∀ z ∈ Metric.ball c R, Complex.exp (F z) = f z := by
  have hlogderiv : DifferentiableOn ℂ (fun z => deriv f z / f z) (Metric.ball c R) := by
    intro z hz
    have hdf : DifferentiableOn ℂ (deriv f) (Metric.ball c R) := hf.deriv Metric.isOpen_ball
    exact ((hdf z hz).div (hf z hz) (hne z hz))
  let F := antiderivBall (fun z => deriv f z / f z) c v0
  have hF_deriv : ∀ z ∈ Metric.ball c R, HasDerivAt F (deriv f z / f z) z :=
    fun z hz => antiderivBall_hasDerivAt hlogderiv v0 hz
  have hF_diff : DifferentiableOn ℂ F (Metric.ball c R) :=
    fun z hz => (hF_deriv z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ Metric.ball c R, f z * Complex.exp (-F z) = 1 := by
    have hQderiv : ∀ z ∈ Metric.ball c R,
        HasDerivAt (fun w => f w * Complex.exp (-F w)) 0 z := by
      intro z hz
      have hf' : HasDerivAt f (deriv f z) z :=
        (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
      have hE' : HasDerivAt (fun w => Complex.exp (-F w))
          (Complex.exp (-F z) * -(deriv f z / f z)) z :=
        ((hF_deriv z hz).neg).cexp
      have hmul := hf'.mul hE'
      have hzero : deriv f z * Complex.exp (-F z) +
          f z * (Complex.exp (-F z) * -(deriv f z / f z)) = 0 := by
        have hfz := hne z hz
        field_simp [hfz]
        ring
      rwa [hzero] at hmul
    intro z hz
    have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
    have hQeq : f z * Complex.exp (-F z) = f c * Complex.exp (-F c) :=
      (convex_ball c R).is_const_of_fderivWithin_eq_zero
        (f := fun w => f w * Complex.exp (-F w))
        (fun w hw => (hQderiv w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => by
          rw [fderivWithin_of_isOpen Metric.isOpen_ball hw, (hQderiv w hw).hasFDerivAt.fderiv]
          simp)
        hz hc
    rw [hQeq]
    simp [F, antiderivBall_self, ← hv0, ← Complex.exp_add]
  refine ⟨F, hF_diff, antiderivBall_self _ _ _, fun z hz => ?_⟩
  have h1 := hconst z hz
  calc
    Complex.exp (F z) = 1 * Complex.exp (F z) := (one_mul _).symm
    _ = (f z * Complex.exp (-F z)) * Complex.exp (F z) := by rw [h1]
    _ = f z * (Complex.exp (-F z) * Complex.exp (F z)) := by ring
    _ = f z := by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/- ### Step 5: Iterated derivatives of the Laplace-Mellin integral and Tonelli -/

/-- Non-negative regularized integral kernel H(t) = J(⌊t⌋) + √t. -/
noncomputable def Hfun (t : ℝ) : ℝ := JVal ⌊t⌋₊ + Real.sqrt t

private lemma measurable_Hfun : Measurable Hfun :=
  ((measurable_of_countable JVal).comp Nat.measurable_floor).add Real.continuous_sqrt.measurable

private lemma Hfun_le_two_mul {t : ℝ} (ht : 1 ≤ t) : |Hfun t| ≤ 2 * t := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hsqrt : Real.sqrt t ≤ t := by
    have : Real.sqrt t ≤ Real.sqrt (t * t) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_mul_self ht0] at this
  calc
    |Hfun t| ≤ |JVal ⌊t⌋₊| + |Real.sqrt t| := abs_add_le _ _
    _ ≤ (⌊t⌋₊ : ℝ) + Real.sqrt t := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      gcongr
      exact abs_JVal_le _
    _ ≤ t + t := add_le_add (Nat.floor_le ht0) hsqrt
    _ = 2 * t := by ring

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
    have hdom : IntegrableOn (fun t : ℝ => 2 * t ^ (-1 - (σ - 1) / 2)) (Set.Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hTpos).const_mul 2
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
          ≤ (2 * t) * t ^ ((σ - 1) / 2) * t ^ (-(σ + 1)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul (Hfun_le_two_mul ht1.le) hb (pow_nonneg hlog0 k) (by positivity))
              (Real.rpow_nonneg htpos.le _)
      _ = 2 * (t * t ^ ((σ - 1) / 2) * t ^ (-(σ + 1))) := by ring
      _ = 2 * t ^ (-1 - (σ - 1) / 2) := by
            congr 1
            nth_rw 1 [← Real.rpow_one t]
            rw [← Real.rpow_add htpos, ← Real.rpow_add htpos]
            congr 1; ring
  have hint_init : IntegrableOn (fun t : ℝ => |Hfun t| * (Real.log t) ^ k * t ^ (-(σ + 1)))
      (Set.Ioc (N : ℝ) T) := by
    refine (integrableOn_const (C := 2 * T * (Real.log T) ^ k)
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
          ≤ (2 * t) * (Real.log T) ^ k * 1 := by
            refine mul_le_mul
              (mul_le_mul (Hfun_le_two_mul ht1.le) (pow_le_pow_left₀ hlog0 hlogle k)
                (pow_nonneg hlog0 k) (by positivity))
              hpow1 (Real.rpow_nonneg htpos.le _) (mul_nonneg (by positivity) (pow_nonneg hlogT0 k))
      _ ≤ 2 * T * (Real.log T) ^ k := by
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

/- ### Step 6: Main Landau contradiction argument -/

set_option maxHeartbeats 600000 in
private theorem landau_zero_free
    (hJ : ∀ᶠ n : ℕ in atTop, -(Real.sqrt n / Real.log n) ≤ JVal n) :
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
    have hJge := hN₀ ⌊t⌋₊ hfl_N0
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
  -- Key identity on Re(s) > 1: L4 s = exp (s * g0 s + P s - s * N^(1/2 - s) / (s - 1/2))
  let Ψ : ℂ → ℂ := fun s =>
    s * gDeriv N 0 s + P s - s * ((N : ℂ) ^ ((1 / 2 : ℂ) - s) / (s - 1 / 2))
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
        gDeriv N 0 s - (N : ℂ) ^ ((1 / 2 : ℂ) - s) / (s - 1 / 2) := by
      rw [← integral_Ioi_sqrt_cpow hNpos (by linarith)]
      have hg0 : gDeriv N 0 s = ∫ t in Set.Ioi (N : ℝ), (Hfun t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        simp [gDeriv]
      rw [hg0, ← integral_sub hH_int hsqrt_int]
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
  let gTilde : ℂ → ℂ := fun z => (F z - P z) / z + (N : ℂ) ^ ((1 / 2 : ℂ) - z) / (z - 1 / 2)
  have hgTilde_diff : DifferentiableOn ℂ gTilde (Metric.ball (2 : ℂ) R) := by
    intro z hz
    have hzre : 1 / 2 < z.re := hball_re z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hzre; linarith
    have hzhalf : z - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [sub_re, div_ofNat_re, one_re, zero_re] at this
      linarith
    have hNz : 0 < (N : ℂ).re := by simp; positivity
    have h1 : DifferentiableWithinAt ℂ (fun w => (F w - P w) / w) (Metric.ball 2 R) z :=
      ((hF_diff z hz).sub (hP_diff z).differentiableWithinAt).div differentiableWithinAt_id hz0
    have h2 : DifferentiableWithinAt ℂ (fun w => (N : ℂ) ^ ((1 / 2 : ℂ) - w) / (w - 1 / 2))
        (Metric.ball 2 R) z := by
      have hc : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - w)) z :=
        (differentiableAt_const _).cpow ((differentiableAt_const _).sub differentiableAt_id) (Or.inl hNz)
      exact (hc.div (differentiableAt_id.sub_const _) hzhalf).differentiableWithinAt
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
    exact (((differentiableAt_id.mul hg0).add (hP_diff z)).sub
      (differentiableAt_id.mul hcp)).differentiableWithinAt
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
    exact ((differentiableWithinAt_id.mul (hg0_diff s hs)).add
      (hP_diff s).differentiableWithinAt).sub
      (differentiableWithinAt_id.mul hcp.differentiableWithinAt)
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

end ChebyshevBiasH1Proof

theorem OMA.solution : OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1.H1 := by
  intro hJ s hs
  exact ChebyshevBiasH1Proof.landau_zero_free hJ s hs
