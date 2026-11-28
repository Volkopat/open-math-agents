import FormalConjectures.ErdosProblems.«967»

/-! Proof of Erdos967.erdos_967.variants.tauberian (Erdos-Ingham 1964 Tauberian equivalence). -/

open Filter MeasureTheory Real
open scoped Topology FourierTransform

namespace OMA.Erdos967


private lemma a_ge_add_two {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0) (k : ℕ) :
    k + 2 ≤ a k := by
  induction k with
  | zero => exact ha₀
  | succ k ih =>
      have hlt : a k < a (k + 1) := ha (Nat.lt_succ_self k)
      omega

private lemma a_pos {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0) (k : ℕ) : 0 < a k := by
  have := a_ge_add_two ha ha₀ k
  omega

private lemma a_gt_one {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0) (k : ℕ) : 1 < a k := by
  have := a_ge_add_two ha ha₀ k
  omega

private lemma log_a_pos {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0) (k : ℕ) :
    0 < Real.log (a k : ℝ) :=
  Real.log_pos (by exact_mod_cast a_gt_one ha ha₀ k)

private lemma tendsto_a_atTop {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0) :
    Tendsto (fun k : ℕ => (a k : ℝ)) atTop atTop :=
  tendsto_atTop_mono
    (fun k => by have := a_ge_add_two ha ha₀ k; exact_mod_cast (by omega : k ≤ a k))
    tendsto_natCast_atTop_atTop

private lemma summand_eq (t : ℝ) {n : ℕ} (hn : 0 < n) :
    Erdos967.summand t n =
      ((1 / (n : ℝ) : ℝ) : ℂ) * Complex.exp ((-(t * Real.log (n : ℝ)) : ℝ) * Complex.I) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnc_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  dsimp [Erdos967.summand]
  rw [Complex.cpow_def_of_ne_zero hnc_ne, one_div, ← Complex.exp_neg]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  rw [hlog]
  have hexp_eq : -((Real.log (n : ℝ) : ℂ) * (1 + (t : ℂ) * Complex.I)) =
      ((-Real.log (n : ℝ) : ℝ) : ℂ) + ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp_eq, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn_pos, one_div]

private lemma norm_summand (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Erdos967.summand t n‖ = 1 / (n : ℝ) := by
  rw [summand_eq t hn, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_of_nonneg (by positivity)]

private lemma summable_summand {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) (t : ℝ) :
    Summable (fun k : ℕ => Erdos967.summand t (a k)) := by
  refine Summable.of_norm ?_
  have heq : (fun k : ℕ => ‖Erdos967.summand t (a k)‖) = fun k => 1 / (a k : ℝ) := by
    ext k; exact norm_summand t (a_pos ha ha₀ k)
  rw [heq]
  exact hsum

private noncomputable def mprWitness (t₀ x : ℝ) : ℝ :=
  let ε := 1 / (2 * (1 + |t₀|))
  if x < 1 then 0 else x * (1 + ε * Real.cos (t₀ * Real.log x))

private lemma mprWitness_zero {t₀ x : ℝ} (hx : x < 1) : mprWitness t₀ x = 0 := by
  simp [mprWitness, hx]

private lemma mprWitness_nonneg (t₀ x : ℝ) : 0 ≤ mprWitness t₀ x := by
  let ε : ℝ := 1 / (2 * (1 + |t₀|))
  have hε_pos : 0 < ε := by positivity
  have hε_le_half : ε ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ 1 + |t₀| := by linarith [abs_nonneg t₀]
    dsimp [ε]
    calc 1 / (2 * (1 + |t₀|)) ≤ 1 / (2 * 1) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num
  by_cases hx : x < 1
  · simp [mprWitness, hx]
  · have hx1 : 1 ≤ x := not_lt.mp hx
    have hcos : -1 ≤ Real.cos (t₀ * Real.log x) := Real.neg_one_le_cos _
    have hfac : 0 ≤ 1 + ε * Real.cos (t₀ * Real.log x) := by nlinarith
    dsimp [mprWitness]
    rw [if_neg hx]
    exact mul_nonneg (by linarith) hfac

private lemma mprWitness_mono (t₀ : ℝ) : Monotone (mprWitness t₀) := by
  let ε : ℝ := 1 / (2 * (1 + |t₀|))
  have hε_pos : 0 < ε := by positivity
  have hε_mul : ε * (1 + |t₀|) = 1 / 2 := by dsimp [ε]; field_simp
  let g : ℝ → ℝ := fun x => x * (1 + ε * Real.cos (t₀ * Real.log x))
  have hg_mono : MonotoneOn g (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
    · refine continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul ?_))
      refine Real.continuous_cos.comp_continuousOn ?_
      refine continuousOn_const.mul (Real.continuousOn_log.mono ?_)
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    · refine DifferentiableOn.mul differentiableOn_id (differentiableOn_const _ |>.add ?_)
      refine DifferentiableOn.const_mul ?_ ε
      refine DifferentiableOn.cos ?_
      refine DifferentiableOn.const_mul (Real.differentiableOn_log.mono ?_) t₀
      intro x hx
      rw [interior_Ici] at hx
      exact ne_of_gt (lt_trans zero_lt_one hx)
    · intro x hx
      rw [interior_Ici] at hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hlog : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx_pos.ne'
      have hcos : HasDerivAt (fun y : ℝ => 1 + ε * Real.cos (t₀ * Real.log y))
          (0 + ε * (-Real.sin (t₀ * Real.log x) * (t₀ * x⁻¹))) x :=
        (hasDerivAt_const x 1).add (((hlog.const_mul t₀).cos).const_mul ε)
      have hg_deriv : HasDerivAt g
          (1 * (1 + ε * Real.cos (t₀ * Real.log x)) +
            x * (0 + ε * (-Real.sin (t₀ * Real.log x) * (t₀ * x⁻¹)))) x :=
        (hasDerivAt_id x).mul hcos
      rw [hg_deriv.deriv]
      have hsimp : 1 * (1 + ε * Real.cos (t₀ * Real.log x)) +
            x * (0 + ε * (-Real.sin (t₀ * Real.log x) * (t₀ * x⁻¹))) =
          1 + ε * Real.cos (t₀ * Real.log x) - ε * t₀ * Real.sin (t₀ * Real.log x) := by
        field_simp [hx_pos.ne']; ring
      rw [hsimp]
      have h1 : |ε * Real.cos (t₀ * Real.log x)| ≤ ε := by
        rw [abs_mul, abs_of_pos hε_pos]
        exact mul_le_of_le_one_right hε_pos.le (Real.abs_cos_le_one _)
      have h2 : |ε * t₀ * Real.sin (t₀ * Real.log x)| ≤ ε * |t₀| := by
        rw [abs_mul, abs_mul, abs_of_pos hε_pos]
        exact mul_le_of_le_one_right (mul_nonneg hε_pos.le (abs_nonneg t₀)) (Real.abs_sin_le_one _)
      have h3 : |ε * Real.cos (t₀ * Real.log x) - ε * t₀ * Real.sin (t₀ * Real.log x)| ≤ 1 / 2 := by
        calc |ε * Real.cos (t₀ * Real.log x) - ε * t₀ * Real.sin (t₀ * Real.log x)|
            ≤ |ε * Real.cos (t₀ * Real.log x)| + |ε * t₀ * Real.sin (t₀ * Real.log x)| :=
              abs_sub _ _
          _ ≤ ε + ε * |t₀| := add_le_add h1 h2
          _ = ε * (1 + |t₀|) := by ring
          _ = 1 / 2 := hε_mul
      linarith [(abs_le.mp h3).1]
  intro x y hxy
  by_cases hx : x < 1
  · rw [mprWitness_zero hx]; exact mprWitness_nonneg t₀ y
  · have hx1 : 1 ≤ x := not_lt.mp hx
    have hy1 : 1 ≤ y := hx1.trans hxy
    have hfx : mprWitness t₀ x = g x := by dsimp [mprWitness, g]; rw [if_neg hx]
    have hfy : mprWitness t₀ y = g y := by dsimp [mprWitness, g]; rw [if_neg (not_lt.mpr hy1)]
    rw [hfx, hfy]
    exact hg_mono hx1 hy1 hxy

private lemma mpr_tail_tendsto {a : ℕ → ℕ} (ha : StrictMono a)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    Tendsto (fun x : ℝ => ∑' k, if (a k : ℝ) ≤ x then 0 else (1 / (a k : ℝ))) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK_tend : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, 1 / (a k : ℝ)) atTop
      (𝓝 (∑' k, 1 / (a k : ℝ))) := hsum.hasSum.tendsto_sum_nat
  obtain ⟨K, hK⟩ := (Metric.tendsto_nhds.mp hK_tend η hη).exists
  refine eventually_atTop.mpr ⟨(a K : ℝ), fun x hx => ?_⟩
  have hsum_tail_dom : Summable (fun k => if (a k : ℝ) ≤ x then 0 else (1 / (a k : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) ?_ hsum
    intro k; split_ifs; positivity; exact le_rfl
  have htail_nn : 0 ≤ ∑' k, if (a k : ℝ) ≤ x then 0 else (1 / (a k : ℝ)) :=
    tsum_nonneg fun k => by split_ifs <;> positivity
  have hsplit := (hsum_tail_dom.sum_add_tsum_nat_add K).symm
  have hzero_head : (∑ k ∈ Finset.range K, if (a k : ℝ) ≤ x then 0 else (1 / (a k : ℝ))) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hlt : k < K := Finset.mem_range.mp hk
    have hak_le : (a k : ℝ) ≤ x :=
      (show (a k : ℝ) ≤ a K by exact_mod_cast (ha hlt).le).trans hx
    rw [if_pos hak_le]
  have htail_le : (∑' k, if (a (k + K) : ℝ) ≤ x then 0 else (1 / (a (k + K) : ℝ))) ≤
      ∑' k, 1 / (a (k + K) : ℝ) := by
    have hdom_shift : Summable (fun k => 1 / (a (k + K) : ℝ)) :=
      (summable_nat_add_iff K).mpr hsum
    refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff K).mpr hsum_tail_dom) hdom_shift
    split_ifs; positivity; exact le_rfl
  have hsum_eq : ∑' k, 1 / (a (k + K) : ℝ) =
      (∑' k, 1 / (a k : ℝ)) - ∑ k ∈ Finset.range K, 1 / (a k : ℝ) := by
    linarith [hsum.sum_add_tsum_nat_add K]
  have hdist_K : ∑' k, 1 / (a k : ℝ) - ∑ k ∈ Finset.range K, 1 / (a k : ℝ) < η := by
    rw [Real.dist_eq, abs_sub_comm] at hK
    have hnn : 0 ≤ ∑' k, 1 / (a k : ℝ) - ∑ k ∈ Finset.range K, 1 / (a k : ℝ) := by
      rw [← hsum_eq]
      exact tsum_nonneg fun k => by positivity
    rwa [abs_of_nonneg hnn] at hK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg htail_nn]
  linarith [hsplit, hzero_head, htail_le, hsum_eq, hdist_K]

private lemma mprWitness_conv {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) {t₀ : ℝ}
    (ht₀_zero : 1 + ∑' k, Erdos967.summand t₀ (a k) = 0) :
    Tendsto (fun x : ℝ => (mprWitness t₀ x + ∑' k, mprWitness t₀ (x / (a k : ℝ))) / x) atTop
      (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) := by
  let ε : ℝ := 1 / (2 * (1 + |t₀|))
  have hε_pos : 0 < ε := by positivity
  have hs_summ : Summable (fun k => Erdos967.summand t₀ (a k)) := summable_summand ha ha₀ hsum t₀
  have htail := mpr_tail_tendsto ha hsum
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη' : 0 < η / (1 + ε) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), Metric.tendsto_nhds.mp htail (η / (1 + ε)) hη']
    with x hx1 htail_lt
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hf_summ : Summable (fun k => mprWitness t₀ (x / (a k : ℝ))) := by
    have hle : ∀ k, ‖mprWitness t₀ (x / (a k : ℝ))‖ ≤ x * (1 + ε) * (1 / (a k : ℝ)) := by
      intro k
      rw [Real.norm_of_nonneg (mprWitness_nonneg _ _)]
      by_cases hdiv : x / (a k : ℝ) < 1
      · rw [mprWitness_zero hdiv]; positivity
      · dsimp [mprWitness]; rw [if_neg hdiv]
        have hcos : 1 + ε * Real.cos (t₀ * Real.log (x / (a k : ℝ))) ≤ 1 + ε := by
          linarith [mul_le_of_le_one_right hε_pos.le (Real.cos_le_one (t₀ * Real.log (x / (a k : ℝ))))]
        calc (x / (a k : ℝ)) * (1 + ε * Real.cos (t₀ * Real.log (x / (a k : ℝ))))
            ≤ (x / (a k : ℝ)) * (1 + ε) :=
              mul_le_mul_of_nonneg_left hcos (by positivity)
          _ = x * (1 + ε) * (1 / (a k : ℝ)) := by ring
    exact Summable.of_norm_bounded (hsum.mul_left (x * (1 + ε))) hle
  have hfx_summ : Summable (fun k => mprWitness t₀ (x / (a k : ℝ)) / x) := hf_summ.div_const x
  let E : ℕ → ℝ := fun k =>
    ε * (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * Erdos967.summand t₀ (a k)).re
  have hE_summ : Summable E := by
    have hs1 : Summable (fun k => Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * Erdos967.summand t₀ (a k)) :=
      hs_summ.mul_left _
    exact (Complex.reCLM.summable hs1).mul_left ε
  have hE_sum_zero : ε * (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I)).re + ∑' k, E k = 0 := by
    have htsum_re : ∑' k, (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * Erdos967.summand t₀ (a k)).re =
        (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * ∑' k, Erdos967.summand t₀ (a k)).re := by
      have h1 : Summable (fun k => Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * Erdos967.summand t₀ (a k)) :=
        hs_summ.mul_left _
      rw [← Complex.re_tsum h1, tsum_mul_left]
    dsimp [E]
    rw [tsum_mul_left, htsum_re]
    have hzero_mul : Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * (1 + ∑' k, Erdos967.summand t₀ (a k)) = 0 := by
      rw [ht₀_zero, mul_zero]
    have hre := congrArg Complex.re hzero_mul
    rw [mul_add, mul_one, Complex.add_re, Complex.zero_re] at hre
    calc ε * (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I)).re +
          ε * (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * ∑' k, Erdos967.summand t₀ (a k)).re
        = ε * ((Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I)).re +
            (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * ∑' k, Erdos967.summand t₀ (a k)).re) := by ring
      _ = ε * 0 := by rw [hre]
      _ = 0 := mul_zero ε
  have hterm_eq : ∀ k, (a k : ℝ) ≤ x → mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ) = E k := by
    intro k hak
    have hak_pos : (0 : ℝ) < a k := by exact_mod_cast a_pos ha ha₀ k
    have hdiv_ge1 : 1 ≤ x / (a k : ℝ) := (one_le_div hak_pos).mpr hak
    have hnot : ¬ x / (a k : ℝ) < 1 := not_lt.mpr hdiv_ge1
    dsimp [mprWitness, E, ε]
    rw [if_neg hnot, summand_eq t₀ (a_pos ha ha₀ k)]
    have hre_exp : (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) *
        (((1 / (a k : ℝ) : ℝ) : ℂ) * Complex.exp ((-(t₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I))).re =
        (1 / (a k : ℝ)) * Real.cos (t₀ * Real.log (x / (a k : ℝ))) := by
      have hmul : Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) *
          (((1 / (a k : ℝ) : ℝ) : ℂ) * Complex.exp ((-(t₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I)) =
          ((1 / (a k : ℝ) : ℝ) : ℂ) * Complex.exp ((t₀ * Real.log (x / (a k : ℝ)) : ℝ) * Complex.I) := by
        rw [mul_left_comm, ← Complex.exp_add, Real.log_div hx_pos.ne' hak_pos.ne']
        congr 2; push_cast; ring
      rw [hmul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    rw [hre_exp]
    field_simp [hx_pos.ne', hak_pos.ne']
    ring
  have hfx_eq : mprWitness t₀ x / x - 1 = ε * (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I)).re := by
    dsimp [mprWitness, ε]
    rw [if_neg (not_lt.mpr hx1), Complex.exp_ofReal_mul_I_re]
    field_simp [hx_pos.ne']
    ring
  have hdiff_eq : (mprWitness t₀ x + ∑' k, mprWitness t₀ (x / (a k : ℝ))) / x - (1 + ∑' k, 1 / (a k : ℝ)) =
      ∑' k, (if (a k : ℝ) ≤ x then 0 else (- (1 / (a k : ℝ)) - E k)) := by
    have htsum_sub1 : (∑' k, mprWitness t₀ (x / (a k : ℝ)) / x) - ∑' k, 1 / (a k : ℝ) =
        ∑' k, (mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ)) := (hfx_summ.tsum_sub hsum).symm
    have htsum_sub2 : (∑' k, (mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ))) - ∑' k, E k =
        ∑' k, ((mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ)) - E k) :=
      ((hfx_summ.sub hsum).tsum_sub hE_summ).symm
    calc (mprWitness t₀ x + ∑' k, mprWitness t₀ (x / (a k : ℝ))) / x - (1 + ∑' k, 1 / (a k : ℝ))
        = (mprWitness t₀ x / x - 1) + ((∑' k, mprWitness t₀ (x / (a k : ℝ)) / x) - ∑' k, 1 / (a k : ℝ)) := by
            rw [add_div, ← tsum_div_const]; ring
      _ = (mprWitness t₀ x / x - 1) + ((∑' k, (mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ))) - ∑' k, E k) + ∑' k, E k := by
            rw [htsum_sub1]; ring
      _ = (ε * (Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I)).re + ∑' k, E k) +
            ∑' k, ((mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ)) - E k) := by
            rw [htsum_sub2, hfx_eq]; ring
      _ = ∑' k, ((mprWitness t₀ (x / (a k : ℝ)) / x - 1 / (a k : ℝ)) - E k) := by
            rw [hE_sum_zero, zero_add]
      _ = ∑' k, (if (a k : ℝ) ≤ x then 0 else (- (1 / (a k : ℝ)) - E k)) := by
            congr 1; ext k
            by_cases hak : (a k : ℝ) ≤ x
            · rw [if_pos hak, hterm_eq k hak, sub_self]
            · have hak_gt : x < (a k : ℝ) := not_le.mp hak
              have hak_pos : (0 : ℝ) < a k := by exact_mod_cast a_pos ha ha₀ k
              have hdiv_lt : x / (a k : ℝ) < 1 := (div_lt_one hak_pos).mpr hak_gt
              rw [if_neg hak, mprWitness_zero hdiv_lt, zero_div, zero_sub]
  have hE_abs : ∀ k, |E k| ≤ ε * (1 / (a k : ℝ)) := by
    intro k
    dsimp [E]
    rw [abs_mul, abs_of_pos hε_pos]
    refine mul_le_mul_of_nonneg_left ?_ hε_pos.le
    calc |(Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * Erdos967.summand t₀ (a k)).re|
        ≤ ‖Complex.exp ((t₀ * Real.log x : ℝ) * Complex.I) * Erdos967.summand t₀ (a k)‖ :=
          Complex.abs_re_le_norm _
      _ = 1 * (1 / (a k : ℝ)) := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, norm_summand t₀ (a_pos ha ha₀ k)]
      _ = 1 / (a k : ℝ) := one_mul _
  have hdom_tail : Summable (fun k => if (a k : ℝ) ≤ x then 0 else (1 + ε) * (1 / (a k : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_) (hsum.mul_left (1 + ε))
    split_ifs; positivity; exact le_rfl
  have hterm_summ : Summable (fun k => if (a k : ℝ) ≤ x then 0 else (- (1 / (a k : ℝ)) - E k)) := by
    refine Summable.of_norm_bounded hdom_tail fun k => ?_
    rw [Real.norm_eq_abs]
    by_cases hak : (a k : ℝ) ≤ x
    · simp [hak]
    · rw [if_neg hak, if_neg hak]
      calc |- (1 / (a k : ℝ)) - E k| ≤ |1 / (a k : ℝ)| + |E k| := by
            rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by simp [abs_neg])
        _ ≤ 1 / (a k : ℝ) + ε * (1 / (a k : ℝ)) := by
            rw [abs_of_nonneg (by positivity)]; gcongr; exact hE_abs k
        _ = (1 + ε) * (1 / (a k : ℝ)) := by ring
  rw [Real.dist_eq, hdiff_eq]
  calc |∑' k, (if (a k : ℝ) ≤ x then 0 else (- (1 / (a k : ℝ)) - E k))|
      ≤ ∑' k, |(if (a k : ℝ) ≤ x then 0 else (- (1 / (a k : ℝ)) - E k))| :=
        by simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hterm_summ.norm
    _ ≤ ∑' k, (if (a k : ℝ) ≤ x then 0 else (1 + ε) * (1 / (a k : ℝ))) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hterm_summ.abs hdom_tail
        by_cases hak : (a k : ℝ) ≤ x
        · simp [hak]
        · rw [if_neg hak, if_neg hak]
          calc |- (1 / (a k : ℝ)) - E k| ≤ |1 / (a k : ℝ)| + |E k| := by
                rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by simp [abs_neg])
            _ ≤ 1 / (a k : ℝ) + ε * (1 / (a k : ℝ)) := by
                rw [abs_of_nonneg (by positivity)]; gcongr; exact hE_abs k
            _ = (1 + ε) * (1 / (a k : ℝ)) := by ring
    _ = (1 + ε) * ∑' k, (if (a k : ℝ) ≤ x then 0 else (1 / (a k : ℝ))) := by
        rw [← tsum_mul_left]
        congr 1; ext k; split_ifs <;> ring
    _ < (1 + ε) * (η / (1 + ε)) := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => by split_ifs <;> positivity)] at htail_lt
        exact mul_lt_mul_of_pos_left htail_lt (by positivity)
    _ = η := by field_simp

private lemma tauberian_mpr {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    (hT : ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
      (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
      Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
        (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
      Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) :
    ∀ t : ℝ, 1 + ∑' k, Erdos967.summand t (a k) ≠ 0 := by
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨t₀, ht₀_zero⟩
  have ht₀_ne : t₀ ≠ 0 := by
    intro ht₀
    subst ht₀
    have hsum_terms : (fun k => Erdos967.summand 0 (a k)) = fun k => ((1 / (a k : ℝ) : ℝ) : ℂ) := by
      ext k
      rw [summand_eq 0 (a_pos ha ha₀ k)]
      simp
    have ht_eq : 1 + ∑' k, Erdos967.summand 0 (a k) =
        ((1 + ∑' k, 1 / (a k : ℝ) : ℝ) : ℂ) := by
      rw [hsum_terms, ← Complex.ofReal_tsum]
      push_cast; rfl
    have hre_pos : 0 < 1 + ∑' k, 1 / (a k : ℝ) := by
      have : 0 ≤ ∑' k, 1 / (a k : ℝ) := tsum_nonneg fun k => by positivity
      linarith
    have hc_ne : ((1 + ∑' k, 1 / (a k : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hre_pos.ne'
    exact hc_ne (ht_eq ▸ ht₀_zero)
  let ε : ℝ := 1 / (2 * (1 + |t₀|))
  have hε_pos : 0 < ε := by positivity
  let f : ℝ → ℝ := mprWitness t₀
  have hf_bdd : ∀ x y : ℝ, BddAbove (f '' Set.Icc x y) := by
    intro x y
    refine ⟨f y, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact mprWitness_mono t₀ hz.2
  have hlim := hT f (mprWitness_mono t₀) (mprWitness_nonneg t₀) (fun x hx => mprWitness_zero hx)
    hf_bdd (mprWitness_conv ha ha₀ hsum ht₀_zero)
  let xm : ℕ → ℝ := fun m => Real.exp (2 * Real.pi * ((m : ℝ) + 1) / |t₀|)
  have hxm_top : Tendsto xm atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have hcoeff : 0 < 2 * Real.pi / |t₀| := by positivity
    have : (fun m : ℕ => 2 * Real.pi * ((m : ℝ) + 1) / |t₀|) =
        fun m : ℕ => (2 * Real.pi / |t₀|) * ((m : ℝ) + 1) := by ext m; ring
    rw [this]
    exact Tendsto.const_mul_atTop hcoeff (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hval : ∀ m : ℕ, f (xm m) / xm m = 1 + ε := by
    intro m
    have harg_pos : 0 < 2 * Real.pi * ((m : ℝ) + 1) / |t₀| := by positivity
    have hxm_gt1 : 1 < xm m := Real.one_lt_exp_iff.mpr harg_pos
    have hxm_ge1 : 1 ≤ xm m := hxm_gt1.le
    dsimp [f, mprWitness, ε]
    rw [if_neg (not_lt.mpr hxm_ge1), Real.log_exp]
    have hcos1 : Real.cos (t₀ * (2 * Real.pi * ((m : ℝ) + 1) / |t₀|)) = 1 := by
      rcases le_or_gt 0 t₀ with ht_nn | ht_neg
      · have ht_pos : 0 < t₀ := lt_of_le_of_ne ht_nn ht₀_ne.symm
        rw [abs_of_pos ht_pos]
        have hmul : t₀ * (2 * Real.pi * ((m : ℝ) + 1) / t₀) = ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
          field_simp [ht_pos.ne']; push_cast; ring
        rw [hmul]
        exact Real.cos_nat_mul_two_pi (m + 1)
      · rw [abs_of_neg ht_neg]
        have hmul : t₀ * (2 * Real.pi * ((m : ℝ) + 1) / (-t₀)) = -(((m + 1 : ℕ) : ℝ) * (2 * Real.pi)) := by
          field_simp [ht_neg.ne]; push_cast; ring
        rw [hmul, Real.cos_neg]
        exact Real.cos_nat_mul_two_pi (m + 1)
    rw [hcos1]
    field_simp [(lt_trans zero_lt_one hxm_gt1).ne']
  have hlim_seq := hlim.comp hxm_top
  simp_rw [Function.comp_def, hval] at hlim_seq
  have hconst := tendsto_nhds_unique hlim_seq tendsto_const_nhds
  linarith

/- Step 3: L1 series, convolution, Fejer kernel, and trapezoid bump helpers -/

private lemma tsum_lintegral_enorm_ne_top
    {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℝ → E} (hF : ∀ k, Integrable (F k))
    (hsum : Summable (fun k => ∫ x, ‖F k x‖)) :
    ∑' k : ℕ, ∫⁻ x, ‖F k x‖ₑ ≠ ⊤ := by
  have heq : (fun k : ℕ => ∫⁻ x, ‖F k x‖ₑ) = fun k => ENNReal.ofReal (∫ x, ‖F k x‖) := by
    ext k
    exact (ofReal_integral_norm_eq_lintegral_enorm (hF k)).symm
  rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun x => norm_nonneg _) hsum]
  exact ENNReal.ofReal_ne_top

private lemma ae_summable_norm_of_summable_integral_norm
    {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℝ → E} (hF : ∀ k, Integrable (F k))
    (hsum : Summable (fun k => ∫ x, ‖F k x‖)) :
    ∀ᵐ x, Summable (fun k => ‖F k x‖) := by
  have hlt : ∑' k : ℕ, ∫⁻ x, ‖F k x‖ₑ ≠ ⊤ := tsum_lintegral_enorm_ne_top hF hsum
  have hlint : ∫⁻ x, ∑' k : ℕ, ‖F k x‖ₑ < ⊤ := by
    rw [lintegral_tsum (fun k => (hF k).aestronglyMeasurable.enorm)]
    exact lt_top_iff_ne_top.mpr hlt
  have hae_lt : ∀ᵐ x, ∑' k : ℕ, ‖F k x‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum fun k => (hF k).aestronglyMeasurable.enorm) hlint.ne
  filter_upwards [hae_lt] with x hx
  have hne : ∑' k : ℕ, (‖F k x‖₊ : ENNReal) ≠ ⊤ := by
    simpa [enorm_eq_nnnorm] using hx.ne
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hne)

private lemma aestronglyMeasurable_tsum_of_summable_norm
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → ℝ → E} (hF : ∀ k, Integrable (F k))
    (hae : ∀ᵐ x, Summable (fun k => ‖F k x‖)) :
    AEStronglyMeasurable (fun x => ∑' k, F k x) := by
  have hae_lim : ∀ᵐ x, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, F k x) atTop
      (𝓝 (∑' k, F k x)) := by
    filter_upwards [hae] with x hx
    exact hx.of_norm.hasSum.tendsto_sum_nat
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (Finset.range N).aestronglyMeasurable_fun_sum fun k _ => (hF k).aestronglyMeasurable)
    hae_lim

private lemma integrable_tsum_of_summable_norm
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → ℝ → E} (hF : ∀ k, Integrable (F k))
    (hsum : Summable (fun k => ∫ x, ‖F k x‖)) :
    Integrable (fun x => ∑' k, F k x) := by
  have hae : ∀ᵐ x, Summable (fun k => ‖F k x‖) :=
    ae_summable_norm_of_summable_integral_norm hF hsum
  have hmeas : AEStronglyMeasurable (fun x => ∑' k, F k x) :=
    aestronglyMeasurable_tsum_of_summable_norm hF hae
  have hof : ∀ v : E, ‖v‖ₑ = ENNReal.ofReal ‖v‖ := fun v => by
    rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg v)]
    rfl
  have hle_ae : (fun x => ‖∑' k, F k x‖ₑ) ≤ᵐ[volume] fun x => ∑' k, ‖F k x‖ₑ := by
    filter_upwards [hae] with x hx
    have hnorm := norm_tsum_le_tsum_norm hx
    have h2 : ∑' k, ‖F k x‖ₑ = ENNReal.ofReal (∑' k, ‖F k x‖) := by
      simp_rw [hof]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) hx).symm
    rw [hof, h2]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hlt : (∫⁻ x, ∑' k, ‖F k x‖ₑ) < ⊤ := by
    rw [lintegral_tsum (fun k => (hF k).aestronglyMeasurable.enorm)]
    exact lt_top_iff_ne_top.mpr (tsum_lintegral_enorm_ne_top hF hsum)
  exact ⟨hmeas, lt_of_le_of_lt (lintegral_mono_ae hle_ae) hlt⟩

private lemma integral_norm_tsum_le
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → ℝ → E} (hF : ∀ k, Integrable (F k))
    (hsum : Summable (fun k => ∫ x, ‖F k x‖)) :
    ∫ x, ‖∑' k, F k x‖ ≤ ∑' k, ∫ x, ‖F k x‖ := by
  have hae : ∀ᵐ x, Summable (fun k => ‖F k x‖) :=
    ae_summable_norm_of_summable_integral_norm hF hsum
  have hnorm_int : ∀ k, Integrable (fun x => ‖F k x‖) := fun k => (hF k).norm
  have hnorm_sum_int : Integrable (fun x => ∑' k, ‖F k x‖) :=
    integrable_tsum_of_summable_norm hnorm_int (by simpa [Real.norm_of_nonneg] using hsum)
  have htsum_int : Integrable (fun x => ∑' k, F k x) :=
    integrable_tsum_of_summable_norm hF hsum
  have hmono : ∫ x, ‖∑' k, F k x‖ ≤ ∫ x, ∑' k, ‖F k x‖ := by
    refine integral_mono_ae htsum_int.norm hnorm_sum_int ?_
    filter_upwards [hae] with x hx
    exact norm_tsum_le_tsum_norm hx
  have heq : ∫ x, ∑' k, ‖F k x‖ = ∑' k, ∫ x, ‖F k x‖ :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hnorm_int
      (by simpa [Real.norm_of_nonneg] using hsum)).symm
  linarith

private noncomputable def conv (f g : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume

private lemma integrable_conv {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (conv f g) :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

private lemma integral_norm_conv_le {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, ‖conv f g x‖ ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hprod : Integrable (fun p : ℝ × ℝ => ‖f p.2‖ * ‖g (p.1 - p.2)‖)
      (volume.prod volume) := by
    simpa [norm_mul] using
      (hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg).norm
  have houter : Integrable (fun x : ℝ => ∫ y : ℝ, ‖f y‖ * ‖g (x - y)‖) :=
    hprod.integral_prod_left
  calc ∫ x, ‖conv f g x‖
      ≤ ∫ x, ∫ y, ‖f y‖ * ‖g (x - y)‖ := by
          refine integral_mono (integrable_conv hf hg).norm houter fun x => ?_
          dsimp [conv]
          rw [MeasureTheory.convolution_def]
          calc ‖∫ y, (ContinuousLinearMap.mul ℂ ℂ) (f y) (g (x - y))‖
              ≤ ∫ y, ‖(ContinuousLinearMap.mul ℂ ℂ) (f y) (g (x - y))‖ :=
                norm_integral_le_integral_norm _
            _ = ∫ y, ‖f y‖ * ‖g (x - y)‖ := by
                simp_rw [ContinuousLinearMap.mul_apply', norm_mul]
    _ = ∫ y, ∫ x, ‖f y‖ * ‖g (x - y)‖ :=
          MeasureTheory.integral_integral_swap (f := fun x y : ℝ => ‖f y‖ * ‖g (x - y)‖) hprod
    _ = ∫ y, ‖f y‖ * ∫ x, ‖g (x - y)‖ := by simp_rw [integral_const_mul]
    _ = ∫ y, ‖f y‖ * ∫ x, ‖g x‖ := by
          have hsub : ∀ y : ℝ, ∫ x : ℝ, ‖g (x - y)‖ = ∫ x : ℝ, ‖g x‖ :=
            fun y => MeasureTheory.integral_sub_right_eq_self (fun x => ‖g x‖) y
          simp_rw [hsub]
    _ = (∫ y, ‖f y‖) * (∫ x, ‖g x‖) := integral_mul_const _ _

private lemma fourier_conv {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (conv f g) w = 𝓕 f w * 𝓕 g w :=
  Real.fourier_mul_convolution_eq hf hg w

private noncomputable def unitTent (w : ℝ) : ℝ := max 0 (1 - |w|)

private lemma unitTent_nonneg (w : ℝ) : 0 ≤ unitTent w := le_max_left _ _

private lemma unitTent_le_one (w : ℝ) : unitTent w ≤ 1 := by
  dsimp [unitTent]
  exact max_le (by norm_num) (by linarith [abs_nonneg w])

private lemma unitTent_eq_zero_of_one_le {w : ℝ} (hw : 1 ≤ |w|) : unitTent w = 0 := by
  dsimp [unitTent]
  exact max_eq_left (by linarith)

private lemma continuous_unitTent : Continuous unitTent :=
  continuous_const.max (continuous_const.sub continuous_abs)

private lemma hasCompactSupport_unitTent : HasCompactSupport (fun w : ℝ => (unitTent w : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun w hw => ?_
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  have habs : 1 ≤ |w| := by
    rcases hmem with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  exact hw (by simp [unitTent_eq_zero_of_one_le habs])

private lemma integrable_unitTent_complex : Integrable (fun w : ℝ => (unitTent w : ℂ)) :=
  (Complex.continuous_ofReal.comp continuous_unitTent).integrable_of_hasCompactSupport
    hasCompactSupport_unitTent

private noncomputable def fejerReal (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2

private lemma fejerReal_nonneg (x : ℝ) : 0 ≤ fejerReal x := by
  dsimp [fejerReal]; split_ifs <;> positivity

private lemma fejerReal_even (x : ℝ) : fejerReal (-x) = fejerReal x := by
  dsimp [fejerReal]
  by_cases hx : x = 0
  · subst hx; simp
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [if_neg hnx, if_neg hx, mul_neg, Real.sin_neg, neg_div_neg_eq]

private lemma fejerReal_le_one (x : ℝ) : fejerReal x ≤ 1 := by
  dsimp [fejerReal]
  split_ifs with hx
  · exact le_rfl
  · have hsin : |Real.sin (Real.pi * x)| ≤ |Real.pi * x| := Real.abs_sin_le_abs
    have hden_pos : 0 < |Real.pi * x| := abs_pos.mpr (mul_ne_zero Real.pi_ne_zero hx)
    have hdiv : |Real.sin (Real.pi * x) / (Real.pi * x)| ≤ 1 := by
      rw [abs_div, div_le_one hden_pos]
      exact hsin
    have hsq : (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 ≤ 1 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hdiv 2
    linarith

private lemma fejerReal_le_inv_sq {x : ℝ} (hx : x ≠ 0) :
    fejerReal x ≤ 1 / (Real.pi * x) ^ 2 := by
  dsimp [fejerReal]
  rw [if_neg hx, div_pow]
  have hsin2 : Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
    have h1 := Real.abs_sin_le_one (Real.pi * x)
    have h2 : |Real.sin (Real.pi * x)| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    linarith
  exact div_le_div_of_nonneg_right hsin2 (sq_nonneg _)

private lemma fejerReal_le_dom (x : ℝ) : fejerReal x ≤ 2 * (1 + x ^ 2)⁻¹ := by
  by_cases hx : |x| ≤ 1
  · have hx2 : x ^ 2 ≤ 1 := by
      rw [← sq_abs]
      have h := pow_le_pow_left₀ (abs_nonneg _) hx 2
      linarith
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have h1 : (1 : ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hpos]
      linarith
    exact (fejerReal_le_one x).trans h1
  · have hxgt : 1 < |x| := not_le.mp hx
    have hx_ne : x ≠ 0 := fun h => by subst h; norm_num at hxgt
    have hx2 : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      have := pow_le_pow_left₀ (by positivity) hxgt.le 2
      linarith
    have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
    have hden : x ^ 2 ≤ (Real.pi * x) ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg x, show (1 : ℝ) ≤ Real.pi ^ 2 by nlinarith]
    have hx2_pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx_ne
    calc fejerReal x ≤ 1 / (Real.pi * x) ^ 2 := fejerReal_le_inv_sq hx_ne
      _ ≤ 1 / x ^ 2 := div_le_div_of_nonneg_left (by norm_num) hx2_pos hden
      _ ≤ 2 / (1 + x ^ 2) := by
          rw [div_le_div_iff₀ hx2_pos (by positivity)]
          linarith
      _ = 2 * (1 + x ^ 2)⁻¹ := div_eq_mul_inv _ _

private lemma continuous_fejerReal : Continuous fejerReal := by
  have heq : fejerReal = fun x : ℝ => (Real.sinc (Real.pi * x)) ^ 2 := by
    ext x
    dsimp [fejerReal]
    by_cases hx : x = 0
    · subst hx; simp
    · simp [hx, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
  rw [heq]
  exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

private lemma integrable_fejerReal : Integrable fejerReal := by
  refine integrable_inv_one_add_sq.const_mul 2 |>.mono' continuous_fejerReal.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (fejerReal_nonneg x)]
  exact fejerReal_le_dom x

private lemma integrable_fejerReal_complex : Integrable (fun x : ℝ => (fejerReal x : ℂ)) :=
  integrable_fejerReal.ofReal

private lemma fourier_unitTent (x : ℝ) :
    𝓕 (fun w : ℝ => (unitTent w : ℂ)) x = (fejerReal x : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  have hsupp : ∫ w : ℝ, Complex.exp (((-2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) * (unitTent w : ℂ) =
      ∫ w in Set.Ioc (-1 : ℝ) 1,
        Complex.exp (((-2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) * (unitTent w : ℂ) := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
    by_cases hw1 : 1 ≤ |w|
    · simp [unitTent_eq_zero_of_one_le hw1]
    · have hlt : |w| < 1 := not_le.mp hw1
      exfalso; apply hw
      exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  rw [hsupp, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hcont : Continuous fun w : ℝ =>
      Complex.exp (((-2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) * (unitTent w : ℂ) := by
    refine Continuous.mul (Complex.continuous_exp.comp ?_)
      (Complex.continuous_ofReal.comp continuous_unitTent)
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)]
  have hleft : ∫ w in (-1 : ℝ)..0,
      Complex.exp (((-2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) * (unitTent w : ℂ) =
      ∫ w in (-1 : ℝ)..0,
        Complex.exp (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I * (w : ℂ)) * (1 + (w : ℂ)) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Icc] at hw
    have htent : unitTent w = 1 + w := by
      dsimp [unitTent]; rw [abs_of_nonpos hw.2]
      have h1 : 0 ≤ 1 - -w := by linarith [hw.1]
      rw [max_eq_right h1]; ring
    rw [htent]
    congr 1
    · congr 1; push_cast; ring
    · push_cast; ring
  have hright : ∫ w in (0 : ℝ)..1,
      Complex.exp (((-2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) * (unitTent w : ℂ) =
      ∫ w in (0 : ℝ)..1,
        Complex.exp (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I * (w : ℂ)) * (1 - (w : ℂ)) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hw
    have htent : unitTent w = 1 - w := by
      dsimp [unitTent]; rw [abs_of_nonneg hw.1]
      have h1 : 0 ≤ 1 - w := by linarith [hw.2]
      exact max_eq_right h1
    rw [htent]
    congr 1
    · congr 1; push_cast; ring
    · push_cast; ring
  rw [hleft, hright]
  by_cases hx : x = 0
  · subst hx
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, fejerReal]
    have hL_r : ∫ w in (-1 : ℝ)..0, (1 + w) = 1 / 2 := by
      have hd : ∀ w ∈ Set.uIcc (-1 : ℝ) 0,
          HasDerivAt (fun y : ℝ => y + y ^ 2 / 2) (1 + w) w := by
        intro w _
        exact ((hasDerivAt_id w).add ((hasDerivAt_pow 2 w).div_const 2)).congr_deriv (by norm_num)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
      norm_num
    have hR_r : ∫ w in (0 : ℝ)..1, (1 - w) = 1 / 2 := by
      have hd : ∀ w ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - w) w := by
        intro w _
        exact ((hasDerivAt_id w).sub ((hasDerivAt_pow 2 w).div_const 2)).congr_deriv (by norm_num)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
      norm_num
    have hL : ∫ w in (-1 : ℝ)..0, (1 + (w : ℂ)) = (1 / 2 : ℂ) := by
      have h1 : (fun w : ℝ => (1 + (w : ℂ))) = fun w => ((1 + w : ℝ) : ℂ) := by
        ext w; push_cast; rfl
      rw [h1, intervalIntegral.integral_ofReal, hL_r]
      norm_num
    have hR : ∫ w in (0 : ℝ)..1, (1 - (w : ℂ)) = (1 / 2 : ℂ) := by
      have h1 : (fun w : ℝ => (1 - (w : ℂ))) = fun w => ((1 - w : ℝ) : ℂ) := by
        ext w; push_cast; rfl
      rw [h1, intervalIntegral.integral_ofReal, hR_r]
      norm_num
    rw [hL, hR]; norm_num
  · let k : ℂ := ((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I
    have hk : k ≠ 0 := by
      dsimp [k]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)) Complex.I_ne_zero
    let F2 : ℝ → ℂ := fun w => ((1 + (w : ℂ)) / k - 1 / k ^ 2) * Complex.exp (k * (w : ℂ))
    let F1 : ℝ → ℂ := fun w => ((1 - (w : ℂ)) / k + 1 / k ^ 2) * Complex.exp (k * (w : ℂ))
    have hF2 : ∀ w ∈ Set.uIcc (-1 : ℝ) 0,
        HasDerivAt F2 (Complex.exp (k * (w : ℂ)) * (1 + (w : ℂ))) w := by
      intro w _
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 w := (hasDerivAt_id w).ofReal_comp
      have hlin : HasDerivAt (fun y : ℝ => (1 + (y : ℂ)) / k - 1 / k ^ 2) (1 / k) w :=
        ((((hasDerivAt_const w (1 : ℂ)).add hid).div_const k).sub
          (hasDerivAt_const w (1 / k ^ 2))).congr_deriv (by ring)
      have hexp : HasDerivAt (fun y : ℝ => Complex.exp (k * (y : ℂ))) (Complex.exp (k * (w : ℂ)) * k) w :=
        ((hid.const_mul k).cexp).congr_deriv (by ring)
      exact (hlin.mul hexp).congr_deriv (by field_simp [hk]; ring)
    have hF1 : ∀ w ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt F1 (Complex.exp (k * (w : ℂ)) * (1 - (w : ℂ))) w := by
      intro w _
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 w := (hasDerivAt_id w).ofReal_comp
      have hlin : HasDerivAt (fun y : ℝ => (1 - (y : ℂ)) / k + 1 / k ^ 2) (-1 / k) w :=
        ((((hasDerivAt_const w (1 : ℂ)).sub hid).div_const k).add
          (hasDerivAt_const w (1 / k ^ 2))).congr_deriv (by ring)
      have hexp : HasDerivAt (fun y : ℝ => Complex.exp (k * (y : ℂ))) (Complex.exp (k * (w : ℂ)) * k) w :=
        ((hid.const_mul k).cexp).congr_deriv (by ring)
      exact (hlin.mul hexp).congr_deriv (by field_simp [hk]; ring)
    have hL : ∫ w in (-1 : ℝ)..0, Complex.exp (k * (w : ℂ)) * (1 + (w : ℂ)) = F2 0 - F2 (-1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hF2 (by apply Continuous.intervalIntegrable; fun_prop)
    have hR : ∫ w in (0 : ℝ)..1, Complex.exp (k * (w : ℂ)) * (1 - (w : ℂ)) = F1 1 - F1 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hF1 (by apply Continuous.intervalIntegrable; fun_prop)
    change (∫ w in (-1 : ℝ)..0, Complex.exp (k * (w : ℂ)) * (1 + (w : ℂ))) +
        (∫ w in (0 : ℝ)..1, Complex.exp (k * (w : ℂ)) * (1 - (w : ℂ))) = (fejerReal x : ℂ)
    rw [hL, hR]
    dsimp [F1, F2]
    have hcomb : (((1 + 0) / k - 1 / k ^ 2) * Complex.exp (k * 0) -
          ((1 + ((-1 : ℝ) : ℂ)) / k - 1 / k ^ 2) * Complex.exp (k * ((-1 : ℝ) : ℂ))) +
          (((1 - 1) / k + 1 / k ^ 2) * Complex.exp (k * 1) -
          ((1 - 0) / k + 1 / k ^ 2) * Complex.exp (k * 0)) =
        (Complex.exp (k / 2) - Complex.exp (-(k / 2))) ^ 2 / k ^ 2 := by
      have hexp_sq : (Complex.exp (k / 2) - Complex.exp (-(k / 2))) ^ 2 =
          Complex.exp k + Complex.exp (-k) - 2 := by
        calc (Complex.exp (k / 2) - Complex.exp (-(k / 2))) ^ 2
            = Complex.exp (k / 2) * Complex.exp (k / 2) -
                2 * (Complex.exp (k / 2) * Complex.exp (-(k / 2))) +
                Complex.exp (-(k / 2)) * Complex.exp (-(k / 2)) := by ring
          _ = Complex.exp (k / 2 + k / 2) - 2 * Complex.exp (k / 2 + -(k / 2)) +
                Complex.exp (-(k / 2) + -(k / 2)) := by
                rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
          _ = Complex.exp k + Complex.exp (-k) - 2 := by
                simp only [add_halves, add_neg_cancel, Complex.exp_zero]
                have hneg : -(k / 2) + -(k / 2) = -k := by ring
                rw [hneg]; ring
      rw [hexp_sq]
      simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_zero, Complex.exp_zero, mul_neg, mul_one]
      ring
    rw [hcomb]
    have hk2 : k / 2 = -(((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      dsimp [k]; push_cast; ring
    have hsin_c : Complex.exp (k / 2) - Complex.exp (-(k / 2)) =
        -2 * Complex.I * Complex.sin ((Real.pi * x : ℝ) : ℂ) := by
      rw [hk2, neg_neg, show -(((Real.pi * x : ℝ) : ℂ) * Complex.I) = (-((Real.pi * x : ℝ) : ℂ)) * Complex.I by ring,
        Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    rw [hsin_c]
    have hnum_sq : (-2 * Complex.I * Complex.sin ((Real.pi * x : ℝ) : ℂ)) ^ 2 =
        -4 * Complex.sin ((Real.pi * x : ℝ) : ℂ) ^ 2 := by
      rw [mul_pow, mul_pow, Complex.I_sq]; ring
    have hk_eq : k ^ 2 = -4 * (((Real.pi * x : ℝ) : ℂ) ^ 2) := by
      dsimp [k]
      rw [mul_pow, Complex.I_sq]
      push_cast; ring
    rw [hnum_sq, hk_eq]
    dsimp [fejerReal]
    rw [if_neg hx]
    push_cast
    have hpx_ne : ((Real.pi * x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
    field_simp [hpx_ne]

private lemma fourier_fejerReal (w : ℝ) :
    𝓕 (fun x : ℝ => (fejerReal x : ℂ)) w = (unitTent w : ℂ) := by
  have h𝓕 : 𝓕 (fun y : ℝ => (unitTent y : ℂ)) = fun x : ℝ => (fejerReal x : ℂ) := by
    ext x; exact fourier_unitTent x
  have hinv := congrFun (Continuous.fourier_fourierInv_eq
    (Complex.continuous_ofReal.comp continuous_unitTent) integrable_unitTent_complex
    (h𝓕 ▸ integrable_fejerReal_complex)) w
  have hfejer : 𝓕⁻ (fun y : ℝ => (unitTent y : ℂ)) = fun x : ℝ => (fejerReal x : ℂ) := by
    ext x
    rw [Real.fourierInv_eq_fourier_neg, fourier_unitTent, fejerReal_even]
  change 𝓕 (𝓕⁻ (fun y : ℝ => (unitTent y : ℂ))) w = (unitTent w : ℂ) at hinv
  rw [hfejer] at hinv
  exact hinv

private lemma integral_fejerReal : ∫ x : ℝ, fejerReal x = 1 := by
  have h0 := fourier_fejerReal 0
  rw [Real.fourier_real_eq_integral_exp_smul] at h0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul, unitTent, abs_zero,
    sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] at h0
  have hre := congrArg Complex.re h0
  have heq := integral_re integrable_fejerReal_complex
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at heq hre
  linarith

private noncomputable def tent (w₀ δ w : ℝ) : ℝ := unitTent ((w - w₀) / δ)

private noncomputable def tentPre (w₀ δ x : ℝ) : ℂ :=
  ((δ * fejerReal (δ * x) : ℝ) : ℂ) * Complex.exp ((2 * Real.pi * w₀ * x : ℝ) * Complex.I)

private lemma continuous_tentPre (w₀ δ : ℝ) : Continuous (tentPre w₀ δ) := by
  refine (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_fejerReal.comp
    (continuous_const.mul continuous_id)))).mul (Complex.continuous_exp.comp ?_)
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const

private lemma norm_tentPre (w₀ δ x : ℝ) (hδ : 0 < δ) :
    ‖tentPre w₀ δ x‖ = δ * fejerReal (δ * x) := by
  dsimp [tentPre]
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_of_nonneg (mul_nonneg hδ.le (fejerReal_nonneg _))]

private lemma norm_tentPre_le (w₀ δ x : ℝ) (hδ : 0 < δ) :
    ‖tentPre w₀ δ x‖ ≤ δ := by
  rw [norm_tentPre w₀ δ x hδ]
  exact mul_le_of_le_one_right hδ.le (fejerReal_le_one _)

private lemma integrable_tentPre (w₀ δ : ℝ) (hδ : 0 < δ) : Integrable (tentPre w₀ δ) := by
  have hsc : Integrable (fun x : ℝ => δ * fejerReal (δ * x)) :=
    (integrable_fejerReal.comp_mul_left' hδ.ne').const_mul δ
  refine hsc.mono' (continuous_tentPre w₀ δ).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_tentPre w₀ δ x hδ]

private lemma integral_norm_tentPre (w₀ δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, ‖tentPre w₀ δ x‖ = 1 := by
  simp_rw [norm_tentPre w₀ δ _ hδ, integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left fejerReal δ, smul_eq_mul]
  rw [abs_of_pos (inv_pos.mpr hδ), integral_fejerReal]
  field_simp [hδ.ne']

private lemma fourier_tentPre (w₀ δ w : ℝ) (hδ : 0 < δ) :
    𝓕 (tentPre w₀ δ) w = (tent w₀ δ w : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have heq : (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) • tentPre w₀ δ x) =
      fun x : ℝ => (δ : ℂ) * (Complex.exp (((-2 * Real.pi * (δ * x) * ((w - w₀) / δ) : ℝ) : ℂ) * Complex.I) •
        (fejerReal (δ * x) : ℂ)) := by
    ext x
    dsimp [tentPre]
    rw [Complex.ofReal_mul δ (fejerReal (δ * x))]
    have hmul : Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
          (((δ : ℂ) * (fejerReal (δ * x) : ℂ)) * Complex.exp ((2 * Real.pi * w₀ * x : ℝ) * Complex.I)) =
        (δ : ℂ) * (Complex.exp ((((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) +
            ((2 * Real.pi * w₀ * x : ℝ) : ℂ) * Complex.I) * (fejerReal (δ * x) : ℂ)) := by
      rw [Complex.exp_add]; ring
    have hexp : (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) +
          ((2 * Real.pi * w₀ * x : ℝ) : ℂ) * Complex.I =
        ((-2 * Real.pi * (δ * x) * ((w - w₀) / δ) : ℝ) : ℂ) * Complex.I := by
      push_cast; field_simp [hδ.ne']; ring
    rw [hmul, hexp]
  rw [heq, integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => Complex.exp (((-2 * Real.pi * y * ((w - w₀) / δ) : ℝ) : ℂ) * Complex.I) • (fejerReal y : ℂ)) δ]
  rw [Complex.real_smul, abs_of_pos (inv_pos.mpr hδ)]
  have h1 : (δ : ℂ) * ((δ⁻¹ : ℝ) : ℂ) = 1 := by push_cast; field_simp [hδ.ne']
  rw [← mul_assoc, h1, one_mul, ← Real.fourier_real_eq_integral_exp_smul, fourier_fejerReal]
  rfl

private noncomputable def trap (w₀ δ w : ℝ) : ℝ :=
  2 * tent w₀ (2 * δ) w - tent w₀ δ w

private noncomputable def trapPre (w₀ δ x : ℝ) : ℂ :=
  2 * tentPre w₀ (2 * δ) x - tentPre w₀ δ x

private lemma trap_eq_one_of_mem_Icc {w₀ δ w : ℝ} (hδ : 0 < δ)
    (hw : w ∈ Set.Icc (w₀ - δ) (w₀ + δ)) : trap w₀ δ w = 1 := by
  have habs : |w - w₀| ≤ δ := abs_sub_le_iff.mpr ⟨by linarith [hw.2], by linarith [hw.1]⟩
  have h1 : |(w - w₀) / (2 * δ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (mul_pos zero_lt_two hδ), div_le_iff₀ (mul_pos zero_lt_two hδ)]
    linarith
  have h2 : |(w - w₀) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ]
    exact habs
  have ht2 : tent w₀ (2 * δ) w = 1 - |(w - w₀) / (2 * δ)| := by
    dsimp [tent, unitTent]; exact max_eq_right (by linarith)
  have ht1 : tent w₀ δ w = 1 - |(w - w₀) / δ| := by
    dsimp [tent, unitTent]; exact max_eq_right (by linarith)
  have hr : |(w - w₀) / (2 * δ)| = |(w - w₀) / δ| / 2 := by
    rw [abs_div, abs_div, abs_of_pos (mul_pos zero_lt_two hδ), abs_of_pos hδ]
    ring
  dsimp [trap]
  rw [ht2, ht1, hr]
  ring

private lemma continuous_trapPre (w₀ δ : ℝ) : Continuous (trapPre w₀ δ) :=
  (continuous_const.mul (continuous_tentPre w₀ (2 * δ))).sub (continuous_tentPre w₀ δ)

private lemma integrable_trapPre (w₀ δ : ℝ) (hδ : 0 < δ) : Integrable (trapPre w₀ δ) :=
  ((integrable_tentPre w₀ (2 * δ) (by linarith)).const_mul 2).sub (integrable_tentPre w₀ δ hδ)

private lemma integral_norm_trapPre_le (w₀ δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, ‖trapPre w₀ δ x‖ ≤ 3 := by
  have h2 : Integrable (fun x : ℝ => 2 * ‖tentPre w₀ (2 * δ) x‖) :=
    (integrable_tentPre w₀ (2 * δ) (by linarith)).norm.const_mul 2
  have h1 : Integrable (fun x : ℝ => ‖tentPre w₀ δ x‖) :=
    (integrable_tentPre w₀ δ hδ).norm
  calc ∫ x : ℝ, ‖trapPre w₀ δ x‖
      ≤ ∫ x : ℝ, (2 * ‖tentPre w₀ (2 * δ) x‖ + ‖tentPre w₀ δ x‖) := by
          refine integral_mono (integrable_trapPre w₀ δ hδ).norm (h2.add h1) fun x => ?_
          dsimp [trapPre]
          calc ‖2 * tentPre w₀ (2 * δ) x - tentPre w₀ δ x‖
              ≤ ‖2 * tentPre w₀ (2 * δ) x‖ + ‖tentPre w₀ δ x‖ := norm_sub_le _ _
            _ = 2 * ‖tentPre w₀ (2 * δ) x‖ + ‖tentPre w₀ δ x‖ := by
                rw [norm_mul, Complex.norm_ofNat]
    _ = 2 * (∫ x : ℝ, ‖tentPre w₀ (2 * δ) x‖) + ∫ x : ℝ, ‖tentPre w₀ δ x‖ := by
          rw [integral_add h2 h1, integral_const_mul]
    _ = 2 * 1 + 1 := by
          rw [integral_norm_tentPre w₀ (2 * δ) (by linarith), integral_norm_tentPre w₀ δ hδ]
    _ = 3 := by norm_num

private lemma integrable_exp_mul {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * f x) := by
  refine hf.norm.mono' ?_ ?_
  · exact ((Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

private lemma fourier_trapPre (w₀ δ w : ℝ) (hδ : 0 < δ) :
    𝓕 (trapPre w₀ δ) w = (trap w₀ δ w : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  have hi2 : Integrable (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
      ((2 : ℂ) * tentPre w₀ (2 * δ) x)) :=
    integrable_exp_mul ((integrable_tentPre w₀ (2 * δ) (by linarith)).const_mul 2) w
  have hi1 : Integrable (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
      tentPre w₀ δ x) :=
    integrable_exp_mul (integrable_tentPre w₀ δ hδ) w
  have hsub_fn :
      (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * trapPre w₀ δ x) =
      (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * ((2 : ℂ) * tentPre w₀ (2 * δ) x)) -
      (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * tentPre w₀ δ x) := by
    rw [← integral_sub hi2 hi1]
    congr 1; ext x; dsimp [trapPre]; ring
  rw [hsub_fn]
  have h2_eq : (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
      ((2 : ℂ) * tentPre w₀ (2 * δ) x)) =
      fun x => (2 : ℂ) * (Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
        tentPre w₀ (2 * δ) x) := by
    ext x; ring
  rw [h2_eq, integral_const_mul]
  have hf1 : (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * tentPre w₀ (2 * δ) x) =
      𝓕 (tentPre w₀ (2 * δ)) w := by
    rw [Real.fourier_real_eq_integral_exp_smul]; simp_rw [smul_eq_mul]
  have hf2 : (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * tentPre w₀ δ x) =
      𝓕 (tentPre w₀ δ) w := by
    rw [Real.fourier_real_eq_integral_exp_smul]; simp_rw [smul_eq_mul]
  rw [hf1, hf2, fourier_tentPre w₀ (2 * δ) w (by linarith), fourier_tentPre w₀ δ w hδ]
  dsimp [trap]; push_cast; ring

private lemma tendsto_fejerReal_shift :
    Tendsto (fun h : ℝ => ∫ y : ℝ, |fejerReal (y - h) - fejerReal y|) (𝓝 0) (𝓝 0) := by
  let bound : ℝ → ℝ := fun y => 10 * (1 + y ^ 2)⁻¹
  have hbound_int : Integrable bound := integrable_inv_one_add_sq.const_mul 10
  have hlim_zero : (∫ y : ℝ, (0 : ℝ)) = 0 := MeasureTheory.integral_zero ℝ ℝ
  conv_rhs => rw [← hlim_zero]
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
  · refine Eventually.of_forall fun h => ?_
    exact (continuous_abs.comp ((continuous_fejerReal.comp (continuous_id.sub continuous_const)).sub
      continuous_fejerReal)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with h hh
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at hh
    refine ae_of_all _ fun y => ?_
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    by_cases hy : |y| ≤ 2
    · have hy2 : y ^ 2 ≤ 4 := by
        rw [← sq_abs]
        have := pow_le_pow_left₀ (abs_nonneg _) hy 2
        linarith
      have hdiff : |fejerReal (y - h) - fejerReal y| ≤ 2 := by
        calc |fejerReal (y - h) - fejerReal y|
            ≤ |fejerReal (y - h)| + |fejerReal y| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add
              (by rw [abs_of_nonneg (fejerReal_nonneg _)]; exact fejerReal_le_one _)
              (by rw [abs_of_nonneg (fejerReal_nonneg _)]; exact fejerReal_le_one _)
          _ = 2 := by norm_num
      have hdom : (2 : ℝ) ≤ bound y := by
        dsimp [bound]
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        linarith
      exact hdiff.trans hdom
    · have hygt : 2 < |y| := not_le.mp hy
      have hy_pos : 0 < |y| := by linarith
      have hy_ne : y ≠ 0 := fun h0 => by subst h0; norm_num at hygt
      have hyh_lb : |y| / 2 ≤ |y - h| := by
        have := abs_sub_abs_le_abs_sub y h
        linarith
      have hyh_pos : 0 < |y - h| := by linarith
      have hyh_ne : y - h ≠ 0 := fun h0 => by rw [h0, abs_zero] at hyh_pos; linarith
      have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by
        have := Real.two_le_pi
        nlinarith
      have h1 : fejerReal (y - h) ≤ 1 / y ^ 2 := by
        have hden : y ^ 2 ≤ (Real.pi * (y - h)) ^ 2 := by
          rw [mul_pow, ← sq_abs (y - h), ← sq_abs y]
          have hsq : (|y| / 2) ^ 2 ≤ |y - h| ^ 2 := pow_le_pow_left₀ (by positivity) hyh_lb 2
          calc |y| ^ 2 = 4 * (|y| / 2) ^ 2 := by ring
            _ ≤ Real.pi ^ 2 * |y - h| ^ 2 := mul_le_mul hpi2 hsq (by positivity) (by positivity)
        calc fejerReal (y - h) ≤ 1 / (Real.pi * (y - h)) ^ 2 := fejerReal_le_inv_sq hyh_ne
          _ ≤ 1 / y ^ 2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_ne_zero hy_ne) hden
      have h2 : fejerReal y ≤ 1 / y ^ 2 := by
        have hden : y ^ 2 ≤ (Real.pi * y) ^ 2 := by
          rw [mul_pow]
          nlinarith [sq_nonneg y]
        calc fejerReal y ≤ 1 / (Real.pi * y) ^ 2 := fejerReal_le_inv_sq hy_ne
          _ ≤ 1 / y ^ 2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_ne_zero hy_ne) hden
      have hdiff : |fejerReal (y - h) - fejerReal y| ≤ 2 / y ^ 2 := by
        calc |fejerReal (y - h) - fejerReal y|
            ≤ |fejerReal (y - h)| + |fejerReal y| := abs_sub _ _
          _ = fejerReal (y - h) + fejerReal y := by
              rw [abs_of_nonneg (fejerReal_nonneg _), abs_of_nonneg (fejerReal_nonneg _)]
          _ ≤ 1 / y ^ 2 + 1 / y ^ 2 := add_le_add h1 h2
          _ = 2 / y ^ 2 := by ring
      have hy2 : 4 ≤ y ^ 2 := by
        rw [← sq_abs]
        have := pow_le_pow_left₀ (by positivity) hygt.le 2
        linarith
      have hdom : 2 / y ^ 2 ≤ bound y := by
        dsimp [bound]
        rw [← div_eq_mul_inv, div_le_div_iff₀ (sq_pos_of_ne_zero hy_ne) (by positivity)]
        linarith
      exact hdiff.trans hdom
  · refine ae_of_all _ fun y => ?_
    have hid : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
    have hsub_tend : Tendsto (fun h : ℝ => y - h) (𝓝 0) (𝓝 y) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := y)).sub hid
    have hcont_diff : Tendsto (fun h : ℝ => |fejerReal (y - h) - fejerReal y|) (𝓝 0) (𝓝 0) := by
      have h1 := (continuous_fejerReal.continuousAt.tendsto.comp hsub_tend).sub (tendsto_const_nhds (x := fejerReal y))
      simpa using h1.abs
    exact hcont_diff

private lemma tendsto_tentPre_shift (w₀ l : ℝ) :
    Tendsto (fun δ : ℝ => ∫ x : ℝ,
      ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ δ x -
        tentPre w₀ δ (x - l)‖) (𝓝[>] 0) (𝓝 0) := by
  have heq : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∫ x : ℝ, ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ δ x -
          tentPre w₀ δ (x - l)‖) =
        ∫ y : ℝ, |fejerReal (y - δ * l) - fejerReal y| := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    have hfun : (fun x : ℝ =>
        ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ δ x -
          tentPre w₀ δ (x - l)‖) =
        fun x : ℝ => δ * |fejerReal (δ * x - δ * l) - fejerReal (δ * x)| := by
      ext x
      dsimp [tentPre]
      have hexp_mul : Complex.exp ((2 * Real.pi * w₀ * (x - l) : ℝ) * Complex.I) =
          Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) *
            Complex.exp ((2 * Real.pi * w₀ * x : ℝ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1; push_cast; ring
      have hsub_eq : Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) *
            (((δ * fejerReal (δ * x) : ℝ) : ℂ) * Complex.exp ((2 * Real.pi * w₀ * x : ℝ) * Complex.I)) -
            ((δ * fejerReal (δ * (x - l)) : ℝ) : ℂ) * Complex.exp ((2 * Real.pi * w₀ * (x - l) : ℝ) * Complex.I) =
          (Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) *
            Complex.exp ((2 * Real.pi * w₀ * x : ℝ) * Complex.I)) *
            ((δ * (fejerReal (δ * x) - fejerReal (δ * x - δ * l)) : ℝ) : ℂ) := by
        rw [hexp_mul]
        push_cast
        have : δ * (x - l) = δ * x - δ * l := by ring
        rw [this]
        ring
      rw [hsub_eq, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
        mul_one, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hδ_pos,
        abs_sub_comm]
    rw [hfun, integral_const_mul,
      MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => |fejerReal (y - δ * l) - fejerReal y|) δ,
      smul_eq_mul, abs_of_pos (inv_pos.mpr hδ_pos), ← mul_assoc, mul_inv_cancel₀ hδ_pos.ne', one_mul]
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
  have hmul_tend : Tendsto (fun δ : ℝ => δ * l) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using (hid.mul_const l).mono_left nhdsWithin_le_nhds
  exact (tendsto_fejerReal_shift.comp hmul_tend).congr' (heq.mono fun δ h => h.symm)

private lemma tendsto_trapPre_shift (w₀ l : ℝ) :
    Tendsto (fun δ : ℝ => ∫ x : ℝ,
      ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - l)‖) (𝓝[>] 0) (𝓝 0) := by
  have ht2 : Tendsto (fun δ : ℝ => ∫ x : ℝ,
      ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ (2 * δ) x -
        tentPre w₀ (2 * δ) (x - l)‖) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    have hmap : Tendsto (fun δ : ℝ => 2 * δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa only [mul_zero] using (hid.const_mul (2 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        have hδ' : 0 < δ := hδ
        show 0 < 2 * δ
        linarith
    exact (tendsto_tentPre_shift w₀ l).comp hmap
  have hlim_sum : Tendsto (fun δ : ℝ =>
      2 * (∫ x : ℝ, ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ (2 * δ) x -
          tentPre w₀ (2 * δ) (x - l)‖) +
        ∫ x : ℝ, ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ δ x -
          tentPre w₀ δ (x - l)‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ht2.const_mul 2).add (tendsto_tentPre_shift w₀ l)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_sum ?_ ?_
  · exact Eventually.of_forall fun δ => integral_nonneg fun x => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    let A : ℝ → ℂ := fun x =>
      Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ (2 * δ) x -
        tentPre w₀ (2 * δ) (x - l)
    let B : ℝ → ℂ := fun x =>
      Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * tentPre w₀ δ x -
        tentPre w₀ δ (x - l)
    have hA_int : Integrable (fun x : ℝ => 2 * ‖A x‖) := by
      have hi := ((integrable_tentPre w₀ (2 * δ) (by linarith)).const_mul
          (Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I))).sub
        ((integrable_tentPre w₀ (2 * δ) (by linarith)).comp_sub_right l)
      exact hi.norm.const_mul 2
    have hB_int : Integrable (fun x : ℝ => ‖B x‖) := by
      have hi := ((integrable_tentPre w₀ δ hδ_pos).const_mul
          (Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I))).sub
        ((integrable_tentPre w₀ δ hδ_pos).comp_sub_right l)
      exact hi.norm
    have hT_int : Integrable (fun x : ℝ =>
        ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - l)‖) := by
      have hi := ((integrable_trapPre w₀ δ hδ_pos).const_mul
          (Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I))).sub
        ((integrable_trapPre w₀ δ hδ_pos).comp_sub_right l)
      exact hi.norm
    calc ∫ x : ℝ, ‖Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - l)‖
        ≤ ∫ x : ℝ, (2 * ‖A x‖ + ‖B x‖) := by
            refine integral_mono hT_int (hA_int.add hB_int) fun x => ?_
            have heq : Complex.exp ((-(2 * Real.pi * w₀ * l) : ℝ) * Complex.I) * trapPre w₀ δ x -
                trapPre w₀ δ (x - l) = 2 * A x - B x := by
              dsimp [trapPre, A, B]; ring
            rw [heq]
            calc ‖2 * A x - B x‖ ≤ ‖2 * A x‖ + ‖B x‖ := norm_sub_le _ _
              _ = 2 * ‖A x‖ + ‖B x‖ := by rw [norm_mul, Complex.norm_ofNat]
      _ = 2 * (∫ x : ℝ, ‖A x‖) + ∫ x : ℝ, ‖B x‖ := by
            rw [integral_add hA_int hB_int, integral_const_mul]

/- ## Step 4: Local and global Wiener inversion -/

private noncomputable def Ψ (a : ℕ → ℕ) (w : ℝ) : ℂ :=
  1 + ∑' k : ℕ, Erdos967.summand (2 * Real.pi * w) (a k)

private noncomputable def opM (a : ℕ → ℕ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  φ x + ∑' k : ℕ, ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))

private lemma integrable_opM_term (a : ℕ → ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (k : ℕ) :
    Integrable (fun x : ℝ => ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))) :=
  (hφ.comp_sub_right (Real.log (a k : ℝ))).const_mul _

private lemma integral_norm_opM_term (a : ℕ → ℕ) {φ : ℝ → ℂ} (_hφ : Integrable φ) (k : ℕ) :
    ∫ x : ℝ, ‖((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))‖ =
      (1 / (a k : ℝ)) * ∫ x : ℝ, ‖φ x‖ := by
  have hfun : (fun x : ℝ => ‖((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))‖) =
      fun x : ℝ => (1 / (a k : ℝ)) * ‖φ (x - Real.log (a k : ℝ))‖ := by
    ext x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hfun, integral_const_mul, MeasureTheory.integral_sub_right_eq_self (fun x => ‖φ x‖) _]

private lemma summable_norm_opM_term (a : ℕ → ℕ) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    {φ : ℝ → ℂ} (hφ : Integrable φ) :
    Summable (fun k : ℕ => ∫ x : ℝ, ‖((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))‖) := by
  simp_rw [integral_norm_opM_term a hφ]
  exact hsum.mul_right _

private lemma integrable_opM (a : ℕ → ℕ) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    {φ : ℝ → ℂ} (hφ : Integrable φ) : Integrable (opM a φ) :=
  hφ.add (integrable_tsum_of_summable_norm (fun k => integrable_opM_term a hφ k)
    (summable_norm_opM_term a hsum hφ))

private lemma fourier_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (fun x => f x - g x) w = 𝓕 f w - 𝓕 g w := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, mul_sub]
  exact integral_sub (integrable_exp_mul hf w) (integrable_exp_mul hg w)

private lemma fourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (fun x => f x + g x) w = 𝓕 f w + 𝓕 g w := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, mul_add]
  exact integral_add (integrable_exp_mul hf w) (integrable_exp_mul hg w)

private lemma fourier_const_mul {f : ℝ → ℂ} (c : ℂ) (w : ℝ) :
    𝓕 (fun x => c * f x) w = c * 𝓕 f w := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  have hfun : (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * (c * f x)) =
      fun x : ℝ => c * (Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * f x) := by
    ext x; ring
  rw [hfun, integral_const_mul]

private lemma fourier_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (w : ℝ) :
    𝓕 (fun x => ∑ i ∈ s, f i x) w = ∑ i ∈ s, 𝓕 (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp
  | @insert j s hj ih =>
      simp_rw [Finset.sum_insert hj]
      have hj_int : Integrable (f j) := hf j (Finset.mem_insert_self _ _)
      have hs_int : Integrable (fun x => ∑ i ∈ s, f i x) :=
        integrable_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [fourier_add hj_int hs_int w, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private lemma fourier_opM_term {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (φ : ℝ → ℂ) (w : ℝ) (k : ℕ) :
    ∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
        (((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))) =
      Erdos967.summand (2 * Real.pi * w) (a k) * 𝓕 φ w := by
  let l : ℝ := Real.log (a k : ℝ)
  have hfun : (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
        (((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - l))) =
      fun x : ℝ => Erdos967.summand (2 * Real.pi * w) (a k) *
        (Complex.exp (((-2 * Real.pi * (x - l) * w : ℝ) : ℂ) * Complex.I) * φ (x - l)) := by
    ext x
    rw [summand_eq (2 * Real.pi * w) (a_pos ha ha₀ k)]
    have hexp : Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((-(2 * Real.pi * w * l) : ℝ) * Complex.I) *
          Complex.exp (((-2 * Real.pi * (x - l) * w : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hexp]; ring
  rw [hfun, integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self
      (fun y : ℝ => Complex.exp (((-2 * Real.pi * y * w : ℝ) : ℂ) * Complex.I) * φ y) l,
    Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]

private lemma fourier_opM {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) {φ : ℝ → ℂ} (hφ : Integrable φ) (w : ℝ) :
    𝓕 (opM a φ) w = 𝓕 φ w * Ψ a w := by
  let F : ℕ → ℝ → ℂ := fun k x => ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (x - Real.log (a k : ℝ))
  let e : ℝ → ℂ := fun x => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)
  let G : ℕ → ℝ → ℂ := fun k x => e x * F k x
  have hF_int : ∀ k, Integrable (F k) := fun k => integrable_opM_term a hφ k
  have hF_sum : Summable (fun k => ∫ x, ‖F k x‖) := summable_norm_opM_term a hsum hφ
  have haeF : ∀ᵐ x, Summable (fun k => F k x) :=
    (ae_summable_norm_of_summable_integral_norm hF_int hF_sum).mono fun x hx => hx.of_norm
  have hG_int : ∀ k, Integrable (G k) := fun k => integrable_exp_mul (hF_int k) w
  have hG_sum : Summable (fun k => ∫ x, ‖G k x‖) := by
    have heq : (fun k => ∫ x, ‖G k x‖) = fun k => ∫ x, ‖F k x‖ := by
      ext k
      congr 1 with x
      dsimp [G, e]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [heq]
    exact hF_sum
  have htsum_G_int : Integrable (fun x => ∑' k, G k x) :=
    integrable_tsum_of_summable_norm hG_int hG_sum
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  have hcongr : (fun x : ℝ => e x * opM a φ x) =ᵐ[volume] fun x : ℝ => e x * φ x + ∑' k, G k x := by
    filter_upwards [haeF] with x hx
    dsimp [opM, F, G, e]
    rw [mul_add, hx.tsum_mul_left (e x)]
  rw [integral_congr_ae hcongr, integral_add (integrable_exp_mul hφ w) htsum_G_int]
  have hint_tsum : ∫ x, ∑' k, G k x = ∑' k, ∫ x, G k x :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hG_int hG_sum).symm
  rw [hint_tsum]
  have hterm : (fun k => ∫ x, G k x) = fun k => Erdos967.summand (2 * Real.pi * w) (a k) * 𝓕 φ w := by
    ext k; exact fourier_opM_term ha ha₀ φ w k
  rw [hterm, (summable_summand ha ha₀ hsum (2 * Real.pi * w)).tsum_mul_right]
  have hF0 : ∫ x : ℝ, e x * φ x = 𝓕 φ w := by
    dsimp [e]
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
  rw [hF0]
  dsimp [Ψ]
  ring

private lemma continuous_opM (a : ℕ → ℕ) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    {φ : ℝ → ℂ} (hφ : Continuous φ) {B : ℝ} (hB : ∀ x : ℝ, ‖φ x‖ ≤ B) :
    Continuous (opM a φ) := by
  refine hφ.add (continuous_tsum ?_ (hsum.mul_right B) ?_)
  · intro k
    exact continuous_const.mul (hφ.comp (continuous_id.sub continuous_const))
  · intro k x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

private lemma norm_fourier_le_integral_norm {f : ℝ → ℂ} (w : ℝ) :
    ‖𝓕 f w‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc ‖∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) • f x‖
      ≤ ∫ x : ℝ, ‖Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) • f x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f x‖ := by
        congr 1 with x
        rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

private lemma norm_trapPre_le (w₀ δ x : ℝ) (hδ : 0 < δ) : ‖trapPre w₀ δ x‖ ≤ 5 * δ := by
  have h1 : ‖tentPre w₀ δ x‖ ≤ δ := by
    rw [norm_tentPre w₀ δ x hδ]
    exact mul_le_of_le_one_right hδ.le (fejerReal_le_one _)
  have h2 : ‖tentPre w₀ (2 * δ) x‖ ≤ 2 * δ := by
    rw [norm_tentPre w₀ (2 * δ) x (by linarith)]
    exact mul_le_of_le_one_right (by linarith) (fejerReal_le_one _)
  dsimp [trapPre]
  calc ‖2 * tentPre w₀ (2 * δ) x - tentPre w₀ δ x‖
      ≤ ‖2 * tentPre w₀ (2 * δ) x‖ + ‖tentPre w₀ δ x‖ := norm_sub_le _ _
    _ = 2 * ‖tentPre w₀ (2 * δ) x‖ + ‖tentPre w₀ δ x‖ := by rw [norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (2 * δ) + δ := by linarith
    _ = 5 * δ := by ring

private noncomputable def shiftErr (a : ℕ → ℕ) (w₀ δ : ℝ) (x : ℝ) : ℂ :=
  Ψ a w₀ * trapPre w₀ δ x - opM a (trapPre w₀ δ) x

private lemma shiftErr_eq_tsum {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) {w₀ δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    shiftErr a w₀ δ x = ∑' k : ℕ, ((1 / (a k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ))) := by
  let A : ℕ → ℂ := fun k => Erdos967.summand (2 * Real.pi * w₀) (a k) * trapPre w₀ δ x
  let B : ℕ → ℂ := fun k => ((1 / (a k : ℝ) : ℝ) : ℂ) * trapPre w₀ δ (x - Real.log (a k : ℝ))
  have hA : Summable A := (summable_summand ha ha₀ hsum (2 * Real.pi * w₀)).mul_right _
  have hB : Summable B := by
    refine Summable.of_norm_bounded (g := fun k => (1 / (a k : ℝ)) * (5 * δ)) (hsum.mul_right _) ?_
    intro k
    dsimp [B]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_trapPre_le w₀ δ _ hδ) (by positivity)
  have hterm : ∀ k : ℕ, A k - B k = ((1 / (a k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ))) := by
    intro k
    dsimp [A, B]
    rw [summand_eq (2 * Real.pi * w₀) (a_pos ha ha₀ k)]
    ring
  dsimp [shiftErr, Ψ, opM]
  rw [add_mul, one_mul, ← (summable_summand ha ha₀ hsum (2 * Real.pi * w₀)).tsum_mul_right]
  have hsub : (trapPre w₀ δ x + ∑' k, A k) - (trapPre w₀ δ x + ∑' k, B k) =
      ∑' k, A k - ∑' k, B k := by ring
  rw [hsub, ← hA.tsum_sub hB]
  simp_rw [hterm]

private lemma integrable_shiftErr_term (a : ℕ → ℕ) {w₀ δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    Integrable (fun x : ℝ => ((1 / (a k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ)))) :=
  (((integrable_trapPre w₀ δ hδ).const_mul _).sub
    ((integrable_trapPre w₀ δ hδ).comp_sub_right _)).const_mul _

private lemma integral_norm_shiftErr_term (a : ℕ → ℕ) {w₀ δ : ℝ} (_hδ : 0 < δ) (k : ℕ) :
    ∫ x : ℝ, ‖((1 / (a k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ)))‖ =
      (1 / (a k : ℝ)) * ∫ x : ℝ,
        ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - Real.log (a k : ℝ))‖ := by
  have hfun : (fun x : ℝ => ‖((1 / (a k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ)))‖) =
      fun x : ℝ => (1 / (a k : ℝ)) *
        ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - Real.log (a k : ℝ))‖ := by
    ext x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hfun, integral_const_mul]

private lemma integral_norm_shiftErr_term_le (a : ℕ → ℕ) {w₀ δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∫ x : ℝ, ‖((1 / (a k : ℝ) : ℝ) : ℂ) *
      (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ)))‖ ≤ (1 / (a k : ℝ)) * 6 := by
  rw [integral_norm_shiftErr_term a hδ k]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hi1 : Integrable (fun x : ℝ => ‖trapPre w₀ δ x‖) := (integrable_trapPre w₀ δ hδ).norm
  have hi2 : Integrable (fun x : ℝ => ‖trapPre w₀ δ (x - Real.log (a k : ℝ))‖) :=
    ((integrable_trapPre w₀ δ hδ).comp_sub_right _).norm
  have hi_lhs : Integrable (fun x : ℝ =>
      ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
        trapPre w₀ δ (x - Real.log (a k : ℝ))‖) :=
    (((integrable_trapPre w₀ δ hδ).const_mul _).sub
      ((integrable_trapPre w₀ δ hδ).comp_sub_right _)).norm
  calc ∫ x : ℝ,
        ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - Real.log (a k : ℝ))‖
      ≤ ∫ x : ℝ, (‖trapPre w₀ δ x‖ + ‖trapPre w₀ δ (x - Real.log (a k : ℝ))‖) := by
          refine integral_mono hi_lhs (hi1.add hi2) fun x => ?_
          calc ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
                trapPre w₀ δ (x - Real.log (a k : ℝ))‖
              ≤ ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x‖ +
                  ‖trapPre w₀ δ (x - Real.log (a k : ℝ))‖ := norm_sub_le _ _
            _ = ‖trapPre w₀ δ x‖ + ‖trapPre w₀ δ (x - Real.log (a k : ℝ))‖ := by
                  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ = (∫ x : ℝ, ‖trapPre w₀ δ x‖) + ∫ x : ℝ, ‖trapPre w₀ δ (x - Real.log (a k : ℝ))‖ :=
          integral_add hi1 hi2
    _ = (∫ x : ℝ, ‖trapPre w₀ δ x‖) + ∫ x : ℝ, ‖trapPre w₀ δ x‖ := by
          rw [MeasureTheory.integral_sub_right_eq_self (fun x => ‖trapPre w₀ δ x‖) _]
    _ ≤ 3 + 3 := add_le_add (integral_norm_trapPre_le w₀ δ hδ) (integral_norm_trapPre_le w₀ δ hδ)
    _ = 6 := by norm_num

private lemma summable_tail_tendsto_zero {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun N : ℕ => ∑' k : ℕ, f (k + N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, f k) atTop (𝓝 (∑' k : ℕ, f k)) :=
    hf.hasSum.tendsto_sum_nat
  have h2 : (fun N : ℕ => ∑' k : ℕ, f (k + N)) =
      fun N : ℕ => (∑' k : ℕ, f k) - ∑ k ∈ Finset.range N, f k := by
    ext N
    have hsplit : ∑ k ∈ Finset.range N, f k + ∑' k : ℕ, f (k + N) = ∑' k : ℕ, f k :=
      hf.sum_add_tsum_nat_add N
    linarith
  rw [h2]
  simpa [sub_self] using (tendsto_const_nhds (x := ∑' k : ℕ, f k)).sub h1

private lemma tendsto_integral_norm_shiftErr {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) (w₀ : ℝ) :
    Tendsto (fun δ : ℝ => ∫ x : ℝ, ‖shiftErr a w₀ δ x‖) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htail_lim : Tendsto (fun N : ℕ => (∑' k : ℕ, 1 / (a (k + N) : ℝ)) * 6) atTop (𝓝 0) := by
    simpa using (summable_tail_tendsto_zero hsum).mul_const (6 : ℝ)
  have htail_ev : ∀ᶠ N : ℕ in atTop, (∑' k : ℕ, 1 / (a (k + N) : ℝ)) * 6 < ε / 2 :=
    (Metric.tendsto_nhds.mp htail_lim (ε / 2) (by linarith)).mono fun N hN => by
      have hnn : 0 ≤ (∑' k : ℕ, 1 / (a (k + N) : ℝ)) * 6 :=
        mul_nonneg (tsum_nonneg fun k => by positivity) (by norm_num)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hN
      exact hN
  rcases eventually_atTop.mp htail_ev with ⟨N, hN⟩
  have htail_bound : (∑' k : ℕ, 1 / (a (k + N) : ℝ)) * 6 < ε / 2 := hN N le_rfl
  have hhead : ∀ k ∈ Finset.range N, ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (1 / (a k : ℝ)) * ∫ x : ℝ,
        ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - Real.log (a k : ℝ))‖ < ε / (2 * (N + 1 : ℝ)) := by
    intro k _
    have ht := (tendsto_trapPre_shift w₀ (Real.log (a k : ℝ))).const_mul (1 / (a k : ℝ))
    simp only [mul_zero] at ht
    exact (Metric.tendsto_nhds.mp ht (ε / (2 * (N + 1 : ℝ))) (by positivity)).mono fun δ hδ => by
      have hnn : 0 ≤ (1 / (a k : ℝ)) * ∫ x : ℝ,
          ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
            trapPre w₀ δ (x - Real.log (a k : ℝ))‖ :=
        mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hδ
      exact hδ
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ k ∈ Finset.range N,
      (1 / (a k : ℝ)) * ∫ x : ℝ,
        ‖Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
          trapPre w₀ δ (x - Real.log (a k : ℝ))‖ < ε / (2 * (N + 1 : ℝ)) :=
    (Finset.eventually_all (Finset.range N)).mpr hhead
  filter_upwards [self_mem_nhdsWithin, hall] with δ hδ_pos hδ_head
  have hδ_gt : 0 < δ := hδ_pos
  have hnn : 0 ≤ ∫ x : ℝ, ‖shiftErr a w₀ δ x‖ := integral_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  let D : ℕ → ℝ → ℂ := fun k x => ((1 / (a k : ℝ) : ℝ) : ℂ) *
    (Complex.exp ((-(2 * Real.pi * w₀ * Real.log (a k : ℝ)) : ℝ) * Complex.I) * trapPre w₀ δ x -
      trapPre w₀ δ (x - Real.log (a k : ℝ)))
  have hD_int : ∀ k, Integrable (D k) := fun k => integrable_shiftErr_term a hδ_gt k
  have hD_sum : Summable (fun k => ∫ x : ℝ, ‖D k x‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun k => integral_norm_shiftErr_term_le a hδ_gt k) (hsum.mul_right 6)
  have hle_tsum : ∫ x : ℝ, ‖shiftErr a w₀ δ x‖ ≤ ∑' k, ∫ x : ℝ, ‖D k x‖ := by
    have hfun : (fun x : ℝ => ‖shiftErr a w₀ δ x‖) = fun x : ℝ => ‖∑' k, D k x‖ := by
      ext x; rw [shiftErr_eq_tsum ha ha₀ hsum hδ_gt x]
    rw [hfun]
    exact integral_norm_tsum_le hD_int hD_sum
  have hsplit := hD_sum.sum_add_tsum_nat_add N
  have hhead_sum : ∑ k ∈ Finset.range N, ∫ x : ℝ, ‖D k x‖ ≤
      ∑ k ∈ Finset.range N, (ε / (2 * (N + 1 : ℝ))) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [integral_norm_shiftErr_term a hδ_gt k]
    exact (hδ_head k hk).le
  have hhead_lt : ∑ k ∈ Finset.range N, (ε / (2 * (N + 1 : ℝ))) < ε / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2N : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
    rw [← mul_div_assoc, div_lt_div_iff₀ h2N (by norm_num)]
    nlinarith
  have htail_le : ∑' k : ℕ, ∫ x : ℝ, ‖D (k + N) x‖ ≤ (∑' k : ℕ, 1 / (a (k + N) : ℝ)) * 6 := by
    rw [← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun k => integral_norm_shiftErr_term_le a hδ_gt (k + N)) ?_ ?_
    · exact (hD_sum.comp_injective (add_left_injective N))
    · exact ((hsum.comp_injective (add_left_injective N)).mul_right 6)
  linarith

private lemma local_inverse {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) (hΨ : ∀ w : ℝ, Ψ a w ≠ 0) (w₀ : ℝ) :
    ∃ δ > 0, ∃ ψ : ℝ → ℂ, Integrable ψ ∧
      ∀ w ∈ Set.Icc (w₀ - δ) (w₀ + δ), 𝓕 ψ w * Ψ a w = 1 := by
  have hΨ0 : Ψ a w₀ ≠ 0 := hΨ w₀
  have hnorm_pos : 0 < ‖Ψ a w₀‖ := norm_pos_iff.mpr hΨ0
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∫ x : ℝ, ‖shiftErr a w₀ δ x‖ ≤ ‖Ψ a w₀‖ / 2 := by
    have ht := Metric.tendsto_nhds.mp (tendsto_integral_norm_shiftErr ha ha₀ hsum w₀)
      (‖Ψ a w₀‖ / 2) (by positivity)
    exact ht.mono fun δ hδ => by
      have hnn : 0 ≤ ∫ x : ℝ, ‖shiftErr a w₀ δ x‖ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hδ
      exact hδ.le
  rcases (hev.and self_mem_nhdsWithin).exists with ⟨δ, hδ_err, hδ_pos⟩
  have hδ : 0 < δ := hδ_pos
  let c₀ : ℂ := (Ψ a w₀)⁻¹
  let ρ : ℝ → ℂ := fun x => c₀ * shiftErr a w₀ δ x
  have hρ_eq : ρ = fun x => trapPre w₀ δ x - c₀ * opM a (trapPre w₀ δ) x := by
    ext x
    dsimp [ρ, shiftErr]
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hΨ0, one_mul]
  have hρ_int : Integrable ρ := by
    rw [hρ_eq]
    exact (integrable_trapPre w₀ δ hδ).sub ((integrable_opM a hsum (integrable_trapPre w₀ δ hδ)).const_mul c₀)
  have hρ_norm : ∫ x : ℝ, ‖ρ x‖ ≤ 1 / 2 := by
    have hfun : (fun x : ℝ => ‖ρ x‖) = fun x => ‖c₀‖ * ‖shiftErr a w₀ δ x‖ := by
      ext x; dsimp [ρ]; exact norm_mul _ _
    rw [hfun, integral_const_mul]
    have hc₀ : ‖c₀‖ = ‖Ψ a w₀‖⁻¹ := norm_inv (Ψ a w₀)
    rw [hc₀]
    calc ‖Ψ a w₀‖⁻¹ * ∫ x : ℝ, ‖shiftErr a w₀ δ x‖
        ≤ ‖Ψ a w₀‖⁻¹ * (‖Ψ a w₀‖ / 2) := mul_le_mul_of_nonneg_left hδ_err (by positivity)
      _ = 1 / 2 := by field_simp [hnorm_pos.ne']
  have hFρ_norm : ∀ w : ℝ, ‖𝓕 ρ w‖ ≤ 1 / 2 := fun w =>
    (norm_fourier_le_integral_norm w).trans hρ_norm
  have hFρ_val : ∀ w : ℝ, 𝓕 ρ w = (trap w₀ δ w : ℂ) * (1 - c₀ * Ψ a w) := by
    intro w
    rw [hρ_eq, fourier_sub (integrable_trapPre w₀ δ hδ)
      ((integrable_opM a hsum (integrable_trapPre w₀ δ hδ)).const_mul c₀) w,
      fourier_const_mul, fourier_opM ha ha₀ hsum (integrable_trapPre w₀ δ hδ) w,
      fourier_trapPre w₀ δ w hδ]
    ring
  let u : ℕ → ℝ → ℂ := Nat.rec (trapPre w₀ δ) fun _ prev => conv prev ρ
  have hu_int : ∀ m : ℕ, Integrable (u m) := by
    intro m
    induction m with
    | zero => exact integrable_trapPre w₀ δ hδ
    | succ m ih => exact integrable_conv ih hρ_int
  have hu_norm : ∀ m : ℕ, ∫ x : ℝ, ‖u m x‖ ≤ 3 * (1 / 2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => dsimp [u]; simpa using integral_norm_trapPre_le w₀ δ hδ
    | succ m ih =>
        calc ∫ x : ℝ, ‖u (m + 1) x‖
            ≤ (∫ x : ℝ, ‖u m x‖) * (∫ x : ℝ, ‖ρ x‖) := integral_norm_conv_le (hu_int m) hρ_int
          _ ≤ (3 * (1 / 2 : ℝ) ^ m) * (1 / 2) :=
                mul_le_mul ih hρ_norm (integral_nonneg fun _ => norm_nonneg _) (by positivity)
          _ = 3 * (1 / 2 : ℝ) ^ (m + 1) := by ring
  have hu_F : ∀ m : ℕ, ∀ w : ℝ, 𝓕 (u m) w = (trap w₀ δ w : ℂ) * (𝓕 ρ w) ^ m := by
    intro m
    induction m with
    | zero =>
        intro w
        dsimp [u]
        simpa using fourier_trapPre w₀ δ w hδ
    | succ m ih =>
        intro w
        calc 𝓕 (u (m + 1)) w = 𝓕 (u m) w * 𝓕 ρ w := fourier_conv (hu_int m) hρ_int w
          _ = ((trap w₀ δ w : ℂ) * (𝓕 ρ w) ^ m) * 𝓕 ρ w := by rw [ih w]
          _ = (trap w₀ δ w : ℂ) * (𝓕 ρ w) ^ (m + 1) := by ring
  have hu_sum : Summable (fun m : ℕ => ∫ x : ℝ, ‖u m x‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hu_norm
      (summable_geometric_two.mul_left 3)
  let ψ : ℝ → ℂ := fun x => c₀ * ∑' m : ℕ, u m x
  refine ⟨δ, hδ, ψ, (integrable_tsum_of_summable_norm hu_int hu_sum).const_mul c₀, ?_⟩
  intro w hw
  have hFψ : 𝓕 ψ w = c₀ * ∑' m : ℕ, 𝓕 (u m) w := by
    dsimp [ψ]
    rw [fourier_const_mul]
    congr 1
    let e : ℝ → ℂ := fun x => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)
    let G : ℕ → ℝ → ℂ := fun m x => e x * u m x
    have hae : ∀ᵐ x, Summable (fun m => u m x) :=
      (ae_summable_norm_of_summable_integral_norm hu_int hu_sum).mono fun x hx => hx.of_norm
    have hG_int : ∀ m, Integrable (G m) := fun m => integrable_exp_mul (hu_int m) w
    have hG_sum : Summable (fun m => ∫ x, ‖G m x‖) := by
      have heq : (fun m => ∫ x, ‖G m x‖) = fun m => ∫ x, ‖u m x‖ := by
        ext m; congr 1 with x; dsimp [G, e]; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [heq]; exact hu_sum
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
    have hcongr : (fun x : ℝ => e x * ∑' m, u m x) =ᵐ[volume] fun x : ℝ => ∑' m, G m x :=
      hae.mono fun x hx => (hx.tsum_mul_left (e x)).symm
    rw [integral_congr_ae hcongr, ← MeasureTheory.integral_tsum_of_summable_integral_norm hG_int hG_sum]
    congr 1 with m
    dsimp [G, e]
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
  have htrap1 : trap w₀ δ w = 1 := trap_eq_one_of_mem_Icc hδ hw
  have hFρ_eq : 𝓕 ρ w = 1 - c₀ * Ψ a w := by rw [hFρ_val w, htrap1, Complex.ofReal_one, one_mul]
  have hFρ_lt : ‖1 - c₀ * Ψ a w‖ < 1 := by
    rw [← hFρ_eq]
    linarith [hFρ_norm w]
  have hgeom : ∑' m : ℕ, 𝓕 (u m) w = (c₀ * Ψ a w)⁻¹ := by
    have hfun : (fun m : ℕ => 𝓕 (u m) w) = fun m => (1 - c₀ * Ψ a w) ^ m := by
      ext m
      rw [hu_F m w, htrap1, Complex.ofReal_one, one_mul, hFρ_eq]
    rw [hfun, tsum_geometric_of_norm_lt_one hFρ_lt]
    ring_nf
  rw [hFψ, hgeom]
  dsimp [c₀]
  field_simp [hΨ0, hΨ w]

private lemma sum_tent_partition {h : ℝ} (hh : 0 < h) (N : ℕ) (hN : 0 < N) {w : ℝ}
    (hw : w ∈ Set.Icc (-(N : ℝ) * h) ((N : ℝ) * h)) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, tent ((j : ℝ) * h) h w = 1 := by
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let u : ℝ := w / h
  have hterm : ∀ j : ℤ, tent ((j : ℝ) * h) h w = max 0 (1 - |u - (j : ℝ)|) := by
    intro j
    dsimp [tent, unitTent, u]
    congr 2
    have hdiv : (w - (j : ℝ) * h) / h = w / h - (j : ℝ) := by field_simp [hh.ne']
    rw [hdiv]
  simp_rw [hterm]
  have hu_ge : -(N : ℝ) ≤ u := by
    dsimp [u]; rw [le_div_iff₀ hh]; linarith [hw.1]
  have hu_le : u ≤ (N : ℝ) := by
    dsimp [u]; rw [div_le_iff₀ hh]; linarith [hw.2]
  by_cases hu_top : u = (N : ℝ)
  · rw [hu_top]
    have hN_mem : (N : ℤ) ∈ s := by dsimp [s]; rw [Finset.mem_Icc]; omega
    rw [Finset.sum_eq_single (N : ℤ)]
    · simp
    · intro j hj_s hj
      rw [Finset.mem_Icc] at hj_s
      have hj_le : (j : ℝ) ≤ (N : ℝ) - 1 := by exact_mod_cast (by omega : j ≤ (N : ℤ) - 1)
      have habs : 1 ≤ |(N : ℝ) - (j : ℝ)| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      exact max_eq_left (by linarith)
    · intro habs; exact absurd hN_mem habs
  · have hu_lt : u < (N : ℝ) := lt_of_le_of_ne hu_le hu_top
    let k : ℤ := ⌊u⌋
    have hk_ge : -(N : ℤ) ≤ k := Int.le_floor.mpr (by exact_mod_cast hu_ge)
    have hk_lt_N : k < (N : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hu_lt)
    have hk_mem : k ∈ s := by dsimp [s]; rw [Finset.mem_Icc]; omega
    have hk1_mem : k + 1 ∈ s := by dsimp [s]; rw [Finset.mem_Icc]; omega
    have hku : (k : ℝ) ≤ u := Int.floor_le u
    have huk1 : u < (k : ℝ) + 1 := Int.lt_floor_add_one u
    have hzero : ∀ j ∈ s, j ≠ k → j ≠ k + 1 → max (0 : ℝ) (1 - |u - (j : ℝ)|) = 0 := by
      intro j _ hjk hjk1
      have hcases : j ≤ k - 1 ∨ k + 2 ≤ j := by omega
      rcases hcases with hj_lo | hj_hi
      · have hjr : (j : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast hj_lo
        have habs : 1 ≤ |u - (j : ℝ)| := by rw [abs_of_nonneg (by linarith)]; linarith
        exact max_eq_left (by linarith)
      · have hjr : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hj_hi
        have habs : 1 ≤ |u - (j : ℝ)| := by rw [abs_of_neg (by linarith)]; linarith
        exact max_eq_left (by linarith)
    have hsplit : ∑ j ∈ s, max (0 : ℝ) (1 - |u - (j : ℝ)|) =
        max 0 (1 - |u - (k : ℝ)|) + max 0 (1 - |u - ((k + 1 : ℤ) : ℝ)|) := by
      have hk1_er : k + 1 ∈ s.erase k := Finset.mem_erase.mpr ⟨by omega, hk1_mem⟩
      rw [← Finset.add_sum_erase s (fun j : ℤ => max (0 : ℝ) (1 - |u - (j : ℝ)|)) hk_mem,
        ← Finset.add_sum_erase (s.erase k) (fun j : ℤ => max (0 : ℝ) (1 - |u - (j : ℝ)|)) hk1_er,
        Finset.sum_eq_zero (fun j hj => ?_), add_zero]
      have hj1 : j ≠ k + 1 := (Finset.mem_erase.mp hj).1
      have hjk : j ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hjs : j ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2
      exact hzero j hjs hjk hj1
    rw [hsplit]
    have hfk : max (0 : ℝ) (1 - |u - (k : ℝ)|) = 1 - (u - (k : ℝ)) := by
      rw [abs_of_nonneg (by linarith)]
      exact max_eq_right (by linarith)
    have hfk1 : max (0 : ℝ) (1 - |u - ((k + 1 : ℤ) : ℝ)|) = u - (k : ℝ) := by
      push_cast
      rw [abs_of_neg (by linarith)]
      have heq : 1 - -(u - ((k : ℝ) + 1)) = u - (k : ℝ) := by ring
      rw [heq]
      exact max_eq_right (by linarith)
    rw [hfk, hfk1]
    ring

private lemma norm_conv_le_bound_mul_integral {f g : ℝ → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ t : ℝ, ‖f t‖ ≤ B) (hg : Integrable g) (x : ℝ) :
    ‖conv f g x‖ ≤ B * ∫ y : ℝ, ‖g y‖ := by
  dsimp [conv]
  rw [MeasureTheory.convolution_def]
  have hint : Integrable (fun y : ℝ => B * ‖g (x - y)‖) := (hg.comp_sub_left x).norm.const_mul B
  have hf_meas : AEStronglyMeasurable (fun y : ℝ => (ContinuousLinearMap.mul ℂ ℂ) (f y) (g (x - y))) :=
    hf.aestronglyMeasurable.mul (hg.comp_sub_left x).aestronglyMeasurable
  have hnorm_int : Integrable (fun y : ℝ => ‖(ContinuousLinearMap.mul ℂ ℂ) (f y) (g (x - y))‖) := by
    refine hint.mono' hf_meas.norm ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (norm_nonneg _), ContinuousLinearMap.mul_apply', norm_mul]
    exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
  calc ‖∫ y : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (f y) (g (x - y))‖
      ≤ ∫ y : ℝ, ‖(ContinuousLinearMap.mul ℂ ℂ) (f y) (g (x - y))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, B * ‖g (x - y)‖ := by
        refine integral_mono hnorm_int hint fun y => ?_
        rw [ContinuousLinearMap.mul_apply', norm_mul]
        exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
    _ = B * ∫ y : ℝ, ‖g (x - y)‖ := integral_const_mul _ _
    _ = B * ∫ y : ℝ, ‖g y‖ := by
        rw [MeasureTheory.integral_sub_left_eq_self (fun y => ‖g y‖) volume x]

private lemma global_fejer_preimage {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) (hΨ : ∀ w : ℝ, Ψ a w ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    ∃ ψ : ℝ → ℂ, Integrable ψ ∧ Continuous ψ ∧ (∃ B : ℝ, ∀ x : ℝ, ‖ψ x‖ ≤ B) ∧
      ∀ x : ℝ, opM a ψ x = ((R * fejerReal (R * x) : ℝ) : ℂ) := by
  classical
  have hloc : ∀ w₀ : ℝ, ∃ δ > 0, ∃ ψ : ℝ → ℂ, Integrable ψ ∧
      ∀ w ∈ Set.Icc (w₀ - δ) (w₀ + δ), 𝓕 ψ w * Ψ a w = 1 :=
    fun w₀ => local_inverse ha ha₀ hsum hΨ w₀
  let δfun : ℝ → ℝ := fun w₀ => (hloc w₀).choose
  have hδ_pos : ∀ w₀ : ℝ, 0 < δfun w₀ := fun w₀ => (hloc w₀).choose_spec.1
  let ψfun : ℝ → ℝ → ℂ := fun w₀ => (hloc w₀).choose_spec.2.choose
  have hψ_int : ∀ w₀ : ℝ, Integrable (ψfun w₀) :=
    fun w₀ => (hloc w₀).choose_spec.2.choose_spec.1
  have hψ_inv : ∀ w₀ : ℝ, ∀ w ∈ Set.Icc (w₀ - δfun w₀) (w₀ + δfun w₀),
      𝓕 (ψfun w₀) w * Ψ a w = 1 :=
    fun w₀ => (hloc w₀).choose_spec.2.choose_spec.2
  have hopen : ∀ w₀ : ℝ, IsOpen (Metric.ball w₀ (δfun w₀)) := fun _ => Metric.isOpen_ball
  have hcov : Set.Icc (-R) R ⊆ ⋃ w₀ : ℝ, Metric.ball w₀ (δfun w₀) :=
    fun w _ => Set.mem_iUnion.mpr ⟨w, Metric.mem_ball_self (hδ_pos w)⟩
  rcases lebesgue_number_lemma_of_metric isCompact_Icc hopen hcov with ⟨r₀, hr₀_pos, hr₀⟩
  rcases exists_nat_gt (2 * R / r₀) with ⟨N₀, hN₀⟩
  let N : ℕ := N₀ + 1
  have hN_pos : 0 < N := Nat.succ_pos N₀
  have hN_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  let h : ℝ := R / (N : ℝ)
  have hh_pos : 0 < h := div_pos hR hN_real
  have hh_lt : h < r₀ := by
    have hgt : 2 * R / r₀ < (N : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast Nat.le_succ N₀)
    have h1 : 2 * R < (N : ℝ) * r₀ := (div_lt_iff₀ hr₀_pos).mp hgt
    have h2 : R / (N : ℝ) < r₀ / 2 := by
      rw [div_lt_div_iff₀ hN_real (by norm_num)]
      linarith
    dsimp [h]
    linarith
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hj_mem : ∀ j ∈ s, (j : ℝ) * h ∈ Set.Icc (-R) R := by
    intro j hj
    dsimp [s] at hj
    rw [Finset.mem_Icc] at hj
    have hlo : -(N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hhi : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj.2
    have hNh : (N : ℝ) * h = R := mul_div_cancel₀ R hN_real.ne'
    constructor <;> nlinarith
  let c : ℤ → ℝ := fun j => if hj : j ∈ s then (hr₀ _ (hj_mem j hj)).choose else 0
  have hc_sub : ∀ j (hj : j ∈ s), Metric.ball ((j : ℝ) * h) r₀ ⊆ Metric.ball (c j) (δfun (c j)) := by
    intro j hj
    dsimp [c]
    rw [dif_pos hj]
    exact (hr₀ _ (hj_mem j hj)).choose_spec
  have hj_inv : ∀ j ∈ s, ∀ w : ℝ,
      (tent ((j : ℝ) * h) h w : ℂ) * (𝓕 (ψfun (c j)) w * Ψ a w) =
        (tent ((j : ℝ) * h) h w : ℂ) := by
    intro j hj w
    by_cases hlt : |(w - (j : ℝ) * h) / h| < 1
    · have hdist : dist w ((j : ℝ) * h) < r₀ := by
        rw [Real.dist_eq]
        rw [abs_div, abs_of_pos hh_pos] at hlt
        have habs : |w - (j : ℝ) * h| < h := (div_lt_one hh_pos).mp hlt
        exact habs.trans hh_lt
      have hball : w ∈ Metric.ball (c j) (δfun (c j)) := hc_sub j hj hdist
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hball
      have hw_icc : w ∈ Set.Icc (c j - δfun (c j)) (c j + δfun (c j)) :=
        ⟨by linarith [hball.1], by linarith [hball.2]⟩
      rw [hψ_inv (c j) w hw_icc, mul_one]
    · have hle : 1 ≤ |(w - (j : ℝ) * h) / h| := not_lt.mp hlt
      have hzero : tent ((j : ℝ) * h) h w = 0 := unitTent_eq_zero_of_one_le hle
      rw [hzero, Complex.ofReal_zero, zero_mul]
  let θ : ℝ → ℂ := fun x => ∑ j ∈ s, conv (tentPre ((j : ℝ) * h) h) (ψfun (c j)) x
  have hθ_int : Integrable θ := integrable_finsetSum s fun j _ =>
    integrable_conv (integrable_tentPre _ h hh_pos) (hψ_int (c j))
  have hθ_F : ∀ w : ℝ, 𝓕 θ w * Ψ a w = ∑ j ∈ s, (tent ((j : ℝ) * h) h w : ℂ) := by
    intro w
    dsimp [θ]
    rw [fourier_finset_sum s (fun j => conv (tentPre ((j : ℝ) * h) h) (ψfun (c j)))
      (fun j _ => integrable_conv (integrable_tentPre _ h hh_pos) (hψ_int (c j))) w,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [fourier_conv (integrable_tentPre _ h hh_pos) (hψ_int (c j)) w,
      fourier_tentPre ((j : ℝ) * h) h w hh_pos, mul_assoc, hj_inv j hj w]
  have hθ_one : ∀ w ∈ Set.Icc (-R) R, 𝓕 θ w * Ψ a w = 1 := by
    intro w hw
    rw [hθ_F w]
    have hNh : (N : ℝ) * h = R := mul_div_cancel₀ R hN_real.ne'
    have hw' : w ∈ Set.Icc (-(N : ℝ) * h) ((N : ℝ) * h) := by
      have : -(N : ℝ) * h = -R := by linarith [hNh]
      rw [this, hNh]
      exact hw
    have hsum1 := sum_tent_partition hh_pos N hN_pos hw'
    rw [← Complex.ofReal_one, ← hsum1, Complex.ofReal_sum]
  let ψ : ℝ → ℂ := conv (tentPre 0 R) θ
  have hψ_int' : Integrable ψ := integrable_conv (integrable_tentPre 0 R hR) hθ_int
  have htent_bound : ∀ t : ℝ, ‖tentPre 0 R t‖ ≤ R := by
    intro t
    rw [norm_tentPre 0 R t hR]
    exact mul_le_of_le_one_right hR.le (fejerReal_le_one _)
  have hbdd : BddAbove (Set.range fun t : ℝ => ‖tentPre 0 R t‖) :=
    ⟨R, fun _ ⟨t, ht⟩ => ht ▸ htent_bound t⟩
  have hψ_cont : Continuous ψ :=
    hbdd.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
      (continuous_tentPre 0 R) hθ_int
  have hψ_bnd : ∀ x : ℝ, ‖ψ x‖ ≤ R * ∫ y : ℝ, ‖θ y‖ := fun x =>
    norm_conv_le_bound_mul_integral (continuous_tentPre 0 R) htent_bound hθ_int x
  have hM_eq : ∀ w : ℝ, 𝓕 (fun x => opM a ψ x - tentPre 0 R x) w = 0 := by
    intro w
    rw [fourier_sub (integrable_opM a hsum hψ_int') (integrable_tentPre 0 R hR) w,
      fourier_opM ha ha₀ hsum hψ_int' w]
    change (𝓕 (conv (tentPre 0 R) θ) w) * Ψ a w - 𝓕 (tentPre 0 R) w = 0
    rw [fourier_conv (integrable_tentPre 0 R hR) hθ_int w, fourier_tentPre 0 R w hR, mul_assoc]
    by_cases hw : w ∈ Set.Icc (-R) R
    · rw [hθ_one w hw, mul_one, sub_self]
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hw
      have habs : 1 ≤ |(w - 0) / R| := by
        rw [sub_zero, abs_div, abs_of_pos hR, one_le_div hR]
        rcases hw with hlt | hgt
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hzero : tent 0 R w = 0 := unitTent_eq_zero_of_one_le habs
      rw [hzero, Complex.ofReal_zero, zero_mul, sub_self]
  let d : ℝ → ℂ := fun x => opM a ψ x - tentPre 0 R x
  have hd_cont : Continuous d :=
    (continuous_opM a hsum hψ_cont hψ_bnd).sub (continuous_tentPre 0 R)
  have hd_int : Integrable d :=
    (integrable_opM a hsum hψ_int').sub (integrable_tentPre 0 R hR)
  have hd_F : 𝓕 d = 0 := funext hM_eq
  have hd_inv : 𝓕⁻ (𝓕 d) = d :=
    hd_cont.fourierInv_fourier_eq hd_int (by rw [hd_F]; exact integrable_zero _ _ _)
  refine ⟨ψ, hψ_int', hψ_cont, ⟨R * ∫ y : ℝ, ‖θ y‖, hψ_bnd⟩, ?_⟩
  intro x
  have hdx : d x = 0 := by
    rw [← congrFun hd_inv x, hd_F, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    simp
  have hmx : opM a ψ x = tentPre 0 R x := sub_eq_zero.mp hdx
  rw [hmx]
  dsimp [tentPre]
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]

/- ## Step 5: Tail bound, Tauberian forward direction, and final equivalence -/

private lemma integral_Ioi_fejerReal_le {B : ℝ} (hB : 0 < B) :
    ∫ y in Set.Ioi B, fejerReal y ≤ 1 / (Real.pi ^ 2 * B) := by
  have hint_rpow : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi B) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hB
  have hint_const : IntegrableOn (fun y : ℝ => (1 / Real.pi ^ 2) * y ^ (-2 : ℝ)) (Set.Ioi B) :=
    hint_rpow.const_mul _
  have hint_fejer : IntegrableOn fejerReal (Set.Ioi B) :=
    integrable_fejerReal.integrableOn
  have hmono : ∫ y in Set.Ioi B, fejerReal y ≤
      ∫ y in Set.Ioi B, (1 / Real.pi ^ 2) * y ^ (-2 : ℝ) := by
    refine setIntegral_mono_on hint_fejer hint_const measurableSet_Ioi fun y hy => ?_
    have hy_pos : 0 < y := hB.trans hy
    have hle := fejerReal_le_inv_sq hy_pos.ne'
    have heq : 1 / (Real.pi * y) ^ 2 = (1 / Real.pi ^ 2) * y ^ (-2 : ℝ) := by
      rw [mul_pow, show y ^ (-2 : ℝ) = (y ^ 2)⁻¹ from by norm_cast]
      ring
    linarith
  have hval : ∫ y in Set.Ioi B, (1 / Real.pi ^ 2) * y ^ (-2 : ℝ) = 1 / (Real.pi ^ 2 * B) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hB]
    have h1 : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [h1, Real.rpow_neg_one]
    ring
  linarith

private lemma integral_Iio_fejerReal_eq {B : ℝ} :
    ∫ y in Set.Iio (-B), fejerReal y = ∫ y in Set.Ioi B, fejerReal y := by
  have h1 : ∫ y in Set.Iio (-B), fejerReal y =
      ∫ y : ℝ, (Set.Iio (-B)).indicator fejerReal y :=
    (integral_indicator measurableSet_Iio).symm
  have h2 : ∫ y in Set.Ioi B, fejerReal y =
      ∫ y : ℝ, (Set.Ioi B).indicator fejerReal y :=
    (integral_indicator measurableSet_Ioi).symm
  have h3 : (fun y : ℝ => (Set.Iio (-B)).indicator fejerReal y) =
      fun y : ℝ => (Set.Ioi B).indicator fejerReal (-y) := by
    ext y
    by_cases hy : y ∈ Set.Iio (-B)
    · have hny : -y ∈ Set.Ioi B := by rw [Set.mem_Ioi]; rw [Set.mem_Iio] at hy; linarith
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hny, fejerReal_even]
    · have hny : -y ∉ Set.Ioi B := by rw [Set.mem_Ioi]; rw [Set.mem_Iio] at hy; linarith
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hny]
  rw [h1, h3, integral_neg_eq_self, ← h2]

private lemma fejer_tail_bound {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) ≤ 2 / (Real.pi ^ 2 * (R * δ)) := by
  let B : ℝ := R * δ
  have hB : 0 < B := mul_pos hR hδ
  have heq_set : (Set.Icc (-δ) δ)ᶜ = Set.Iio (-δ) ∪ Set.Ioi δ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hscaled : ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) =
      ∫ z in (Set.Icc (-B) B)ᶜ, fejerReal z := by
    have h1 : ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) =
        ∫ y : ℝ, (Set.Icc (-δ) δ)ᶜ.indicator (fun y => R * fejerReal (R * y)) y :=
      (integral_indicator measurableSet_Icc.compl).symm
    have h2 : ∫ z in (Set.Icc (-B) B)ᶜ, fejerReal z =
        ∫ z : ℝ, (Set.Icc (-B) B)ᶜ.indicator fejerReal z :=
      (integral_indicator measurableSet_Icc.compl).symm
    have hfun : (fun y : ℝ => (Set.Icc (-δ) δ)ᶜ.indicator (fun y => R * fejerReal (R * y)) y) =
        fun y : ℝ => R * ((Set.Icc (-B) B)ᶜ.indicator fejerReal (R * y)) := by
      ext y
      by_cases hy : y ∈ (Set.Icc (-δ) δ)ᶜ
      · have hRy : R * y ∈ (Set.Icc (-B) B)ᶜ := by
          simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hy ⊢
          rcases hy with h | h
          · left; dsimp [B]; nlinarith
          · right; dsimp [B]; nlinarith
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hRy]
      · have hRy : R * y ∉ (Set.Icc (-B) B)ᶜ := by
          simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_or, not_lt] at hy ⊢
          exact ⟨by dsimp [B]; nlinarith [hy.1], by dsimp [B]; nlinarith [hy.2]⟩
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hRy, mul_zero]
    rw [h1, hfun, integral_const_mul,
      MeasureTheory.Measure.integral_comp_mul_left ((Set.Icc (-B) B)ᶜ.indicator fejerReal) R,
      smul_eq_mul, abs_of_pos (inv_pos.mpr hR), ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, ← h2]
  rw [hscaled]
  have heqB : (Set.Icc (-B) B)ᶜ = Set.Iio (-B) ∪ Set.Ioi B := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-B)) (Set.Ioi B) :=
    Set.disjoint_left.mpr fun z hz1 hz2 => by rw [Set.mem_Iio] at hz1; rw [Set.mem_Ioi] at hz2; linarith
  rw [heqB, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    integrable_fejerReal.integrableOn integrable_fejerReal.integrableOn,
    integral_Iio_fejerReal_eq, ← two_mul]
  calc 2 * ∫ y in Set.Ioi B, fejerReal y
      ≤ 2 * (1 / (Real.pi ^ 2 * B)) :=
        mul_le_mul_of_nonneg_left (integral_Ioi_fejerReal_le hB) (by norm_num)
    _ = 2 / (Real.pi ^ 2 * (R * δ)) := by dsimp [B]; ring

private lemma fejer_rescale_integral {R : ℝ} (hR : 0 < R) :
    ∫ y : ℝ, R * fejerReal (R * y) = 1 := by
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left fejerReal R, smul_eq_mul,
    abs_of_pos (inv_pos.mpr hR), ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, integral_fejerReal]

private lemma integrable_fejer_rescale {R : ℝ} (hR : 0 < R) :
    Integrable (fun y : ℝ => R * fejerReal (R * y)) :=
  (integrable_fejerReal.comp_mul_left' hR.ne').const_mul R

private lemma integrable_tsum_H_aux {a : ℕ → ℕ}
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    {φ : ℝ → ℂ} (hφ : Integrable φ) {h : ℝ → ℝ} (hm_h : Measurable h)
    {M : ℝ} (hM : ∀ u : ℝ, |h u| ≤ M) (u : ℝ) :
    Integrable (fun y : ℝ => φ y * (h (u - y) : ℂ)) ∧
      (∀ k : ℕ, Integrable (fun y : ℝ =>
        ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ)) * (h (u - y) : ℂ))) ∧
      Summable (fun k : ℕ => ∫ y : ℝ,
        ‖((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ)) * (h (u - y) : ℂ)‖) := by
  have hM_nn : 0 ≤ M := (abs_nonneg (h 0)).trans (hM 0)
  have hm_hc : Measurable (fun y : ℝ => (h (u - y) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (hm_h.comp (continuous_const.sub continuous_id).measurable)
  have h0 : Integrable (fun y : ℝ => φ y * (h (u - y) : ℂ)) := by
    refine (hφ.norm.mul_const M).mono' (hφ.aestronglyMeasurable.mul hm_hc.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  have hk_int : ∀ k : ℕ, Integrable (fun y : ℝ =>
      ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ)) * (h (u - y) : ℂ)) := by
    intro k
    have hbase := (hφ.comp_sub_right (Real.log (a k : ℝ))).const_mul ((1 / (a k : ℝ) : ℝ) : ℂ)
    refine (hbase.norm.mul_const M).mono'
      (hbase.aestronglyMeasurable.mul hm_hc.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM _)
      (norm_nonneg _)
  have hk_sum : Summable (fun k : ℕ => ∫ y : ℝ,
      ‖((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ)) * (h (u - y) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
      (hsum.mul_right (M * ∫ y : ℝ, ‖φ y‖))
    intro k
    have hint_rhs : Integrable (fun y : ℝ => (1 / (a k : ℝ)) * M * ‖φ (y - Real.log (a k : ℝ))‖) :=
      ((hφ.comp_sub_right (Real.log (a k : ℝ))).norm).const_mul _
    calc ∫ y : ℝ, ‖((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ)) * (h (u - y) : ℂ)‖
        ≤ ∫ y : ℝ, (1 / (a k : ℝ)) * M * ‖φ (y - Real.log (a k : ℝ))‖ := by
          refine integral_mono (hk_int k).norm hint_rhs fun y => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            Real.norm_eq_abs]
          calc (1 / (a k : ℝ)) * ‖φ (y - Real.log (a k : ℝ))‖ * |h (u - y)|
              ≤ (1 / (a k : ℝ)) * ‖φ (y - Real.log (a k : ℝ))‖ * M :=
                mul_le_mul_of_nonneg_left (hM _) (mul_nonneg (by positivity) (norm_nonneg _))
            _ = (1 / (a k : ℝ)) * M * ‖φ (y - Real.log (a k : ℝ))‖ := by ring
      _ = (1 / (a k : ℝ)) * M * ∫ y : ℝ, ‖φ (y - Real.log (a k : ℝ))‖ := integral_const_mul _ _
      _ = (1 / (a k : ℝ)) * (M * ∫ y : ℝ, ‖φ y‖) := by
          rw [MeasureTheory.integral_sub_right_eq_self (fun y => ‖φ y‖) _, mul_assoc]
  exact ⟨h0, hk_int, hk_sum⟩

private lemma integral_opM_mul_h_eq {a : ℕ → ℕ}
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    {φ : ℝ → ℂ} (hφ : Integrable φ) {B : ℝ} (hB : ∀ x : ℝ, ‖φ x‖ ≤ B)
    {h : ℝ → ℝ} (hm_h : Measurable h) {M : ℝ} (hM : ∀ u : ℝ, |h u| ≤ M) (u : ℝ) :
    ∫ y : ℝ, opM a φ y * (h (u - y) : ℂ) =
      ∫ z : ℝ, φ z * ((h (u - z) + ∑' k : ℕ, (1 / (a k : ℝ)) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ) := by
  rcases integrable_tsum_H_aux hsum hφ hm_h hM u with ⟨h0, hk_int, hk_sum⟩
  let F : ℕ → ℝ → ℂ := fun k y =>
    ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ)) * (h (u - y) : ℂ)
  have hF_int : ∀ k, Integrable (F k) := hk_int
  have hF_sum : Summable (fun k => ∫ y, ‖F k y‖) := hk_sum
  have hsum_phi : ∀ y : ℝ, Summable (fun k : ℕ => ((1 / (a k : ℝ) : ℝ) : ℂ) * φ (y - Real.log (a k : ℝ))) := by
    intro y
    refine Summable.of_norm_bounded (g := fun k => (1 / (a k : ℝ)) * B) (hsum.mul_right B) ?_
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
  have hsplit_lhs : (fun y : ℝ => opM a φ y * (h (u - y) : ℂ)) =
      fun y : ℝ => φ y * (h (u - y) : ℂ) + ∑' k : ℕ, F k y := by
    ext y
    dsimp [opM, F]
    rw [add_mul, (hsum_phi y).tsum_mul_right]
  rw [hsplit_lhs, integral_add h0 (integrable_tsum_of_summable_norm hF_int hF_sum),
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum]
  let U : ℕ → ℝ → ℂ := fun k z => φ z * (((1 / (a k : ℝ) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ))
  have hterm_eq : ∀ k : ℕ, ∫ y : ℝ, F k y = ∫ z : ℝ, U k z := by
    intro k
    let l : ℝ := Real.log (a k : ℝ)
    have hfun : (fun y : ℝ => F k y) = fun y : ℝ => U k (y - l) := by
      ext y
      dsimp [F, U, l]
      push_cast
      have : u - (y - Real.log (a k : ℝ)) - Real.log (a k : ℝ) = u - y := by ring
      rw [this]
      ring
    rw [hfun, MeasureTheory.integral_sub_right_eq_self (U k) l]
  simp_rw [hterm_eq]
  have hU_int : ∀ k : ℕ, Integrable (U k) := by
    intro k
    have hm : Measurable (fun z : ℝ => (((1 / (a k : ℝ) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.measurable.comp
        (measurable_const.mul (hm_h.comp ((continuous_const.sub continuous_id).sub continuous_const).measurable))
    refine ((hφ.norm.mul_const ((1 / (a k : ℝ)) * M)).mono'
      (hφ.aestronglyMeasurable.mul hm.aestronglyMeasurable) ?_)
    filter_upwards with z
    dsimp [U]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hM _) (by positivity)) (norm_nonneg _)
  have hU_sum : Summable (fun k : ℕ => ∫ z : ℝ, ‖U k z‖) := by
    have heq : (fun k : ℕ => ∫ z : ℝ, ‖U k z‖) = fun k => ∫ y : ℝ, ‖F k y‖ := by
      ext k
      have hsub : (fun y : ℝ => ‖F k y‖) = fun y : ℝ => ‖U k (y - Real.log (a k : ℝ))‖ := by
        ext y
        dsimp [F, U]
        congr 1
        push_cast
        have : u - (y - Real.log (a k : ℝ)) - Real.log (a k : ℝ) = u - y := by ring
        rw [this]
        ring
      rw [hsub, MeasureTheory.integral_sub_right_eq_self (fun z => ‖U k z‖) _]
    rw [heq]
    exact hk_sum
  have hU_rhs_int : Integrable (fun z : ℝ => ∑' k : ℕ, U k z) :=
    integrable_tsum_of_summable_norm hU_int hU_sum
  have hpointwise : ∀ z : ℝ, φ z * (h (u - z) : ℂ) + ∑' k : ℕ, U k z =
      φ z * ((h (u - z) + ∑' k : ℕ, (1 / (a k : ℝ)) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ) := by
    intro z
    have hsum_real : Summable (fun k : ℕ => (1 / (a k : ℝ)) * h (u - z - Real.log (a k : ℝ))) := by
      refine Summable.of_norm_bounded (g := fun k => (1 / (a k : ℝ)) * M) (hsum.mul_right M) ?_
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
    have hhas : HasSum (fun k : ℕ => (((1 / (a k : ℝ) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ)))
        (((∑' k : ℕ, (1 / (a k : ℝ)) * h (u - z - Real.log (a k : ℝ))) : ℝ) : ℂ) :=
      hsum_real.hasSum.map Complex.ofRealHom Complex.continuous_ofReal
    have hsum_c : Summable (fun k : ℕ => (((1 / (a k : ℝ) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ))) :=
      hhas.summable
    have htsum_ofReal : (∑' k : ℕ, (((1 / (a k : ℝ) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ))) =
        (((∑' k : ℕ, (1 / (a k : ℝ)) * h (u - z - Real.log (a k : ℝ))) : ℝ) : ℂ) :=
      hhas.tsum_eq
    dsimp [U]
    rw [hsum_c.tsum_mul_left (φ z), htsum_ofReal, Complex.ofReal_add, mul_add]
  have h1 : (∫ y : ℝ, φ y * (h (u - y) : ℂ)) + ∑' k : ℕ, ∫ z : ℝ, U k z =
      (∫ z : ℝ, φ z * (h (u - z) : ℂ)) + ∫ z : ℝ, ∑' k : ℕ, U k z :=
    congrArg ((∫ z : ℝ, φ z * (h (u - z) : ℂ)) + ·)
      (MeasureTheory.integral_tsum_of_summable_integral_norm hU_int hU_sum)
  have h2 : (∫ z : ℝ, φ z * (h (u - z) : ℂ)) + ∫ z : ℝ, ∑' k : ℕ, U k z =
      ∫ z : ℝ, (φ z * (h (u - z) : ℂ) + ∑' k : ℕ, U k z) :=
    (integral_add h0 hU_rhs_int).symm
  have h3 : ∫ z : ℝ, (φ z * (h (u - z) : ℂ) + ∑' k : ℕ, U k z) =
      ∫ z : ℝ, φ z * ((h (u - z) + ∑' k : ℕ, (1 / (a k : ℝ)) * h (u - z - Real.log (a k : ℝ)) : ℝ) : ℂ) := by
    simp_rw [hpointwise]
  exact h1.trans (h2.trans h3)

private lemma tauberian_mp (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ)))
    (hΨ_t : ∀ t : ℝ, 1 + (∑' k, Erdos967.summand t (a k)) ≠ 0) :
    ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
      (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
      Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
        (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
      Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1) := by
  intro f hf_mono hf_nonneg hf_zero _hf_bdd hlim
  have hΨ : ∀ w : ℝ, Ψ a w ≠ 0 := fun w => hΨ_t (2 * Real.pi * w)
  let S : ℝ := 1 + ∑' k : ℕ, 1 / (a k : ℝ)
  have hS_pos : 1 ≤ S := by
    have hts : 0 ≤ ∑' k : ℕ, 1 / (a k : ℝ) := tsum_nonneg fun k => by positivity
    dsimp [S]
    linarith
  let g : ℝ → ℝ := fun u => Real.exp (-u) * f (Real.exp u)
  let h : ℝ → ℝ := fun u => g u - 1
  let H : ℝ → ℝ := fun u => h u + ∑' k : ℕ, (1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))
  have hg_nonneg : ∀ u : ℝ, 0 ≤ g u := fun u => mul_nonneg (Real.exp_pos (-u)).le (hf_nonneg _)
  have hm_g : Measurable g :=
    (Real.continuous_exp.comp continuous_neg).measurable.mul
      (hf_mono.measurable.comp Real.continuous_exp.measurable)
  have hm_h : Measurable h := hm_g.sub measurable_const
  have hm_H : Measurable H := by
    refine hm_h.add (Measurable.tsum fun k => ?_)
    exact measurable_const.mul (hm_h.comp (continuous_id.sub continuous_const).measurable)
  have hg_slow : ∀ v w : ℝ, v ≤ w → g v ≤ Real.exp (w - v) * g w := by
    intro v w hvw
    have hexp_le : Real.exp v ≤ Real.exp w := Real.exp_le_exp.mpr hvw
    have hf_le : f (Real.exp v) ≤ f (Real.exp w) := hf_mono hexp_le
    dsimp [g]
    have heq : Real.exp (-v) = Real.exp (w - v) * Real.exp (-w) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf_le (Real.exp_pos (-w)).le)
      (Real.exp_pos (w - v)).le
  have hbound : ∃ M : ℝ, 1 ≤ M ∧ (∀ u : ℝ, g u ≤ M) ∧ (∀ u : ℝ, |h u| ≤ M) := by
    have hev : ∀ᶠ x : ℝ in atTop, (f x + ∑' k, f (x / (a k : ℝ))) / x ≤ S + 1 := by
      have ht := Metric.tendsto_nhds.mp hlim 1 zero_lt_one
      exact ht.mono fun x hx => by
        rw [Real.dist_eq, abs_lt] at hx
        dsimp [S]
        linarith [hx.2]
    rcases eventually_atTop.mp hev with ⟨X₁, hX₁⟩
    let X₀ : ℝ := max 1 X₁
    have hX₀_ge1 : 1 ≤ X₀ := le_max_left _ _
    let M : ℝ := max 1 (max (S + 1) (f X₀))
    have hM_ge1 : 1 ≤ M := le_max_left _ _
    have hg_le : ∀ u : ℝ, g u ≤ M := by
      intro u
      let x : ℝ := Real.exp u
      have hx_pos : 0 < x := Real.exp_pos u
      have hgx : g u = f x / x := by
        dsimp [g, x]; rw [Real.exp_neg, inv_mul_eq_div]
      rw [hgx]
      by_cases hx1 : x < 1
      · rw [hf_zero x hx1, zero_div]
        linarith
      · have hx_ge1 : 1 ≤ x := not_lt.mp hx1
        by_cases hx0 : X₀ ≤ x
        · have htsum_nn : 0 ≤ ∑' k : ℕ, f (x / (a k : ℝ)) := tsum_nonneg fun k => hf_nonneg _
          have h1 : f x / x ≤ (f x + ∑' k, f (x / (a k : ℝ))) / x :=
            div_le_div_of_nonneg_right (by linarith) hx_pos.le
          have h2 := hX₁ x ((le_max_right 1 X₁).trans hx0)
          have h3 : S + 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
          linarith
        · have hx_lt0 : x ≤ X₀ := (not_le.mp hx0).le
          have h1 : f x / x ≤ f X₀ / 1 := by
            have hfx : f x ≤ f X₀ := hf_mono hx_lt0
            calc f x / x ≤ f X₀ / x := div_le_div_of_nonneg_right hfx hx_pos.le
              _ ≤ f X₀ / 1 := div_le_div_of_nonneg_left (hf_nonneg X₀) zero_lt_one hx_ge1
          have h2 : f X₀ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
          linarith
    refine ⟨M, hM_ge1, hg_le, fun u => ?_⟩
    dsimp [h]
    rw [abs_le]
    constructor <;> linarith [hg_nonneg u, hg_le u]
  rcases hbound with ⟨M, hM_ge1, hg_le_M, hh_abs_M⟩
  have hH_eq : ∀ u : ℝ, H u = (f (Real.exp u) + ∑' k, f (Real.exp u / (a k : ℝ))) / Real.exp u - S := by
    intro u
    let x : ℝ := Real.exp u
    have hx_pos : 0 < x := Real.exp_pos u
    have hterm_eq : ∀ k : ℕ, (1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ)) =
        f (x / (a k : ℝ)) / x - 1 / (a k : ℝ) := by
      intro k
      have hak_pos : (0 : ℝ) < a k := Nat.cast_pos.mpr (a_pos ha ha₀ k)
      have hexp_sub : Real.exp (u - Real.log (a k : ℝ)) = x / (a k : ℝ) := by
        rw [Real.exp_sub, Real.exp_log hak_pos]
      have hg_sub : g (u - Real.log (a k : ℝ)) = ((a k : ℝ) / x) * f (x / (a k : ℝ)) := by
        dsimp [g]
        rw [hexp_sub, Real.exp_neg, hexp_sub, inv_div]
      dsimp [h]
      rw [hg_sub]
      field_simp [hak_pos.ne', hx_pos.ne']
    have hsum_f : Summable (fun k : ℕ => f (x / (a k : ℝ)) / x) := by
      refine Summable.of_nonneg_of_le (fun k => div_nonneg (hf_nonneg _) hx_pos.le) ?_
        (hsum.mul_right M)
      intro k
      have hak_pos : (0 : ℝ) < a k := Nat.cast_pos.mpr (a_pos ha ha₀ k)
      have hexp_sub : Real.exp (u - Real.log (a k : ℝ)) = x / (a k : ℝ) := by
        rw [Real.exp_sub, Real.exp_log hak_pos]
      have hg_sub : g (u - Real.log (a k : ℝ)) = ((a k : ℝ) / x) * f (x / (a k : ℝ)) := by
        dsimp [g]
        rw [hexp_sub, Real.exp_neg, hexp_sub, inv_div]
      have hle := hg_le_M (u - Real.log (a k : ℝ))
      rw [hg_sub] at hle
      calc f (x / (a k : ℝ)) / x
          = (1 / (a k : ℝ)) * (((a k : ℝ) / x) * f (x / (a k : ℝ))) := by
            field_simp [hak_pos.ne', hx_pos.ne']
        _ ≤ (1 / (a k : ℝ)) * M := mul_le_mul_of_nonneg_left hle (by positivity)
    have hsum_raw : Summable (fun k : ℕ => f (x / (a k : ℝ))) := by
      have hm := hsum_f.mul_left x
      refine hm.congr fun k => ?_
      field_simp [hx_pos.ne']
    have hdiv_sum : ∑' k : ℕ, f (x / (a k : ℝ)) / x = (∑' k : ℕ, f (x / (a k : ℝ))) / x := by
      have heq : (fun k : ℕ => f (x / (a k : ℝ)) / x) = fun k => f (x / (a k : ℝ)) * x⁻¹ := by
        ext k; exact div_eq_mul_inv _ _
      rw [heq, hsum_raw.tsum_mul_right x⁻¹, div_eq_mul_inv]
    have hx_g : h u = f x / x - 1 := by
      dsimp [h, g, x]; rw [Real.exp_neg, inv_mul_eq_div]
    dsimp [H]
    simp_rw [hterm_eq]
    rw [hsum_f.tsum_sub hsum, hx_g, hdiv_sum]
    dsimp [S]
    ring
  have hH_tendsto : Tendsto H atTop (𝓝 0) := by
    have hcomp : Tendsto (fun u : ℝ => (f (Real.exp u) + ∑' k, f (Real.exp u / (a k : ℝ))) / Real.exp u)
        atTop (𝓝 S) := hlim.comp Real.tendsto_exp_atTop
    have heq : H = fun u : ℝ =>
        (f (Real.exp u) + ∑' k, f (Real.exp u / (a k : ℝ))) / Real.exp u - S := funext hH_eq
    rw [heq]
    simpa [sub_self] using hcomp.sub_const S
  have hH_bound : ∀ u : ℝ, |H u| ≤ M * S := by
    intro u
    have hsum_norm : Summable (fun k : ℕ => ‖(1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hsum.mul_right M)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hh_abs_M _) (by positivity)
    have htsum_le : |∑' k : ℕ, (1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))| ≤
        (∑' k : ℕ, 1 / (a k : ℝ)) * M := by
      calc |∑' k : ℕ, (1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))|
          = ‖∑' k : ℕ, (1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' k : ℕ, ‖(1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))‖ :=
              norm_tsum_le_tsum_norm hsum_norm
        _ ≤ ∑' k : ℕ, (1 / (a k : ℝ)) * M := by
              refine hsum_norm.tsum_le_tsum (fun k => ?_) (hsum.mul_right M)
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
              exact mul_le_mul_of_nonneg_left (hh_abs_M _) (by positivity)
        _ = (∑' k : ℕ, 1 / (a k : ℝ)) * M := hsum.tsum_mul_right M
    calc |H u| ≤ |h u| + |∑' k : ℕ, (1 / (a k : ℝ)) * h (u - Real.log (a k : ℝ))| := abs_add_le _ _
      _ ≤ M + (∑' k : ℕ, 1 / (a k : ℝ)) * M := add_le_add (hh_abs_M u) htsum_le
      _ = M * S := by dsimp [S]; ring
  have hconv : ∀ R : ℝ, 0 < R →
      Tendsto (fun u : ℝ => ∫ y : ℝ, (R * fejerReal (R * y)) * h (u - y)) atTop (𝓝 0) := by
    intro R hR
    rcases global_fejer_preimage ha ha₀ hsum hΨ hR with ⟨ψ, hψ_int, hψ_cont, ⟨B, hB⟩, hψ_opM⟩
    have hI_eq : ∀ u : ℝ,
        ((∫ y : ℝ, (R * fejerReal (R * y)) * h (u - y) : ℝ) : ℂ) =
          ∫ z : ℝ, ψ z * (H (u - z) : ℂ) := by
      intro u
      have hofR : ((∫ y : ℝ, (R * fejerReal (R * y)) * h (u - y) : ℝ) : ℂ) =
          ∫ y : ℝ, (((R * fejerReal (R * y)) * h (u - y) : ℝ) : ℂ) :=
        integral_ofReal.symm
      rw [hofR]
      have hfun : (fun y : ℝ => (((R * fejerReal (R * y)) * h (u - y) : ℝ) : ℂ)) =
          fun y : ℝ => opM a ψ y * (h (u - y) : ℂ) := by
        ext y
        rw [Complex.ofReal_mul, ← hψ_opM y]
      rw [hfun]
      exact integral_opM_mul_h_eq hsum hψ_int hB hm_h hh_abs_M u
    have hF_meas : ∀ u : ℝ, AEStronglyMeasurable (fun z : ℝ => ψ z * (H (u - z) : ℂ)) := by
      intro u
      have hmHc : Measurable (fun z : ℝ => (H (u - z) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp (hm_H.comp (continuous_const.sub continuous_id).measurable)
      exact hψ_cont.aestronglyMeasurable.mul hmHc.aestronglyMeasurable
    have h_bound : ∀ u : ℝ, ∀ᵐ z : ℝ, ‖ψ z * (H (u - z) : ℂ)‖ ≤ ‖ψ z‖ * (M * S) := by
      intro u
      filter_upwards with z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hH_bound (u - z)) (norm_nonneg _)
    have h_lim : ∀ᵐ z : ℝ, Tendsto (fun u : ℝ => ψ z * (H (u - z) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      filter_upwards with z
      have hHu : Tendsto (fun u : ℝ => H (u - z)) atTop (𝓝 0) :=
        hH_tendsto.comp (tendsto_atTop_add_const_right _ (-z) tendsto_id)
      have hHcu : Tendsto (fun u : ℝ => (H (u - z) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
        rw [← Complex.ofReal_zero]
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp hHu
      simpa only [mul_zero] using tendsto_const_nhds.mul hHcu
    have hdct : Tendsto (fun u : ℝ => ∫ z : ℝ, ψ z * (H (u - z) : ℂ)) atTop (𝓝 (∫ _ : ℝ, (0 : ℂ))) :=
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun z => ‖ψ z‖ * (M * S))
        (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
        (hψ_int.norm.mul_const (M * S)) h_lim
    rw [integral_zero] at hdct
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hdct
    simp only [Complex.zero_re] at hre
    refine hre.congr fun u => ?_
    dsimp only [Function.comp_def]
    rw [← hI_eq u, Complex.ofReal_re]
  have hg_tendsto : Tendsto g atTop (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hexp_pos : ContinuousAt (fun d : ℝ => Real.exp (2 * d) - 1) 0 := by fun_prop
    have hexp_neg : ContinuousAt (fun d : ℝ => 1 - Real.exp (-2 * d)) 0 := by fun_prop
    have hev_δ : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
        Real.exp (2 * d) - 1 < ε / (4 * M) ∧ 1 - Real.exp (-2 * d) < ε / (4 * M) := by
      filter_upwards [Metric.tendsto_nhds.mp (hexp_pos.tendsto.mono_left nhdsWithin_le_nhds)
          (ε / (4 * M)) (by positivity),
        Metric.tendsto_nhds.mp (hexp_neg.tendsto.mono_left nhdsWithin_le_nhds)
          (ε / (4 * M)) (by positivity)] with d hd1 hd2
      simp only [mul_zero, Real.exp_zero, sub_self, Real.dist_eq, sub_zero] at hd1 hd2
      exact ⟨(abs_lt.mp hd1).2, (abs_lt.mp hd2).2⟩
    rcases (hev_δ.and self_mem_nhdsWithin).exists with ⟨δ, ⟨hδ_exp1, hδ_exp2⟩, hδ_pos⟩
    have hδ : 0 < δ := hδ_pos
    let K : ℝ := min (1 / 2) (ε / (8 * (M + 1)))
    have hK_pos : 0 < K := lt_min (by norm_num) (by positivity)
    have hK_le1 : K ≤ 1 / 2 := min_le_left _ _
    have hK_le2 : K ≤ ε / (8 * (M + 1)) := min_le_right _ _
    let R : ℝ := 4 / (Real.pi ^ 2 * δ * K)
    have hR : 0 < R := by positivity
    let τ : ℝ := ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y))
    have hτ_nn : 0 ≤ τ := setIntegral_nonneg measurableSet_Icc.compl fun y _ =>
      mul_nonneg hR.le (fejerReal_nonneg _)
    have hτ_le : τ ≤ 2 / (Real.pi ^ 2 * (R * δ)) := fejer_tail_bound hR hδ
    have hR_val : 2 / (Real.pi ^ 2 * (R * δ)) = K / 2 := by
      dsimp [R]
      field_simp [Real.pi_ne_zero, hδ.ne', hK_pos.ne']
      ring
    have hτ_lt_half : τ < 1 / 2 := by linarith
    have hτ_lt_eps : τ < ε / (8 * (M + 1)) := by linarith
    have hMτ : M * τ < ε / 8 := by
      calc M * τ ≤ (M + 1) * τ := by nlinarith
        _ < (M + 1) * (ε / (8 * (M + 1))) := mul_lt_mul_of_pos_left hτ_lt_eps (by linarith)
        _ = ε / 8 := by field_simp [show (M : ℝ) + 1 ≠ 0 by linarith]
    have hint_in : ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) = 1 - τ := by
      have hadd := MeasureTheory.integral_add_compl (measurableSet_Icc (a := -δ) (b := δ))
        (integrable_fejer_rescale hR)
      rw [fejer_rescale_integral hR] at hadd
      dsimp [τ]
      linarith
    have hint_fh : ∀ v : ℝ, Integrable (fun y : ℝ => (R * fejerReal (R * y)) * h (v - y)) := by
      intro v
      have hm_hv : Measurable (fun y : ℝ => h (v - y)) :=
        hm_h.comp (continuous_const.sub continuous_id).measurable
      refine ((integrable_fejer_rescale hR).norm.mul_const M).mono'
        (((continuous_const.mul (continuous_fejerReal.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable).mul hm_hv.aestronglyMeasurable) ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hh_abs_M _) (abs_nonneg _)
    have hev_up : ∀ᶠ u : ℝ in atTop, ∫ y : ℝ, (R * fejerReal (R * y)) * h (u + δ - y) < ε / 8 := by
      have hcu := (hconv R hR).comp (tendsto_atTop_add_const_right _ δ tendsto_id)
      exact (Metric.tendsto_nhds.mp hcu (ε / 8) (by positivity)).mono fun u hu => by
        rw [Real.dist_eq, sub_zero] at hu
        exact (abs_lt.mp hu).2
    have hev_lo : ∀ᶠ u : ℝ in atTop, -(ε / 8) < ∫ y : ℝ, (R * fejerReal (R * y)) * h (u - δ - y) := by
      have hcu := (hconv R hR).comp (tendsto_atTop_add_const_right _ (-δ) tendsto_id)
      exact (Metric.tendsto_nhds.mp hcu (ε / 8) (by positivity)).mono fun u hu => by
        rw [Real.dist_eq, sub_zero] at hu
        exact (abs_lt.mp hu).1
    filter_upwards [hev_up, hev_lo] with u hu_up hu_lo
    have hsplit_up : ∫ y : ℝ, (R * fejerReal (R * y)) * h (u + δ - y) =
        (∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * h (u + δ - y)) +
          ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * h (u + δ - y) :=
      (MeasureTheory.integral_add_compl measurableSet_Icc (hint_fh (u + δ))).symm
    have hin_up : (1 - τ) * (Real.exp (-2 * δ) * g u - 1) ≤
        ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * h (u + δ - y) := by
      have hmono : ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * (Real.exp (-2 * δ) * g u - 1) ≤
          ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * h (u + δ - y) := by
        refine setIntegral_mono_on
          (((integrable_fejer_rescale hR).mul_const _).integrableOn)
          ((hint_fh (u + δ)).integrableOn) measurableSet_Icc fun y hy => ?_
        have hker_nn : 0 ≤ R * fejerReal (R * y) := mul_nonneg hR.le (fejerReal_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ hker_nn
        have hy_le : u ≤ u + δ - y := by linarith [hy.2]
        have hdiff : (u + δ - y) - u ≤ 2 * δ := by linarith [hy.1]
        have hslow := hg_slow u (u + δ - y) hy_le
        have hexp_le : Real.exp ((u + δ - y) - u) ≤ Real.exp (2 * δ) := Real.exp_le_exp.mpr hdiff
        have hgu_le : g u ≤ Real.exp (2 * δ) * g (u + δ - y) :=
          hslow.trans (mul_le_mul_of_nonneg_right hexp_le (hg_nonneg _))
        have hmul := mul_le_mul_of_nonneg_left hgu_le (Real.exp_pos (-2 * δ)).le
        have h1 : Real.exp (-2 * δ) * (Real.exp (2 * δ) * g (u + δ - y)) = g (u + δ - y) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
        rw [h1] at hmul
        dsimp [h]
        linarith
      rw [integral_mul_const, hint_in] at hmono
      exact hmono
    have hout_up : -(M * τ) ≤ ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * h (u + δ - y) := by
      have hmono : ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * (-M) ≤
          ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * h (u + δ - y) := by
        refine setIntegral_mono_on
          (((integrable_fejer_rescale hR).mul_const _).integrableOn)
          ((hint_fh (u + δ)).integrableOn) measurableSet_Icc.compl fun y _ => ?_
        have hker_nn : 0 ≤ R * fejerReal (R * y) := mul_nonneg hR.le (fejerReal_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ hker_nn
        exact (abs_le.mp (hh_abs_M _)).1
      rw [integral_mul_const] at hmono
      dsimp [τ] at hmono ⊢
      linarith
    have hub1 : (1 - τ) * (Real.exp (-2 * δ) * g u - 1) < ε / 4 := by nlinarith
    have hub2 : Real.exp (-2 * δ) * g u - 1 < ε / 2 := by
      have hhalf : (1 / 2 : ℝ) < 1 - τ := by linarith
      nlinarith
    have hub3 : (1 - Real.exp (-2 * δ)) * g u < ε / 4 := by
      have hdiff_nn : 0 ≤ 1 - Real.exp (-2 * δ) := by
        have hle : Real.exp (-2 * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      calc (1 - Real.exp (-2 * δ)) * g u ≤ (1 - Real.exp (-2 * δ)) * M :=
            mul_le_mul_of_nonneg_left (hg_le_M u) hdiff_nn
        _ < (ε / (4 * M)) * M := mul_lt_mul_of_pos_right hδ_exp2 (by linarith)
        _ = ε / 4 := by field_simp [show (M : ℝ) ≠ 0 by linarith]
    have hgu_lt : g u - 1 < ε := by
      have heq : g u - 1 = (Real.exp (-2 * δ) * g u - 1) + (1 - Real.exp (-2 * δ)) * g u := by ring
      linarith
    have hsplit_lo : ∫ y : ℝ, (R * fejerReal (R * y)) * h (u - δ - y) =
        (∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * h (u - δ - y)) +
          ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * h (u - δ - y) :=
      (MeasureTheory.integral_add_compl measurableSet_Icc (hint_fh (u - δ))).symm
    have hin_lo : ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * h (u - δ - y) ≤
        (1 - τ) * (Real.exp (2 * δ) * g u - 1) := by
      have hmono : ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * h (u - δ - y) ≤
          ∫ y in Set.Icc (-δ) δ, (R * fejerReal (R * y)) * (Real.exp (2 * δ) * g u - 1) := by
        refine setIntegral_mono_on
          ((hint_fh (u - δ)).integrableOn)
          (((integrable_fejer_rescale hR).mul_const _).integrableOn) measurableSet_Icc fun y hy => ?_
        have hker_nn : 0 ≤ R * fejerReal (R * y) := mul_nonneg hR.le (fejerReal_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ hker_nn
        have hy_le : u - δ - y ≤ u := by linarith [hy.1]
        have hdiff : u - (u - δ - y) ≤ 2 * δ := by linarith [hy.2]
        have hslow := hg_slow (u - δ - y) u hy_le
        have hexp_le : Real.exp (u - (u - δ - y)) ≤ Real.exp (2 * δ) := Real.exp_le_exp.mpr hdiff
        have hle := hslow.trans (mul_le_mul_of_nonneg_right hexp_le (hg_nonneg u))
        dsimp [h]
        linarith
      rw [integral_mul_const, hint_in] at hmono
      exact hmono
    have hout_lo : ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * h (u - δ - y) ≤ M * τ := by
      have hmono : ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * h (u - δ - y) ≤
          ∫ y in (Set.Icc (-δ) δ)ᶜ, (R * fejerReal (R * y)) * M := by
        refine setIntegral_mono_on
          ((hint_fh (u - δ)).integrableOn)
          (((integrable_fejer_rescale hR).mul_const _).integrableOn) measurableSet_Icc.compl fun y _ => ?_
        have hker_nn : 0 ≤ R * fejerReal (R * y) := mul_nonneg hR.le (fejerReal_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ hker_nn
        exact (abs_le.mp (hh_abs_M _)).2
      rw [integral_mul_const] at hmono
      dsimp [τ] at hmono ⊢
      linarith
    have hlb1 : -(ε / 4) < (1 - τ) * (Real.exp (2 * δ) * g u - 1) := by nlinarith
    have hlb2 : -(ε / 2) < Real.exp (2 * δ) * g u - 1 := by
      have hhalf : (1 / 2 : ℝ) < 1 - τ := by linarith
      nlinarith
    have hlb3 : (Real.exp (2 * δ) - 1) * g u < ε / 4 := by
      have hdiff_nn : 0 ≤ Real.exp (2 * δ) - 1 := by
        have hle : 1 ≤ Real.exp (2 * δ) := Real.one_le_exp (by linarith)
        linarith
      calc (Real.exp (2 * δ) - 1) * g u ≤ (Real.exp (2 * δ) - 1) * M :=
            mul_le_mul_of_nonneg_left (hg_le_M u) hdiff_nn
        _ < (ε / (4 * M)) * M := mul_lt_mul_of_pos_right hδ_exp1 (by linarith)
        _ = ε / 4 := by field_simp [show (M : ℝ) ≠ 0 by linarith]
    have hgu_gt : -ε < g u - 1 := by
      have heq : g u - 1 = (Real.exp (2 * δ) * g u - 1) - (Real.exp (2 * δ) - 1) * g u := by ring
      linarith
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨hgu_gt, hgu_lt⟩
  have hcomp : Tendsto (fun x : ℝ => g (Real.log x)) atTop (𝓝 1) :=
    hg_tendsto.comp Real.tendsto_log_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp [g]
  rw [Real.exp_neg, Real.exp_log hx, inv_mul_eq_div]

private lemma erdos_967_tauberian_proof (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (∀ t : ℝ, 1 + (∑' k, Erdos967.summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1) :=
  ⟨tauberian_mp a ha ha₀ hsum, fun h => tauberian_mpr ha ha₀ hsum h⟩

end OMA.Erdos967

theorem OMA.solution : type_of% @Erdos967.erdos_967.variants.tauberian :=
  OMA.Erdos967.erdos_967_tauberian_proof
