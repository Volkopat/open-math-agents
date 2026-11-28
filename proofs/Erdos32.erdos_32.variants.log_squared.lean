import FormalConjectures.ErdosProblems.«32»


open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

noncomputable section

namespace OMAHoheisel

abbrev Z : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1

theorem Z_diff : Differentiable ℂ Z := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1

theorem Z_eq {s : ℂ} (hs : s ≠ 1) : Z s = (s - 1) * riemannZeta s := by
  simp [Z, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar]

theorem Z_one : Z 1 = 1 := by
  simp [Z, DirichletCharacter.LFunctionTrivChar₁]

def mult (ρ : ℂ) : ℕ := analyticOrderNatAt Z ρ

/-! ### Zeros of `Z` -/

theorem Z_zero_iff {s : ℂ} : Z s = 0 ↔ s ≠ 1 ∧ riemannZeta s = 0 := by
  by_cases hs : s = 1
  · subst hs; simp
  · rw [Z_eq hs]; simp [hs, sub_eq_zero]

theorem Z_re_lt_one {s : ℂ} (h : Z s = 0) : s.re < 1 := by
  by_contra h1
  push Not at h1
  exact riemannZeta_ne_zero_of_one_le_re h1 (Z_zero_iff.1 h).2

theorem Z_order_ne_top (u : ℂ) : analyticOrderAt Z u ≠ ⊤ := by
  have h1 : analyticOrderAt Z 1 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero).2 (Or.inr (by rw [Z_one]; exact one_ne_zero))]
    exact ENat.zero_ne_top
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z _ => Z_diff.analyticAt z) isPreconnected_univ (mem_univ 1) (mem_univ u) h1

theorem Z_zeros_finite {K : Set ℂ} (hK : IsCompact K) : {s : ℂ | Z s = 0 ∧ s ∈ K}.Finite := by
  apply (hK.inter_riemannZetaZeros_finite).subset
  intro s hs
  exact ⟨hs.2, (Z_zero_iff.1 hs.1).2⟩

theorem mult_pos {u : ℂ} (h : Z u = 0) : 0 < mult u := by
  unfold mult
  have h1 : analyticOrderAt Z u ≠ 0 := analyticOrderAt_ne_zero.2 ⟨Z_diff.analyticAt u, h⟩
  have h2 := Z_order_ne_top u
  rw [← Nat.cast_analyticOrderNatAt h2] at h1
  exact Nat.pos_of_ne_zero (by exact_mod_cast h1)

/-! ### Factoring out finitely many zeros -/

theorem div_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) (n : ℕ)
    (hn : analyticOrderAt f a = n) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g a ≠ 0 ∧ ∀ s, f s = (s - a) ^ n * g s := by
  obtain ⟨h, hh, hha, hev⟩ := ((hf.analyticAt a).analyticOrderAt_eq_natCast).1 hn
  refine ⟨fun s => if s = a then h a else f s / (s - a) ^ n, ?_, by simpa using hha, ?_⟩
  · intro s
    by_cases hs : s = a
    · rw [hs]
      have : (fun s => if s = a then h a else f s / (s - a) ^ n) =ᶠ[𝓝 a] h := by
        filter_upwards [hev] with w hw
        by_cases hwa : w = a
        · simp [hwa]
        · simp only [hwa, if_false]
          rw [hw, smul_eq_mul]
          have : (w - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwa)
          field_simp
      exact (hh.differentiableAt).congr_of_eventuallyEq this
    · have : (fun s => if s = a then h a else f s / (s - a) ^ n) =ᶠ[𝓝 s]
          (fun s => f s / (s - a) ^ n) := by
        filter_upwards [isOpen_ne.mem_nhds hs] with w hw
        simp [hw]
      apply DifferentiableAt.congr_of_eventuallyEq _ this
      exact (hf s).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hs))
  · intro s
    by_cases hs : s = a
    · rw [hs]
      have := hev.self_of_nhds
      simpa using this
    · simp only [hs, if_false]
      have : (s - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hs)
      field_simp

theorem order_mul_unit {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a u : ℂ} (hua : u ≠ a) (n : ℕ) :
    analyticOrderAt (fun s => (s - a) ^ n * g s) u = analyticOrderAt g u := by
  have h1 : AnalyticAt ℂ (fun s : ℂ => (s - a) ^ n) u := by fun_prop
  have h2 := analyticOrderAt_mul h1 (hg.analyticAt u)
  have h3 : analyticOrderAt (fun s : ℂ => (s - a) ^ n) u = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (pow_ne_zero _ (sub_ne_zero.2 hua)))
  rw [h3, zero_add] at h2
  exact h2

/-- Factor `f = (∏_{u ∈ F} (s - u)^{ord_u f}) g` with `g` entire and nonzero on `F`. -/
theorem factor (F : Finset ℂ) : ∀ f : ℂ → ℂ, Differentiable ℂ f →
    (∀ u ∈ F, analyticOrderAt f u ≠ ⊤) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ u ∈ F, g u ≠ 0) ∧
      ∀ s, f s = (∏ u ∈ F, (s - u) ^ analyticOrderNatAt f u) * g s := by
  induction F using Finset.induction_on with
  | empty => intro f hf _; exact ⟨f, hf, by simp, by simp⟩
  | insert a F haF ih =>
    intro f hf hfin
    have ha := hfin a (Finset.mem_insert_self a F)
    obtain ⟨g1, hg1, hg1a, hfg1⟩ := div_zero hf a (analyticOrderNatAt f a)
      (Nat.cast_analyticOrderNatAt ha).symm
    have hord : ∀ u ∈ F, analyticOrderAt g1 u = analyticOrderAt f u := by
      intro u hu
      have hua : u ≠ a := fun h => haF (h ▸ hu)
      have : f = fun s => (s - a) ^ analyticOrderNatAt f a * g1 s := funext hfg1
      rw [this, order_mul_unit hg1 hua]
    obtain ⟨g, hg, hgF, hg1g⟩ := ih g1 hg1 (fun u hu => by
      rw [hord u hu]; exact hfin u (Finset.mem_insert_of_mem hu))
    refine ⟨g, hg, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · intro h0
        apply hg1a
        rw [hg1g, h0, mul_zero]
      · exact hgF u hu
    · intro s
      rw [hfg1, hg1g, Finset.prod_insert haF]
      have : ∀ u ∈ F, analyticOrderNatAt g1 u = analyticOrderNatAt f u := by
        intro u hu; unfold analyticOrderNatAt; rw [hord u hu]
      rw [Finset.prod_congr rfl (fun u hu => by rw [this u hu])]
      ring

/-! ### Polynomial growth of `Z` on `Re s ≥ 1/20` -/

/-- Euler–Maclaurin term: `(s-1) n^{-s} + (n+1)^{1-s} - n^{1-s}`. -/
def En (n : ℕ) (s : ℂ) : ℂ :=
  (s - 1) * (n : ℂ) ^ (-s) + ((n : ℂ) + 1) ^ (1 - s) - (n : ℂ) ^ (1 - s)

theorem En_differentiable (n : ℕ) (hn : 0 < n) : Differentiable ℂ (En n) := by
  have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  intro s
  unfold En
  apply DifferentiableAt.sub
  · apply DifferentiableAt.add
    · exact (differentiableAt_id.sub_const 1).mul
        ((differentiableAt_id.neg).const_cpow (Or.inl h1))
    · exact ((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl h2)
  · exact ((differentiableAt_const 1).sub differentiableAt_id).const_cpow (Or.inl h1)

theorem En_bound (n : ℕ) (hn : 0 < n) (s : ℂ) (hs : 0 < s.re) :
    ‖En n s‖ ≤ ‖s - 1‖ * ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hs1 : s = 1
  · subst hs1; simp [En]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have hns : -s ≠ 0 := neg_ne_zero.2 hs0
  -- f u = u^(1-s), f' u = (1-s) u^(-s), f'' u = (1-s)(-s) u^(-s-1)
  set f' : ℝ → ℂ := fun u => (1 - s) * (u : ℂ) ^ (-s) with hf'
  have hderf : ∀ u : ℝ, 0 < u → HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 - s)) (f' u) u := by
    intro u hu
    have := hasDerivAt_ofReal_cpow_const hu.ne' h1s
    simpa [hf', sub_sub, add_comm] using this
  have hderf' : ∀ u : ℝ, 0 < u →
      HasDerivAt f' ((1 - s) * (-s * (u : ℂ) ^ (-s - 1))) u := by
    intro u hu
    exact (hasDerivAt_ofReal_cpow_const hu.ne' hns).const_mul (1 - s)
  have hbd2 : ∀ u ∈ Ico (n : ℝ) (n + 1), ‖(1 - s) * (-s * (u : ℂ) ^ (-s - 1))‖ ≤
      ‖s - 1‖ * ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
    intro u hu
    have hu0 : 0 < u := hn0.trans_le hu.1
    rw [norm_mul, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu0, norm_sub_rev]
    have : u ^ (-s - 1).re ≤ (n : ℝ) ^ (-s.re - 1) := by
      simp only [sub_re, neg_re, one_re]
      exact Real.rpow_le_rpow_of_nonpos hn0 hu.1 (by linarith)
    rw [mul_assoc]
    gcongr
  -- step 1: ‖f' u - f' n‖ ≤ K (u - n)
  set K := ‖s - 1‖ * ‖s‖ * (n : ℝ) ^ (-s.re - 1) with hK
  have step1 : ∀ u ∈ Icc (n : ℝ) (n + 1), ‖f' u - f' n‖ ≤ K * (u - n) := by
    apply norm_image_sub_le_of_norm_deriv_le_segment' _ hbd2
    intro u hu
    exact (hderf' u (hn0.trans_le hu.1)).hasDerivWithinAt
  -- step 2: g u = u^(1-s) - f' n * u
  have step2 := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u : ℝ => (u : ℂ) ^ (1 - s) - f' n * u) (f' := fun u => f' u - f' n) (C := K)
    (a := n) (b := n + 1) (fun u hu => by
      have h := (hderf u (hn0.trans_le hu.1)).sub ((hasDerivAt_id u).ofReal_comp.const_mul (f' n))
      convert h.hasDerivWithinAt using 1
      · funext y; simp
      · simp)
    (fun u hu => (step1 u (Ico_subset_Icc_self hu)).trans (by
      have : u - n ≤ 1 := by linarith [hu.2]
      have hK0 : 0 ≤ K := by positivity
      nlinarith [hu.1]))
    (n + 1) ⟨by linarith, le_refl _⟩
  have e : En n s = ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) - f' n * (((n : ℝ) + 1 : ℝ) : ℂ)) -
      ((((n : ℝ)) : ℂ) ^ (1 - s) - f' n * ((n : ℝ) : ℂ)) := by
    simp only [En, hf']
    push_cast
    ring
  rw [e]
  simpa using step2

theorem summable_shift_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hp)
  simpa using h

/-- The Euler–Maclaurin series. -/
def Sser (s : ℂ) : ℂ := ∑' n : ℕ, En (n + 1) s

theorem En_bound' (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖En (n + 1) s‖ ≤ ‖s - 1‖ * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have := En_bound (n + 1) (Nat.succ_pos n) s hs
  simpa using this

theorem En_summable (s : ℂ) (hs : 0 < s.re) : Summable (fun n : ℕ => ‖En (n + 1) s‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => En_bound' n s hs)
    ((summable_shift_rpow (by linarith : -s.re - 1 < -1)).mul_left _)

theorem En_sum_partial (s : ℂ) (N : ℕ) : ∑ n ∈ Finset.range N, En (n + 1) s =
    (s - 1) * ∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s) + ((N : ℂ) + 1) ^ (1 - s) - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [En]
    push_cast
    ring

theorem Sser_eq (s : ℂ) (hs : 1 < s.re) : Sser s = (s - 1) * riemannZeta s - 1 := by
  have hsum := (En_summable s (by linarith)).of_norm.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have hs' : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
      have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
      simpa using this
    have := hs'.hasSum.tendsto_sum_nat
    simpa [cpow_neg, one_div] using this
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun N : ℕ => ‖((N : ℂ) + 1) ^ (1 - s)‖) = fun N : ℕ => ((N : ℝ) + 1) ^ (1 - s.re) := by
      funext N
      have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp
    rw [this]
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine this.congr (fun N => ?_)
    simp only [Function.comp]
    ring_nf
  have h4 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, En (n + 1) s) atTop
      (𝓝 ((s - 1) * riemannZeta s + 0 - 1)) := by
    simp_rw [En_sum_partial]
    exact ((h2.const_mul _).add h3).sub_const 1
  rw [Sser]
  rw [tendsto_nhds_unique hsum h4]
  ring

theorem Sser_diffOn {a K : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ Sser ({s : ℂ | a < s.re} ∩ ball 0 K) := by
  have hU : IsOpen ({s : ℂ | a < s.re} ∩ ball 0 K) :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ball
  refine differentiableOn_tsum_of_summable_norm
    ((summable_shift_rpow (by linarith : -a - 1 < -1)).mul_left ((K + 1) * K))
    (fun n => (En_differentiable (n + 1) (Nat.succ_pos n)).differentiableOn) hU ?_
  intro n w hw
  have hw1 : a < w.re := hw.1
  have hw2 : ‖w‖ < K := by simpa using hw.2
  refine (En_bound' n w (by linarith)).trans ?_
  have h1 : ‖w - 1‖ ≤ K + 1 := by
    calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ K + 1 := by simp; linarith
  have h2 : ((n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-a - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by linarith)
  have h3 : 0 ≤ ((n : ℝ) + 1) ^ (-w.re - 1) := by positivity
  calc ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) ≤ (K + 1) * K * ((n : ℝ) + 1) ^ (-a - 1) := by
        have hK : 0 < K := lt_of_le_of_lt (norm_nonneg w) hw2
        gcongr

theorem Z_eq_series {s : ℂ} (hs : 0 < s.re) : Z s = 1 + Sser s := by
  set a := min (s.re / 2) 1
  set K := ‖s‖ + 3
  have ha : 0 < a := lt_min (by positivity) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have has : a < s.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set V := {s : ℂ | a < s.re} ∩ ball 0 K
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_re).inter isOpen_ball
  have hVc : IsPreconnected V :=
    ((convex_halfSpace_re_gt a).inter (convex_ball 0 K)).isPreconnected
  have h2V : (2 : ℂ) ∈ V := by
    refine ⟨?_, ?_⟩
    · show a < (2 : ℂ).re
      simp only [re_ofNat]
      linarith
    · simp [K]; linarith [norm_nonneg s]
  have hsV : s ∈ V := ⟨has, by simp [K]⟩
  have hf : AnalyticOnNhd ℂ Z V := fun z _ => Z_diff.analyticAt z
  have hg : AnalyticOnNhd ℂ (fun s => 1 + Sser s) V :=
    ((differentiableOn_const 1).add (Sser_diffOn ha)).analyticOnNhd hV
  have heq : Z =ᶠ[𝓝 (2 : ℂ)] (fun s => 1 + Sser s) := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [this] with w hw
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    rw [Z_eq hw1, Sser_eq w hw]; ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hVc h2V heq hsV

theorem Z_bound : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 20 ≤ s.re → ‖Z s‖ ≤ C * (‖s‖ + 1) ^ 2 := by
  set C0 := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(21 / 20 : ℝ))
  have hC0 : 0 ≤ C0 := tsum_nonneg fun n => by positivity
  refine ⟨C0 + 1, by linarith, fun s hs => ?_⟩
  have hs0 : 0 < s.re := by linarith
  rw [Z_eq_series hs0, Sser]
  have hsum := En_summable s hs0
  have hb : ∑' n : ℕ, ‖En (n + 1) s‖ ≤ ‖s - 1‖ * ‖s‖ * C0 := by
    rw [← tsum_mul_left]
    refine hsum.tsum_le_tsum (fun n => (En_bound' n s hs0).trans ?_)
      ((summable_shift_rpow (by norm_num)).mul_left _)
    gcongr
    · linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · linarith
  have h1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by simp
  calc ‖1 + ∑' n : ℕ, En (n + 1) s‖ ≤ 1 + ‖s - 1‖ * ‖s‖ * C0 := by
        refine (norm_add_le _ _).trans ?_
        simp only [norm_one]
        gcongr
        exact (norm_tsum_le_tsum_norm hsum).trans hb
    _ ≤ (C0 + 1) * (‖s‖ + 1) ^ 2 := by
        have : ‖s - 1‖ * ‖s‖ ≤ (‖s‖ + 1) ^ 2 := by nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
        nlinarith [norm_nonneg s]

theorem zeta_lower : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 6 / 5 ≤ s.re → c ≤ ‖riemannZeta s‖ := by

  have hsum : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (6 / 5 : ℂ) n‖) := by
    have h := (ArithmeticFunction.LSeriesSummable_moebius_iff (s := (6 / 5 : ℂ))).2 (by norm_num)
    exact h.norm
  set C1 := ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (6 / 5 : ℂ) n‖
  have hC1 : 0 ≤ C1 := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨1 / (C1 + 1), by positivity, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at hprod
  have hle : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ C1 := by
    have hb : ∀ n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n‖ ≤
        ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (6 / 5 : ℂ) n‖ := fun n =>
      LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
    have hs' : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
    exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hb hsum)
  have h1 : 1 = ‖riemannZeta s‖ * ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ := by
    rw [← norm_mul, hprod]; simp
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (riemannZeta s), norm_nonneg (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s)]

/-! ### Landau's local expansion of `Z'/Z` -/

/-- Centres `6/5 + i t`. -/
def ctr (t : ℝ) : ℂ := 6 / 5 + t * I

/-- Zeros of `Z` in the closed disc of radius `11/20` about `c`. -/
def zball (c : ℂ) : Finset ℂ := (Z_zeros_finite (isCompact_closedBall c (11 / 20))).toFinset

theorem mem_zball {c u : ℂ} : u ∈ zball c ↔ Z u = 0 ∧ u ∈ closedBall c (11 / 20) := by
  simp [zball]

theorem ctr_re (t : ℝ) : (ctr t).re = 6 / 5 := by simp [ctr]
theorem ctr_im (t : ℝ) : (ctr t).im = t := by simp [ctr]

theorem norm_ctr_le (t : ℝ) : ‖ctr t‖ ≤ |t| + 6 / 5 := by
  unfold ctr
  calc ‖(6 / 5 : ℂ) + t * I‖ ≤ ‖(6 / 5 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = |t| + 6 / 5 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      norm_num; ring

/-- The log-derivative of a factorization. -/
theorem logDeriv_factor {g : ℂ → ℂ} (hg : Differentiable ℂ g) (F : Finset ℂ) (m : ℂ → ℕ)
    {s : ℂ} (hsF : ∀ u ∈ F, s ≠ u) (hgs : g s ≠ 0) :
    logDeriv (fun z => (∏ u ∈ F, (z - u) ^ m u) * g z) s =
      ∑ u ∈ F, (m u : ℂ) / (s - u) + deriv g s / g s := by
  have hP : (∏ u ∈ F, (s - u) ^ m u) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hsF u hu))
  rw [logDeriv_mul s hP hgs (by fun_prop) (hg s)]
  rw [logDeriv_prod (f := fun u z => (z - u) ^ m u) (x := s)
    (fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hsF u hu))) (fun u _ => by fun_prop)]
  rw [logDeriv_apply g s]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
  have : deriv (fun z : ℂ => z - u) s = 1 := by simp
  rw [this]
  field_simp

theorem bc_at {h : ℂ → ℂ} {c : ℂ} {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ)
    (hd : DifferentiableOn ℂ h (ball c R)) (hre : ∀ w ∈ ball c R, (h w).re ≤ Λ) (h0 : h c = 0)
    {w : ℂ} (hw : w ∈ ball c R) : ‖h w‖ ≤ 2 * Λ * ‖w - c‖ / (R - ‖w - c‖) := by
  have hmaps : ∀ z ∈ ball (0 : ℂ) R, c + z ∈ ball c R := by
    intro z hz; simpa [dist_eq_norm] using hz
  have hd' : DifferentiableOn ℂ (fun z => h (c + z)) (ball 0 R) :=
    hd.comp (by fun_prop) hmaps
  have := Complex.borelCaratheodory_zero (f := fun z => h (c + z)) (z := w - c) hΛ hd'
    (fun z hz => hre _ (hmaps z hz)) hR (by simpa [dist_eq_norm] using hw) (by simpa using h0)
  simpa using this

/-- Primitive of `g'/g` on a disc where `g ≠ 0`, with `g = g(c) exp(h)`. -/
theorem log_on_ball {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} {R : ℝ}
    (hne : ∀ w ∈ ball c R, g w ≠ 0) (hc : c ∈ ball c R) :
    ∃ h : ℂ → ℂ, h c = 0 ∧ (∀ w ∈ ball c R, HasDerivAt h (deriv g w / g w) w) ∧
      ∀ w ∈ ball c R, g w = g c * Complex.exp (h w) := by
  have hdg : Differentiable ℂ (deriv g) := fun w => ((hg.analyticAt w).deriv).differentiableAt
  have hdiff : DifferentiableOn ℂ (fun w => deriv g w / g w) (ball c R) :=
    fun w hw => ((hdg w).div (hg w) (hne w hw)).differentiableWithinAt
  obtain ⟨H, hH0, hH⟩ := (hdiff.isExactOn_ball).with_val_at c 0
  refine ⟨H, hH0, hH, ?_⟩
  have hφd : ∀ w ∈ ball c R, HasDerivAt (fun w => g w * Complex.exp (-H w)) 0 w := by
    intro w hw
    have h1 := (hg w).hasDerivAt
    have h2 := ((hH w hw).neg).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    have := hne w hw
    field_simp
    ring
  intro w hw
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
    (f := fun w => g w * Complex.exp (-H w))
    (fun z hz => (hφd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hφd z hz).deriv) hw hc
  simp only [hH0, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp

theorem log_ratio_bound (A0 : ℝ) (t : ℝ) (CZ m0 : ℝ) (hCZ : 0 < CZ) (hm0 : 0 < m0)
    (hA0 : |Real.log (CZ / m0)| ≤ A0) :
    Real.log (CZ * (|t| + 4) ^ 2 / m0) ≤ (A0 + 4) * Real.log (|t| + 3) := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hL : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have h1 : Real.log (CZ * (|t| + 4) ^ 2 / m0) = Real.log (CZ / m0) + 2 * Real.log (|t| + 4) := by
    rw [show CZ * (|t| + 4) ^ 2 / m0 = CZ / m0 * (|t| + 4) ^ 2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have h2 : Real.log (|t| + 4) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [show ((|t| + 3) ^ (2 : ℝ)) = (|t| + 3) * (|t| + 3) by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add (by positivity)]; simp]
    nlinarith
  have h3 : Real.log (CZ / m0) ≤ A0 := (le_abs_self _).trans hA0
  have hA0' : 0 ≤ A0 := (abs_nonneg _).trans hA0
  nlinarith

theorem landau : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    (∑ u ∈ zball (ctr t), (mult u : ℝ)) ≤ C * Real.log (|t| + 3) ∧
    ∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → Z s ≠ 0 →
      ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤
        C * Real.log (|t| + 3) := by
  obtain ⟨CZ, hCZ, hZb⟩ := Z_bound
  obtain ⟨cz, hcz, hzl⟩ := zeta_lower
  set m0 := cz / 5 with hm0def
  have hm0 : 0 < m0 := by positivity
  set A0 := |Real.log (CZ / m0)|
  have hl12 : 0 < Real.log (12 / 11) := Real.log_pos (by norm_num)
  refine ⟨(A0 + 5) * (1680 + 1 / Real.log (12 / 11)), by positivity, fun t => ?_⟩
  set c := ctr t with hc
  set F := zball c with hF
  set L := Real.log (|t| + 3) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  set M := CZ * (|t| + 4) ^ 2 with hMdef
  have hM0 : 0 < M := by positivity
  set Λ := Real.log (M / m0) with hΛdef
  have hΛ : Λ ≤ (A0 + 4) * L := log_ratio_bound A0 t CZ m0 hCZ hm0 le_rfl
  obtain ⟨g, hg, hgF, hZg⟩ := factor F Z Z_diff (fun u _ => Z_order_ne_top u)
  set n := ∑ u ∈ F, mult u with hn
  have hmult : ∀ u, analyticOrderNatAt Z u = mult u := fun u => rfl
  simp only [hmult] at hZg
  -- bound of `Z` near the centre
  have hZbd : ∀ z ∈ closedBall c (23 / 20), ‖Z z‖ ≤ M := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : 1 / 20 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - c)
      rw [sub_re, hc, ctr_re] at this
      have := neg_abs_le (z.re - 6 / 5); linarith
    refine (hZb z hre).trans ?_
    have hz' : ‖z‖ ≤ |t| + 47 / 20 := by
      calc ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using norm_add_le (z - c) c
        _ ≤ 23 / 20 + (|t| + 6 / 5) := add_le_add hz (norm_ctr_le t)
        _ = |t| + 47 / 20 := by ring
    have : (‖z‖ + 1) ^ 2 ≤ (|t| + 4) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [hMdef]; exact mul_le_mul_of_nonneg_left this hCZ.le
  -- lower bound at the centre
  have hZc : m0 ≤ ‖Z c‖ := by
    have hc1 : c ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hc, ctr_re] at this; norm_num at this
    rw [Z_eq hc1, norm_mul]
    have h1 : 1 / 5 ≤ ‖c - 1‖ := by
      have := Complex.abs_re_le_norm (c - 1)
      rw [sub_re, hc, ctr_re] at this; norm_num at this ⊢; linarith
    have h2 := hzl c (by rw [hc, ctr_re])
    rw [hm0def]
    calc cz / 5 = 1 / 5 * cz := by ring
      _ ≤ ‖c - 1‖ * ‖riemannZeta c‖ := by gcongr
  -- the product is large on the sphere and small at the centre
  have hPsph : ∀ z ∈ sphere c (23 / 20), (3 / 5 : ℝ) ^ n ≤ ‖∏ u ∈ F, (z - u) ^ mult u‖ := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    rw [norm_prod, hn, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro u hu
    rw [norm_pow]
    apply pow_le_pow_left₀ (by norm_num)
    have hu' := (mem_zball.1 hu).2
    rw [mem_closedBall, dist_eq_norm] at hu'
    have := norm_sub_norm_le (z - c) (u - c)
    rw [show z - c - (u - c) = z - u by ring] at this
    linarith
  have hPc : ‖∏ u ∈ F, (c - u) ^ mult u‖ ≤ (11 / 20 : ℝ) ^ n := by
    rw [norm_prod, hn, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro u hu
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hu' := (mem_zball.1 hu).2
    rw [mem_closedBall, dist_eq_norm] at hu'
    rw [norm_sub_rev]; exact hu'
  -- `g` on the big disc
  have hgsph : ∀ z ∈ frontier (ball c (23 / 20)), ‖g z‖ ≤ M / (3 / 5) ^ n := by
    intro z hz
    rw [frontier_ball c (by norm_num)] at hz
    have h1 := hPsph z hz
    have h2 := hZbd z (sphere_subset_closedBall hz)
    rw [hZg z, norm_mul] at h2
    rw [le_div_iff₀ (by positivity)]
    calc ‖g z‖ * (3 / 5) ^ n ≤ ‖g z‖ * ‖∏ u ∈ F, (z - u) ^ mult u‖ := by gcongr
      _ = ‖∏ u ∈ F, (z - u) ^ mult u‖ * ‖g z‖ := by ring
      _ ≤ M := h2
  have hgball : ∀ w ∈ closedBall c (23 / 20), ‖g w‖ ≤ M / (3 / 5) ^ n := by
    intro w hw
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      hg.diffContOnCl hgsph
    rwa [closure_ball c (by norm_num)]
  have hgc : m0 / (11 / 20) ^ n ≤ ‖g c‖ := by
    rw [div_le_iff₀ (by positivity)]
    calc m0 ≤ ‖Z c‖ := hZc
      _ = ‖∏ u ∈ F, (c - u) ^ mult u‖ * ‖g c‖ := by rw [hZg c, norm_mul]
      _ ≤ (11 / 20) ^ n * ‖g c‖ := by gcongr
      _ = ‖g c‖ * (11 / 20) ^ n := by ring
  -- zero count
  have hcount : (n : ℝ) * Real.log (12 / 11) ≤ Λ := by
    have h1 := hgball c (mem_closedBall_self (by norm_num))
    have h2 : m0 / (11 / 20) ^ n ≤ M / (3 / 5) ^ n := hgc.trans h1
    have h3 : (12 / 11 : ℝ) ^ n ≤ M / m0 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
      rw [le_div_iff₀ hm0]
      have e : (12 / 11 : ℝ) ^ n * (11 / 20) ^ n = (3 / 5) ^ n := by
        rw [← mul_pow]; norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 11 / 20) n]
    have := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at this
    exact this
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hcount
  refine ⟨?_, ?_⟩
  · -- count bound
    have : (n : ℝ) ≤ Λ / Real.log (12 / 11) := by rw [le_div_iff₀ hl12]; exact hcount
    have hsum : (∑ u ∈ F, (mult u : ℝ)) = n := by rw [hn]; push_cast; rfl
    rw [hsum]
    calc (n : ℝ) ≤ Λ / Real.log (12 / 11) := this
      _ ≤ (A0 + 4) * L / Real.log (12 / 11) := by gcongr
      _ ≤ (A0 + 5) * (1680 + 1 / Real.log (12 / 11)) * L := by
          have hA0 : 0 ≤ A0 := abs_nonneg _
          rw [div_le_iff₀ hl12]
          have : 0 ≤ (A0 + 5) * 1680 * L * Real.log (12 / 11) := by positivity
          have e : (A0 + 5) * (1680 + 1 / Real.log (12 / 11)) * L * Real.log (12 / 11) =
              (A0 + 5) * 1680 * L * Real.log (12 / 11) + (A0 + 5) * L := by field_simp
          rw [e]; nlinarith
  · intro s hs hZs
    -- `g` does not vanish on the small disc
    have hgne : ∀ w ∈ ball c (11 / 20), g w ≠ 0 := by
      intro w hw hgw
      by_cases hwF : w ∈ F
      · exact hgF w hwF hgw
      · apply hwF
        rw [hF, mem_zball]
        refine ⟨by rw [hZg w, hgw, mul_zero], ball_subset_closedBall hw⟩
    obtain ⟨h, hh0, hhd, hhg⟩ := log_on_ball hg hgne (mem_ball_self (by norm_num))
    -- real part bound
    have hre : ∀ w ∈ ball c (11 / 20), (h w).re ≤ Λ + 1 := by
      intro w hw
      have h1 := hgball w (ball_subset_closedBall (ball_subset_ball (by norm_num) hw))
      have h2 : ‖g w‖ = ‖g c‖ * Real.exp (h w).re := by
        rw [hhg w hw, norm_mul, Complex.norm_exp]
      have hgc0 : 0 < ‖g c‖ := lt_of_lt_of_le (by positivity) hgc
      have h3 : Real.exp (h w).re ≤ M / m0 := by
        have h4 : ‖g c‖ * Real.exp (h w).re ≤ M / (3 / 5) ^ n := h2 ▸ h1
        have h5 : M / (3 / 5) ^ n ≤ (M / m0) * ‖g c‖ := by
          have h7 : M / (3 / 5) ^ n ≤ M / (11 / 20) ^ n :=
            div_le_div_of_nonneg_left hM0.le (by positivity)
              (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
          have h6 : (M / m0) * (m0 / (11 / 20) ^ n) ≤ (M / m0) * ‖g c‖ := by gcongr
          have e : (M / m0) * (m0 / (11 / 20) ^ n) = M / (11 / 20) ^ n := by field_simp
          rw [e] at h6
          exact h7.trans h6
        have := h4.trans h5
        nlinarith
      have := (Real.le_log_iff_exp_le (by positivity)).2 h3
      linarith
    have hdiffh : DifferentiableOn ℂ h (ball c (11 / 20)) :=
      fun w hw => (hhd w hw).differentiableAt.differentiableWithinAt
    -- Cauchy estimate at `s`
    have hsball : s ∈ ball c (11 / 20) := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hsub : closedBall s (1 / 40) ⊆ ball c (11 / 20) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball, dist_eq_norm]
      calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := by simpa using norm_add_le (z - s) (s - c)
        _ < 11 / 20 := by linarith
    have hcauchy : ‖deriv h s‖ ≤ 42 * (Λ + 1) / (1 / 40) := by
      apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
      · exact DifferentiableOn.diffContOnCl
          (hdiffh.mono (closure_ball s (by norm_num : (1 / 40 : ℝ) ≠ 0) ▸ hsub))
      · intro z hz
        have hz' : z ∈ ball c (11 / 20) := hsub (sphere_subset_closedBall hz)
        have hzc : ‖z - c‖ ≤ 21 / 40 := by
          rw [mem_sphere, dist_eq_norm] at hz
          calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := by simpa using norm_add_le (z - s) (s - c)
            _ ≤ 21 / 40 := by linarith
        have hbc := bc_at (by norm_num) (by linarith) hdiffh hre hh0 hz'
        refine hbc.trans ?_
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (z - c)]
    have hderiv : deriv h s = deriv g s / g s := (hhd s hsball).deriv
    have hsF : ∀ u ∈ F, s ≠ u := by
      intro u hu hsu
      exact hZs (hsu ▸ (mem_zball.1 hu).1)
    have hlog : deriv Z s / Z s = ∑ u ∈ F, (mult u : ℂ) / (s - u) + deriv g s / g s := by
      have hfun : Z = fun z => (∏ u ∈ F, (z - u) ^ mult u) * g z := funext hZg
      rw [← logDeriv_apply, hfun]
      exact logDeriv_factor hg F mult hsF (hgne s hsball)
    rw [hlog, add_sub_cancel_left, ← hderiv]
    calc ‖deriv h s‖ ≤ 42 * (Λ + 1) / (1 / 40) := hcauchy
      _ = 1680 * (Λ + 1) := by ring
      _ ≤ (A0 + 5) * (1680 + 1 / Real.log (12 / 11)) * L := by
          have hA0 : 0 ≤ A0 := abs_nonneg _
          have h1 : Λ + 1 ≤ (A0 + 5) * L := by nlinarith
          have h2 : 0 ≤ (A0 + 5) * (1 / Real.log (12 / 11)) * L := by positivity
          nlinarith

/-! ### `-ζ'/ζ` and the zero-free region -/


theorem landauG : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    (∑ u ∈ zball (ctr t), (mult u : ℝ)) ≤ C * Real.log (|t| + 3) ∧
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (ctr t) (11 / 20)) ∧
      (∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → ‖G s‖ ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ ball (ctr t) (11 / 20), Z s ≠ 0 →
        deriv Z s / Z s = ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u) + G s := by
  obtain ⟨CZ, hCZ, hZb⟩ := Z_bound
  obtain ⟨cz, hcz, hzl⟩ := zeta_lower
  set m0 := cz / 5 with hm0def
  have hm0 : 0 < m0 := by positivity
  set A0 := |Real.log (CZ / m0)|
  have hl12 : 0 < Real.log (12 / 11) := Real.log_pos (by norm_num)
  refine ⟨(A0 + 5) * (1680 + 1 / Real.log (12 / 11)), by positivity, fun t => ?_⟩
  set c := ctr t with hc
  set F := zball c with hF
  set L := Real.log (|t| + 3) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  set M := CZ * (|t| + 4) ^ 2 with hMdef
  have hM0 : 0 < M := by positivity
  set Λ := Real.log (M / m0) with hΛdef
  have hΛ : Λ ≤ (A0 + 4) * L := log_ratio_bound A0 t CZ m0 hCZ hm0 le_rfl
  obtain ⟨g, hg, hgF, hZg⟩ := factor F Z Z_diff (fun u _ => Z_order_ne_top u)
  set n := ∑ u ∈ F, mult u with hn
  have hmult : ∀ u, analyticOrderNatAt Z u = mult u := fun u => rfl
  simp only [hmult] at hZg
  -- bound of `Z` near the centre
  have hZbd : ∀ z ∈ closedBall c (23 / 20), ‖Z z‖ ≤ M := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : 1 / 20 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - c)
      rw [sub_re, hc, ctr_re] at this
      have := neg_abs_le (z.re - 6 / 5); linarith
    refine (hZb z hre).trans ?_
    have hz' : ‖z‖ ≤ |t| + 47 / 20 := by
      calc ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using norm_add_le (z - c) c
        _ ≤ 23 / 20 + (|t| + 6 / 5) := add_le_add hz (norm_ctr_le t)
        _ = |t| + 47 / 20 := by ring
    have : (‖z‖ + 1) ^ 2 ≤ (|t| + 4) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [hMdef]; exact mul_le_mul_of_nonneg_left this hCZ.le
  -- lower bound at the centre
  have hZc : m0 ≤ ‖Z c‖ := by
    have hc1 : c ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hc, ctr_re] at this; norm_num at this
    rw [Z_eq hc1, norm_mul]
    have h1 : 1 / 5 ≤ ‖c - 1‖ := by
      have := Complex.abs_re_le_norm (c - 1)
      rw [sub_re, hc, ctr_re] at this; norm_num at this ⊢; linarith
    have h2 := hzl c (by rw [hc, ctr_re])
    rw [hm0def]
    calc cz / 5 = 1 / 5 * cz := by ring
      _ ≤ ‖c - 1‖ * ‖riemannZeta c‖ := by gcongr
  -- the product is large on the sphere and small at the centre
  have hPsph : ∀ z ∈ sphere c (23 / 20), (3 / 5 : ℝ) ^ n ≤ ‖∏ u ∈ F, (z - u) ^ mult u‖ := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    rw [norm_prod, hn, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro u hu
    rw [norm_pow]
    apply pow_le_pow_left₀ (by norm_num)
    have hu' := (mem_zball.1 hu).2
    rw [mem_closedBall, dist_eq_norm] at hu'
    have := norm_sub_norm_le (z - c) (u - c)
    rw [show z - c - (u - c) = z - u by ring] at this
    linarith
  have hPc : ‖∏ u ∈ F, (c - u) ^ mult u‖ ≤ (11 / 20 : ℝ) ^ n := by
    rw [norm_prod, hn, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro u hu
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hu' := (mem_zball.1 hu).2
    rw [mem_closedBall, dist_eq_norm] at hu'
    rw [norm_sub_rev]; exact hu'
  -- `g` on the big disc
  have hgsph : ∀ z ∈ frontier (ball c (23 / 20)), ‖g z‖ ≤ M / (3 / 5) ^ n := by
    intro z hz
    rw [frontier_ball c (by norm_num)] at hz
    have h1 := hPsph z hz
    have h2 := hZbd z (sphere_subset_closedBall hz)
    rw [hZg z, norm_mul] at h2
    rw [le_div_iff₀ (by positivity)]
    calc ‖g z‖ * (3 / 5) ^ n ≤ ‖g z‖ * ‖∏ u ∈ F, (z - u) ^ mult u‖ := by gcongr
      _ = ‖∏ u ∈ F, (z - u) ^ mult u‖ * ‖g z‖ := by ring
      _ ≤ M := h2
  have hgball : ∀ w ∈ closedBall c (23 / 20), ‖g w‖ ≤ M / (3 / 5) ^ n := by
    intro w hw
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      hg.diffContOnCl hgsph
    rwa [closure_ball c (by norm_num)]
  have hgc : m0 / (11 / 20) ^ n ≤ ‖g c‖ := by
    rw [div_le_iff₀ (by positivity)]
    calc m0 ≤ ‖Z c‖ := hZc
      _ = ‖∏ u ∈ F, (c - u) ^ mult u‖ * ‖g c‖ := by rw [hZg c, norm_mul]
      _ ≤ (11 / 20) ^ n * ‖g c‖ := by gcongr
      _ = ‖g c‖ * (11 / 20) ^ n := by ring
  -- zero count
  have hcount : (n : ℝ) * Real.log (12 / 11) ≤ Λ := by
    have h1 := hgball c (mem_closedBall_self (by norm_num))
    have h2 : m0 / (11 / 20) ^ n ≤ M / (3 / 5) ^ n := hgc.trans h1
    have h3 : (12 / 11 : ℝ) ^ n ≤ M / m0 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
      rw [le_div_iff₀ hm0]
      have e : (12 / 11 : ℝ) ^ n * (11 / 20) ^ n = (3 / 5) ^ n := by
        rw [← mul_pow]; norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 11 / 20) n]
    have := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at this
    exact this
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hcount
  refine ⟨?_, ?_⟩
  · -- count bound
    have : (n : ℝ) ≤ Λ / Real.log (12 / 11) := by rw [le_div_iff₀ hl12]; exact hcount
    have hsum : (∑ u ∈ F, (mult u : ℝ)) = n := by rw [hn]; push_cast; rfl
    rw [hsum]
    calc (n : ℝ) ≤ Λ / Real.log (12 / 11) := this
      _ ≤ (A0 + 4) * L / Real.log (12 / 11) := by gcongr
      _ ≤ (A0 + 5) * (1680 + 1 / Real.log (12 / 11)) * L := by
          have hA0 : 0 ≤ A0 := abs_nonneg _
          rw [div_le_iff₀ hl12]
          have : 0 ≤ (A0 + 5) * 1680 * L * Real.log (12 / 11) := by positivity
          have e : (A0 + 5) * (1680 + 1 / Real.log (12 / 11)) * L * Real.log (12 / 11) =
              (A0 + 5) * 1680 * L * Real.log (12 / 11) + (A0 + 5) * L := by field_simp
          rw [e]; nlinarith
  · -- the remainder `G = g′/g`
    -- `g` does not vanish on the small disc
    have hgne : ∀ w ∈ ball c (11 / 20), g w ≠ 0 := by
      intro w hw hgw
      by_cases hwF : w ∈ F
      · exact hgF w hwF hgw
      · apply hwF
        rw [hF, mem_zball]
        refine ⟨by rw [hZg w, hgw, mul_zero], ball_subset_closedBall hw⟩
    obtain ⟨h, hh0, hhd, hhg⟩ := log_on_ball hg hgne (mem_ball_self (by norm_num))
    -- real part bound
    have hre : ∀ w ∈ ball c (11 / 20), (h w).re ≤ Λ + 1 := by
      intro w hw
      have h1 := hgball w (ball_subset_closedBall (ball_subset_ball (by norm_num) hw))
      have h2 : ‖g w‖ = ‖g c‖ * Real.exp (h w).re := by
        rw [hhg w hw, norm_mul, Complex.norm_exp]
      have hgc0 : 0 < ‖g c‖ := lt_of_lt_of_le (by positivity) hgc
      have h3 : Real.exp (h w).re ≤ M / m0 := by
        have h4 : ‖g c‖ * Real.exp (h w).re ≤ M / (3 / 5) ^ n := h2 ▸ h1
        have h5 : M / (3 / 5) ^ n ≤ (M / m0) * ‖g c‖ := by
          have h7 : M / (3 / 5) ^ n ≤ M / (11 / 20) ^ n :=
            div_le_div_of_nonneg_left hM0.le (by positivity)
              (pow_le_pow_left₀ (by norm_num) (by norm_num) n)
          have h6 : (M / m0) * (m0 / (11 / 20) ^ n) ≤ (M / m0) * ‖g c‖ := by gcongr
          have e : (M / m0) * (m0 / (11 / 20) ^ n) = M / (11 / 20) ^ n := by field_simp
          rw [e] at h6
          exact h7.trans h6
        have := h4.trans h5
        nlinarith
      have := (Real.le_log_iff_exp_le (by positivity)).2 h3
      linarith
    have hdiffh : DifferentiableOn ℂ h (ball c (11 / 20)) :=
      fun w hw => (hhd w hw).differentiableAt.differentiableWithinAt
    have hdg : Differentiable ℂ (deriv g) := fun w => ((hg.analyticAt w).deriv).differentiableAt
    refine ⟨fun w => deriv g w / g w,
      fun w hw => ((hdg w).div (hg w) (hgne w hw)).differentiableWithinAt,
      fun s hs => ?_, fun s hs' hZs => ?_⟩
    · -- Cauchy estimate at `s`
      have hsball : s ∈ ball c (11 / 20) := by
        rw [mem_ball, dist_eq_norm]; linarith
      have hsub : closedBall s (1 / 40) ⊆ ball c (11 / 20) := by
        intro z hz
        rw [mem_closedBall, dist_eq_norm] at hz
        rw [mem_ball, dist_eq_norm]
        calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := by simpa using norm_add_le (z - s) (s - c)
          _ < 11 / 20 := by linarith
      have hcauchy : ‖deriv h s‖ ≤ 42 * (Λ + 1) / (1 / 40) := by
        apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
        · exact DifferentiableOn.diffContOnCl
            (hdiffh.mono (closure_ball s (by norm_num : (1 / 40 : ℝ) ≠ 0) ▸ hsub))
        · intro z hz
          have hz' : z ∈ ball c (11 / 20) := hsub (sphere_subset_closedBall hz)
          have hzc : ‖z - c‖ ≤ 21 / 40 := by
            rw [mem_sphere, dist_eq_norm] at hz
            calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := by simpa using norm_add_le (z - s) (s - c)
              _ ≤ 21 / 40 := by linarith
          have hbc := bc_at (by norm_num) (by linarith) hdiffh hre hh0 hz'
          refine hbc.trans ?_
          rw [div_le_iff₀ (by linarith)]
          nlinarith [norm_nonneg (z - c)]
      have hderiv : deriv h s = deriv g s / g s := (hhd s hsball).deriv
      show ‖deriv g s / g s‖ ≤ _
      rw [← hderiv]
      calc ‖deriv h s‖ ≤ 42 * (Λ + 1) / (1 / 40) := hcauchy
        _ = 1680 * (Λ + 1) := by ring
        _ ≤ (A0 + 5) * (1680 + 1 / Real.log (12 / 11)) * L := by
            have hA0 : 0 ≤ A0 := abs_nonneg _
            have h1 : Λ + 1 ≤ (A0 + 5) * L := by nlinarith
            have h2 : 0 ≤ (A0 + 5) * (1 / Real.log (12 / 11)) * L := by positivity
            nlinarith
    · have hsball : s ∈ ball c (11 / 20) := hs'
      have hsF : ∀ u ∈ F, s ≠ u := by
        intro u hu hsu
        exact hZs (hsu ▸ (mem_zball.1 hu).1)
      have hlog : deriv Z s / Z s = ∑ u ∈ F, (mult u : ℂ) / (s - u) + deriv g s / g s := by
        have hfun : Z = fun z => (∏ u ∈ F, (z - u) ^ mult u) * g z := funext hZg
        rw [← logDeriv_apply, hfun]
        exact logDeriv_factor hg F mult hsF (hgne s hsball)
      exact hlog
/-- `-ζ'/ζ` expressed through `Z`. -/
def Lf (s : ℂ) : ℂ := -deriv Z s / Z s + 1 / (s - 1)

theorem trivChar_one_eq : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta := by
  funext s; simp [DirichletCharacter.LFunctionTrivChar]

theorem deriv_Z {s : ℂ} (hs : s ≠ 1) :
    deriv Z s = (s - 1) * deriv riemannZeta s + riemannZeta s := by
  have := DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs
  rw [trivChar_one_eq] at this
  exact this

theorem Lf_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    Lf s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, Lf, deriv_Z hs1,
    Z_eq hs1]
  field_simp
  ring

/-- `Re (3 + 4w + w²) ≥ 0` on the unit circle. -/
theorem three_four_one_aux {w : ℂ} (hw : ‖w‖ = 1) : 0 ≤ (3 + 4 * w + w ^ 2).re := by
  have h : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this; nlinarith
  have : (3 + 4 * w + w ^ 2).re = 2 * (1 + w.re) ^ 2 := by
    simp only [add_re, mul_re, pow_two]; norm_num; nlinarith
  rw [this]; positivity

theorem three_four_one {σ γ : ℝ} (hσ : 1 < σ) :
    0 ≤ (3 * Lf σ + 4 * Lf (σ + γ * I) + Lf (σ + 2 * γ * I)).re := by
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hre1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hre2 : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have hre3 : 1 < ((σ : ℂ) + 2 * γ * I).re := by simpa using hσ
  rw [Lf_eq_LSeries hre1, Lf_eq_LSeries hre2, Lf_eq_LSeries hre3]
  have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hre1).LSeriesHasSum
  have h2 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hre2).LSeriesHasSum
  have h3 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hre3).LSeriesHasSum
  have hsum := Complex.hasSum_re (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
  refine hsum.nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [LSeries.term, hn.ne', if_false]
  set w : ℂ := (n : ℂ) ^ (-(γ * I)) with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_natCast_cpow_of_pos hn]; simp
  have hp : ∀ k : ℕ, (n : ℂ) ^ ((σ : ℂ) + k * γ * I) = (n : ℂ) ^ (σ : ℂ) * (w ^ k)⁻¹ := by
    intro k
    rw [cpow_add _ _ hn0, hw, ← cpow_nat_mul,
      show (k : ℂ) * -((γ : ℂ) * I) = -(k * γ * I) by ring, cpow_neg, inv_inv]
  have e1 := hp 1
  have e2 := hp 2
  simp only [Nat.cast_one, one_mul, pow_one, Nat.cast_ofNat] at e1 e2
  rw [e1, e2]
  have hnσ : (n : ℂ) ^ (σ : ℂ) = ((n : ℝ) ^ σ : ℝ) := by
    rw [← ofReal_natCast, ofReal_cpow (by positivity)]
  rw [hnσ]
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwn; simp at hwn
  have hpos : 0 < (n : ℝ) ^ σ := by positivity
  have key : 3 * ((f n) / ((n : ℝ) ^ σ : ℝ)) + 4 * ((f n) / (((n : ℝ) ^ σ : ℝ) * w⁻¹)) +
      (f n) / (((n : ℝ) ^ σ : ℝ) * (w ^ 2)⁻¹) =
      ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) * (3 + 4 * w + w ^ 2) := by
    simp only [f]
    push_cast
    field_simp
  simp only [f] at key
  rw [key, re_ofReal_mul]
  exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hpos.le)
    (three_four_one_aux hwn)

theorem zero_free_low : ∃ η : ℝ, 0 < η ∧ ∀ ρ : ℂ, Z ρ = 0 → |ρ.im| ≤ 1 → ρ.re ≤ 1 - η := by
  set K : Set ℂ := (fun y : ℝ => (1 : ℂ) + y * I) '' Icc (-1) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen {s : ℂ | Z s ≠ 0} := isOpen_ne_fun Z_diff.continuous continuous_const
  have hKU : K ⊆ {s : ℂ | Z s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩ h
    have := Z_re_lt_one h
    simp at this
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ / 2, by positivity, fun ρ hρ him => ?_⟩
  by_contra hlt
  push Not at hlt
  have hρ1 := Z_re_lt_one hρ
  have hmem : ρ ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨1 + ρ.im * I, ⟨ρ.im, ⟨by linarith [neg_abs_le ρ.im], by linarith [le_abs_self ρ.im]⟩,
      rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have : ρ - (1 + ρ.im * I) = ((ρ.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  exact hδK hmem hρ

theorem re_div_nonneg {m : ℝ} {z : ℂ} (hm : 0 ≤ m) (hz : 0 ≤ z.re) : 0 ≤ ((m : ℂ) / z).re := by
  rw [div_eq_mul_inv, re_ofReal_mul, inv_re]
  exact mul_nonneg hm (div_nonneg hz (normSq_nonneg _))

theorem Lf_upper {C : ℝ} (hland : ∀ t : ℝ, ∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → Z s ≠ 0 →
      ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤ C * Real.log (|t| + 3))
    {t σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 11 / 10) :
    (Lf (σ + t * I)).re ≤ C * Real.log (|t| + 3)
      - (∑ u ∈ zball (ctr t), (mult u : ℂ) / ((σ + t * I : ℂ) - u)).re
      + (1 / ((σ + t * I : ℂ) - 1)).re := by
  set s : ℂ := σ + t * I
  have hs : ‖s - ctr t‖ ≤ 1 / 2 := by
    have : s - ctr t = ((σ - 6 / 5 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, ctr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hZs : Z s ≠ 0 := fun h => by
    have := Z_re_lt_one h; simp [s] at this; linarith
  have h := hland t s hs hZs
  have h2 := (Complex.abs_re_le_norm _).trans h
  rw [sub_re] at h2
  have h3 := neg_abs_le ((deriv Z s / Z s).re - (∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)).re)
  unfold Lf
  rw [add_re, neg_div, neg_re]
  linarith

theorem re_sum_ge {F : Finset ℂ} {s ρ : ℂ} (hρ : ρ ∈ F) (hre : ∀ u ∈ F, u.re ≤ s.re) :
    (((mult ρ : ℝ) : ℂ) / (s - ρ)).re ≤ (∑ u ∈ F, (mult u : ℂ) / (s - u)).re := by
  rw [re_sum]
  have := Finset.single_le_sum (f := fun u => ((mult u : ℂ) / (s - u)).re)
    (fun u hu => by
      have := re_div_nonneg (m := (mult u : ℝ)) (z := s - u) (Nat.cast_nonneg _)
        (by rw [sub_re]; linarith [hre u hu])
      simpa using this) hρ
  simpa using this

set_option maxHeartbeats 1000000 in
theorem zero_free' : ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℂ, Z ρ = 0 →
    ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3) := by
  obtain ⟨C, hC, hland⟩ := landau
  obtain ⟨η0, hη0, hlow⟩ := zero_free_low
  set K := 3 * C * Real.log 3 + 6 * C + 5 with hK
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hK5 : 5 ≤ K := by
    have : 0 ≤ 3 * C * Real.log 3 + 6 * C := by positivity
    linarith
  refine ⟨min (7 / (200 * K)) (min (7 / 20) η0), by positivity, fun ρ hρ => ?_⟩
  set β := ρ.re
  set γ := ρ.im
  set L := Real.log (|γ| + 3) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith [abs_nonneg γ]
  have hβ1 : β < 1 := Z_re_lt_one hρ
  have hcL : ∀ c' : ℝ, 0 ≤ c' → c' / L ≤ c' := fun c' hc' => div_le_self hc' hL
  have hmin1 := min_le_left (7 / (200 * K)) (min (7 / 20) η0)
  have hmin2 := (min_le_right (7 / (200 * K)) (min (7 / 20) η0)).trans (min_le_left _ _)
  have hmin3 := (min_le_right (7 / (200 * K)) (min (7 / 20) η0)).trans (min_le_right _ _)
  set c := min (7 / (200 * K)) (min (7 / 20) η0)
  have hc0 : 0 ≤ c := by positivity
  have hcLc : c / L ≤ c := hcL c hc0
  by_cases hsmall : β < 13 / 20
  · linarith
  by_cases hlow' : |γ| ≤ 1
  · have := hlow ρ hρ hlow'; linarith
  push Not at hsmall hlow'
  -- main case
  set δ := 1 / (8 * K * L) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 40 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set σ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 11 / 10 := by linarith
  have h341 := three_four_one (σ := σ) (γ := γ) hσ1
  -- bound at σ
  have b0 : (Lf ((σ : ℂ) + (0 : ℝ) * I)).re ≤ C * Real.log 3 + 1 / δ := by
    have h := Lf_upper (fun t s hs hz => hland t |>.2 s hs hz) (t := 0) hσ1 hσ2
    have hsum : 0 ≤ (∑ u ∈ zball (ctr 0), (mult u : ℂ) / (((σ : ℂ) + (0 : ℝ) * I) - u)).re := by
      rw [re_sum]
      refine Finset.sum_nonneg fun u hu => re_div_nonneg (Nat.cast_nonneg _) ?_
      have := Z_re_lt_one (mem_zball.1 hu).1
      simp; linarith
    have hpole : (1 / (((σ : ℂ) + (0 : ℝ) * I) - 1)).re = 1 / δ := by
      have : ((σ : ℂ) + (0 : ℝ) * I) - 1 = ((δ : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [σ]
      rw [this]; simp
    simp only [abs_zero, zero_add] at h
    linarith
  -- bound at σ + iγ
  have b1 : (Lf ((σ : ℂ) + γ * I)).re ≤ C * L - 1 / (σ - β) + 1 := by
    have h := Lf_upper (fun t s hs hz => hland t |>.2 s hs hz) (t := γ) hσ1 hσ2
    have hρF : ρ ∈ zball (ctr γ) := by
      rw [mem_zball]
      refine ⟨hρ, ?_⟩
      rw [mem_closedBall, dist_eq_norm]
      have : ρ - ctr γ = ((β - 6 / 5 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [ctr, β, γ]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hge := re_sum_ge (s := (σ : ℂ) + γ * I) hρF (fun u hu => by
      have := Z_re_lt_one (mem_zball.1 hu).1
      simp; linarith)
    have hval : (((mult ρ : ℝ) : ℂ) / (((σ : ℂ) + γ * I) - ρ)).re = mult ρ / (σ - β) := by
      have : ((σ : ℂ) + γ * I) - ρ = ((σ - β : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [β, γ]
      rw [this, ← ofReal_div, ofReal_re]
    have hm1 : (1 : ℝ) ≤ mult ρ := by exact_mod_cast mult_pos hρ
    have hσβ : 0 < σ - β := by linarith
    have hm : 1 / (σ - β) ≤ mult ρ / (σ - β) := by gcongr
    have hpole : (1 / (((σ : ℂ) + γ * I) - 1)).re ≤ 1 := by
      have : ((σ : ℂ) + γ * I) - 1 = δ + γ * I := by simp [σ]; ring
      rw [this, one_div, inv_re, normSq_apply]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add]
      rw [div_le_one (by nlinarith)]
      have : 1 ≤ γ * γ := by nlinarith [abs_mul_abs_self γ]
      nlinarith
    push_cast at hge hval
    linarith
  -- bound at σ + 2iγ
  have b2 : (Lf ((σ : ℂ) + 2 * γ * I)).re ≤ 2 * C * L + 1 := by
    have h := Lf_upper (fun t s hs hz => hland t |>.2 s hs hz) (t := 2 * γ) hσ1 hσ2
    have hsum : 0 ≤ (∑ u ∈ zball (ctr (2 * γ)), (mult u : ℂ) /
        (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - u)).re := by
      rw [re_sum]
      refine Finset.sum_nonneg fun u hu => re_div_nonneg (Nat.cast_nonneg _) ?_
      have := Z_re_lt_one (mem_zball.1 hu).1
      simp; linarith
    have hpole : (1 / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 1)).re ≤ 1 := by
      have : ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 1 = δ + ((2 * γ : ℝ) : ℂ) * I := by
        simp [σ]; ring
      rw [this, one_div, inv_re, normSq_apply]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add]
      rw [div_le_one (by nlinarith)]
      have : 1 ≤ γ * γ := by nlinarith [abs_mul_abs_self γ]
      nlinarith
    have hlog : Real.log (|2 * γ| + 3) ≤ 2 * L := by
      rw [hLdef, ← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show ((|γ| + 3) ^ (2 : ℝ)) = (|γ| + 3) * (|γ| + 3) by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add (by positivity)]; simp]
      rw [abs_mul]; norm_num; nlinarith [abs_nonneg γ]
    have : (((2 * γ : ℝ) : ℂ)) = 2 * (γ : ℂ) := by push_cast; ring
    rw [this] at h hsum hpole
    have hC2 := mul_le_mul_of_nonneg_left hlog hC.le
    linarith
  -- combine
  have hcomb : 0 ≤ 3 * (C * Real.log 3 + 1 / δ) + 4 * (C * L - 1 / (σ - β) + 1) +
      (2 * C * L + 1) := by
    have e : (3 * Lf σ + 4 * Lf (σ + γ * I) + Lf (σ + 2 * γ * I)).re =
        3 * (Lf ((σ : ℂ) + (0 : ℝ) * I)).re + 4 * (Lf ((σ : ℂ) + γ * I)).re +
          (Lf ((σ : ℂ) + 2 * γ * I)).re := by
      simp
    linarith
  have hσβ : 0 < σ - β := by linarith
  have h4 : 4 / (σ - β) ≤ 25 * K * L := by
    have e1 : 1 / δ = 8 * K * L := by rw [hδ]; field_simp
    have e2 : 4 * (1 / (σ - β)) = 4 / (σ - β) := by ring
    have : 3 * (C * Real.log 3) + 4 * (C * L) + 4 + 2 * C * L + 1 ≤ K * L := by
      have hh := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 3 * C * Real.log 3)
      rw [hK]; nlinarith
    linarith
  have h5 : 4 / (25 * K * L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hσβ] at h4
    linarith
  have h6 : c / L ≤ 7 / (200 * K * L) := by
    rw [show 7 / (200 * K * L) = 7 / (200 * K) / L by field_simp]
    gcongr
  have h7 : σ = 1 + 1 / (8 * K * L) := rfl
  have h8 : 4 / (25 * K * L) - 1 / (8 * K * L) = 7 / (200 * K * L) := by field_simp; ring
  linarith

/-! ### Total zero count -/

theorem zset_finite (σ T : ℝ) : {s : ℂ | Z s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T}.Finite := by
  have hK : IsCompact ((Icc σ 1) ×ℂ (Icc (-T) T)) := isCompact_Icc.reProdIm isCompact_Icc
  apply (Z_zeros_finite hK).subset
  intro s ⟨hz, hσ, hT⟩
  refine ⟨hz, ?_⟩
  rw [mem_reProdIm]
  exact ⟨⟨hσ, (Z_re_lt_one hz).le⟩, abs_le.1 hT⟩

/-- Zeros of `Z` with `Re ≥ σ` and `|Im| ≤ T`. -/
def zbox (σ T : ℝ) : Finset ℂ := (zset_finite σ T).toFinset

theorem mem_zbox {σ T : ℝ} {s : ℂ} : s ∈ zbox σ T ↔ Z s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T := by
  simp [zbox]

/-- Number of zeros (with multiplicity) with `Re ≥ σ`, `|Im| ≤ T`. -/
def Ncount (σ T : ℝ) : ℝ := ∑ ρ ∈ zbox σ T, (mult ρ : ℝ)

theorem sum_biUnion_le' {ι : Type*} [DecidableEq ι] (K : Finset ι) (t : ι → Finset ℂ)
    (f : ℂ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ K.biUnion t, f x ≤ ∑ k ∈ K, ∑ x ∈ t k, f x := by
  induction K using Finset.induction_on with
  | empty => simp
  | insert a K haK ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert haK]
    have h := Finset.sum_union_inter (s₁ := t a) (s₂ := K.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ x ∈ t a ∩ K.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

theorem count_total' : ∃ C : ℝ, ∀ T : ℝ, 3 ≤ T → Ncount (7 / 10) T ≤ C * T ^ 2 := by
  obtain ⟨C, hC, hland⟩ := landau
  refine ⟨30 * C, fun T hT => ?_⟩
  set N : ℕ := ⌈5 * T⌉₊ + 1
  set K : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hsub : zbox (7 / 10) T ⊆ K.biUnion (fun k => zball (ctr (k / 5))) := by
    intro ρ hρ
    rw [mem_zbox] at hρ
    obtain ⟨hz, hre, him⟩ := hρ
    rw [Finset.mem_biUnion]
    refine ⟨round (5 * ρ.im), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have h1 := abs_sub_round (5 * ρ.im)
      have h2 : (5 * ρ.im) ≤ 5 * T := by linarith [le_abs_self ρ.im]
      have h3 : -(5 * T) ≤ 5 * ρ.im := by linarith [neg_abs_le ρ.im]
      have h4 : 5 * T ≤ (⌈5 * T⌉₊ : ℝ) := Nat.le_ceil _
      rw [abs_le] at h1
      constructor
      · have : (-(N : ℤ) : ℝ) ≤ (round (5 * ρ.im) : ℝ) := by push_cast [N]; linarith
        exact_mod_cast this
      · have : (round (5 * ρ.im) : ℝ) ≤ (N : ℤ) := by push_cast [N]; linarith
        exact_mod_cast this
    · rw [mem_zball]
      refine ⟨hz, ?_⟩
      rw [mem_closedBall, dist_eq_norm]
      have h1 := abs_sub_round (5 * ρ.im)
      have hβ := Z_re_lt_one hz
      set k := round (5 * ρ.im)
      have hk : |ρ.im - (k : ℝ) / 5| ≤ 1 / 10 := by
        have : ρ.im - (k : ℝ) / 5 = (5 * ρ.im - k) / 5 := by ring
        rw [this, abs_div]; norm_num; linarith
      have hn : ‖ρ - ctr ((k : ℝ) / 5)‖ ^ 2 ≤ (11 / 20) ^ 2 := by
        rw [Complex.sq_norm, normSq_apply]
        simp only [sub_re, sub_im, ctr_re, ctr_im]
        have h5 : (ρ.im - (k : ℝ) / 5) ^ 2 ≤ (1 / 10) ^ 2 := by
          exact sq_le_sq' (by linarith [(abs_le.1 hk).1]) (abs_le.1 hk).2
        nlinarith
      have : ‖ρ - ctr ((k : ℝ) / 5)‖ ≤ 11 / 20 := by
        nlinarith [norm_nonneg (ρ - ctr ((k : ℝ) / 5))]
      simpa using this
  have hL : ∀ k ∈ K, Real.log (|(k : ℝ) / 5| + 3) ≤ T + 3 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk' : |(k : ℝ)| ≤ N := by
      rw [abs_le]; constructor <;> [exact_mod_cast hk.1; exact_mod_cast hk.2]
    have hN : (N : ℝ) ≤ 5 * T + 2 := by
      have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 5 * T)
      push_cast [N]; linarith
    have : |(k : ℝ) / 5| + 3 ≤ T + 4 := by
      rw [abs_div]; norm_num; linarith
    calc Real.log (|(k : ℝ) / 5| + 3) ≤ (|(k : ℝ) / 5| + 3) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ T + 3 := by linarith
  have hcard : (K.card : ℝ) ≤ 10 * T + 5 := by
    have : K.card = 2 * N + 1 := by
      simp only [K, Int.card_Icc]; omega
    rw [this]; push_cast
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 5 * T)
    simp only [N]; push_cast; linarith
  calc Ncount (7 / 10) T ≤ ∑ ρ ∈ K.biUnion (fun k => zball (ctr (k / 5))), (mult ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    _ ≤ ∑ k ∈ K, ∑ ρ ∈ zball (ctr (k / 5)), (mult ρ : ℝ) :=
        sum_biUnion_le' K _ _ (fun _ => Nat.cast_nonneg _)
    _ ≤ ∑ k ∈ K, C * (T + 3) := by
        apply Finset.sum_le_sum
        intro k hk
        have h := (hland ((k : ℝ) / 5)).1
        push_cast at h ⊢
        exact h.trans (mul_le_mul_of_nonneg_left (hL k hk) hC.le)
    _ = K.card * (C * (T + 3)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (10 * T + 5) * (C * (T + 3)) := by gcongr
    _ ≤ 30 * C * T ^ 2 := by
        have : (10 * T + 5) * (T + 3) ≤ 30 * T ^ 2 := by nlinarith
        nlinarith


/-! ## Rectangle integrals -/
/-- Boundary integral of `f` over the rectangle `[x0,x1] × [y0,y1]` (counterclockwise). -/
noncomputable def RI (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x : ℝ in x0..x1, f (x + y0 * I)) - (∫ x : ℝ in x0..x1, f (x + y1 * I)) +
    I * (∫ y : ℝ in y0..y1, f (x1 + y * I)) - I * (∫ y : ℝ in y0..y1, f (x0 + y * I))

theorem RI_eq_zero {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (H : DifferentiableOn ℂ f ([[x0, x1]] ×ℂ [[y0, y1]])) : RI f x0 x1 y0 y1 = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x0 + y0 * I)
    (x1 + y1 * I) (by simpa using H)
  simpa [RI, smul_eq_mul] using this

theorem integral_b_div_sq_add_sq {a b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in (-a)..a, b / (x ^ 2 + b ^ 2) = 2 * Real.arctan (a / b) := by
  have hd : ∀ x ∈ [[-a, a]], HasDerivAt (fun x => Real.arctan (x / b)) (b / (x ^ 2 + b ^ 2)) x := by
    intro x _
    have h1 := (Real.hasDerivAt_arctan (x / b)).comp x ((hasDerivAt_id x).div_const b)
    have hb' : b ≠ 0 := hb.ne'
    have h2 : (1 / (1 + (x / b) ^ 2) * (1 / b)) = b / (x ^ 2 + b ^ 2) := by
      field_simp; ring
    rw [h2] at h1; exact h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [neg_div, Real.arctan_neg]; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x _; positivity

theorem inv_sub_inv_horiz (x b : ℝ) (hb : 0 < b) :
    ((x : ℂ) + (-b : ℝ) * I)⁻¹ - ((x : ℂ) + b * I)⁻¹ = 2 * I * ((b / (x ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have h1 : ((x : ℂ) + (-b : ℝ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have h2 : ((x : ℂ) + b * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have h3 : ((x : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + b ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hp : ((x : ℂ) + (-b : ℝ) * I) * ((x : ℂ) + b * I) = (x : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [inv_sub_inv h1 h2, hp, div_eq_iff h3]
  push_cast
  field_simp
  ring

theorem inv_sub_inv_vert (y a : ℝ) (ha : 0 < a) :
    I * ((a : ℂ) + y * I)⁻¹ - I * (((-a : ℝ) : ℂ) + y * I)⁻¹ =
      2 * I * ((a / (y ^ 2 + a ^ 2) : ℝ) : ℂ) := by
  have h1 : ((a : ℂ) + y * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (((-a : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : ((y : ℂ) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < y ^ 2 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hp : ((a : ℂ) + y * I) * (((-a : ℝ) : ℂ) + y * I) = -((y : ℂ) ^ 2 + (a : ℂ) ^ 2) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [← mul_sub, inv_sub_inv h1 h2, hp]
  push_cast
  field_simp
  ring

theorem ii_inv_horiz {c : ℝ} (hc : c ≠ 0) (x0 x1 : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + c * I)⁻¹) volume x0 x1 := by
  apply Continuous.intervalIntegrable
  exact Continuous.inv₀ (by fun_prop) (fun x h => by
    have := congrArg Complex.im h; simp at this; exact hc this)

theorem ii_inv_vert {c : ℝ} (hc : c ≠ 0) (y0 y1 : ℝ) :
    IntervalIntegrable (fun y : ℝ => ((c : ℂ) + y * I)⁻¹) volume y0 y1 := by
  apply Continuous.intervalIntegrable
  exact Continuous.inv₀ (by fun_prop) (fun x h => by
    have := congrArg Complex.re h; simp at this; exact hc this)

theorem RI_inv_sym {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    RI (fun z => z⁻¹) (-a) a (-b) b = 2 * Real.pi * I := by
  unfold RI
  have e1 : (∫ x : ℝ in (-a)..a, ((x : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹) -
      (∫ x : ℝ in (-a)..a, ((x : ℂ) + (b : ℂ) * I)⁻¹)
      = 2 * I * (((2 * Real.arctan (a / b)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_sub (ii_inv_horiz (by linarith) _ _)
      (ii_inv_horiz hb.ne' _ _)]
    simp_rw [inv_sub_inv_horiz _ _ hb]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_b_div_sq_add_sq hb]
  have e2 : I * (∫ y : ℝ in (-b)..b, ((a : ℂ) + y * I)⁻¹) -
      I * (∫ y : ℝ in (-b)..b, (((-a : ℝ) : ℂ) + y * I)⁻¹)
      = 2 * I * (((2 * Real.arctan (b / a)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((ii_inv_vert ha.ne' _ _).const_mul _)
        ((ii_inv_vert (by linarith) _ _).const_mul _)]
    simp_rw [inv_sub_inv_vert _ _ ha]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_b_div_sq_add_sq ha]
  have hsplit : ∀ p q r t : ℂ, p - q + r - t = (p - q) + (r - t) := fun _ _ _ _ => by ring
  rw [hsplit, e1, e2]
  have hab : b / a = (a / b)⁻¹ := by rw [inv_div]
  rw [hab, Real.arctan_inv_of_pos (div_pos ha hb)]
  push_cast
  ring

/-- Integrability of `f` on the four sides of a rectangle. -/
def RIable (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume x0 x1 ∧
  IntervalIntegrable (fun x : ℝ => f (x + y1 * I)) volume x0 x1 ∧
  IntervalIntegrable (fun y : ℝ => f (x1 + y * I)) volume y0 y1 ∧
  IntervalIntegrable (fun y : ℝ => f (x0 + y * I)) volume y0 y1

theorem RIable_of_contOn {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hf : ContinuousOn f ([[x0, x1]] ×ℂ [[y0, y1]] \ {0}))
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) : RIable f x0 x1 y0 y1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable <;>
    refine hf.comp (Continuous.continuousOn (by fun_prop)) ?_ <;> intro t ht <;>
    simp only [Set.mem_sdiff, mem_reProdIm, mem_singleton_iff] <;>
    refine ⟨⟨by simp [ht], by simp [ht]⟩, fun h => ?_⟩ <;>
    first
    | (have := congrArg Complex.im h; simp at this; tauto)
    | (have := congrArg Complex.re h; simp at this; tauto)

theorem RI_add {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hf : RIable f x0 x1 y0 y1)
    (hg : RIable g x0 x1 y0 y1) :
    RI (fun z => f z + g z) x0 x1 y0 y1 = RI f x0 x1 y0 y1 + RI g x0 x1 y0 y1 := by
  unfold RI
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem RI_sub {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hf : RIable f x0 x1 y0 y1)
    (hg : RIable g x0 x1 y0 y1) :
    RI (fun z => f z - g z) x0 x1 y0 y1 = RI f x0 x1 y0 y1 - RI g x0 x1 y0 y1 := by
  unfold RI
  rw [intervalIntegral.integral_sub hf.1 hg.1, intervalIntegral.integral_sub hf.2.1 hg.2.1,
    intervalIntegral.integral_sub hf.2.2.1 hg.2.2.1, intervalIntegral.integral_sub hf.2.2.2 hg.2.2.2]
  ring

theorem RI_const_mul (k : ℂ) (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :
    RI (fun z => k * f z) x0 x1 y0 y1 = k * RI f x0 x1 y0 y1 := by
  unfold RI
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem RI_congr {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (h : ∀ z, z ≠ 0 → f z = g z)
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    RI f x0 x1 y0 y1 = RI g x0 x1 y0 y1 := by
  unfold RI
  have e1 : ∀ c : ℝ, c ≠ 0 → ∀ x : ℝ, f (x + c * I) = g (x + c * I) := fun c hc x =>
    h _ (fun h' => by have := congrArg Complex.im h'; simp at this; exact hc this)
  have e2 : ∀ c : ℝ, c ≠ 0 → ∀ y : ℝ, f (c + y * I) = g (c + y * I) := fun c hc y =>
    h _ (fun h' => by have := congrArg Complex.re h'; simp at this; exact hc this)
  simp only [e1 _ hy0, e1 _ hy1, e2 _ hx0, e2 _ hx1]

theorem RI_split {f : ℂ → ℂ} {x0 m x1 y0 y1 : ℝ}
    (h1 : IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume x0 m)
    (h2 : IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume m x1)
    (h3 : IntervalIntegrable (fun x : ℝ => f (x + y1 * I)) volume x0 m)
    (h4 : IntervalIntegrable (fun x : ℝ => f (x + y1 * I)) volume m x1) :
    RI f x0 x1 y0 y1 = RI f x0 m y0 y1 + RI f m x1 y0 y1 := by
  unfold RI
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  ring

theorem RI_inv {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) :
    RI (fun z => z⁻¹) (-a) c (-b) b = 2 * Real.pi * I := by
  rw [RI_split (m := a) (ii_inv_horiz (by simp; linarith) _ _) (ii_inv_horiz (by simp; linarith) _ _)
    (ii_inv_horiz hb.ne' _ _) (ii_inv_horiz hb.ne' _ _), RI_inv_sym ha hb, RI_eq_zero, add_zero]
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_inv
  intro h
  rw [mem_reProdIm, h] at hz
  simp [uIcc_of_le hac] at hz
  linarith [hz.1]

theorem RI_pole {H : ℂ → ℂ} {V : Set ℂ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c)
    (hV : IsOpen V) (hR : [[-a, c]] ×ℂ [[-b, b]] ⊆ V) (hH : DifferentiableOn ℂ H V) :
    RI (fun z => H z / z) (-a) c (-b) b = 2 * Real.pi * I * H 0 := by
  have h0 : (0 : ℂ) ∈ V := hR (by
    simp only [mem_reProdIm, zero_re, zero_im]
    exact ⟨mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩),
      mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)⟩)
  have hg : DifferentiableOn ℂ (dslope H 0) V :=
    (differentiableOn_dslope (hV.mem_nhds h0)).mpr hH
  have hx0 : (-a) ≠ 0 := by linarith
  have hx1 : c ≠ 0 := by linarith
  have hy0 : (-b) ≠ 0 := by linarith
  have hy1 : b ≠ 0 := by linarith
  have hcongr : RI (fun z => H z / z) (-a) c (-b) b =
      RI (fun z => dslope H 0 z + H 0 * z⁻¹) (-a) c (-b) b := by
    apply RI_congr _ hx0 hx1 hy0 hy1
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_field]
    field_simp
    ring
  have hgc : ContinuousOn (dslope H 0) ([[-a, c]] ×ℂ [[-b, b]] \ {0}) :=
    hg.continuousOn.mono (sdiff_subset.trans hR)
  have hic : ContinuousOn (fun z : ℂ => H 0 * z⁻¹) ([[-a, c]] ×ℂ [[-b, b]] \ {0}) := by
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_inv₀.mono (fun z hz => hz.2)
  rw [hcongr, RI_add (RIable_of_contOn hgc hx0 hx1 hy0 hy1) (RIable_of_contOn hic hx0 hx1 hy0 hy1),
    RI_const_mul, RI_inv ha hb hac, RI_eq_zero (hg.mono hR)]
  ring

/-! ### General rectangles -/

/-- `z` lies on the boundary of `[x0,x1] × [y0,y1]`. -/
def OnBdry (z : ℂ) (x0 x1 y0 y1 : ℝ) : Prop :=
  (z.re ∈ [[x0, x1]] ∧ (z.im = y0 ∨ z.im = y1)) ∨ (z.im ∈ [[y0, y1]] ∧ (z.re = x0 ∨ z.re = x1))

theorem RIable_of_bdry {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hf : ∀ z, OnBdry z x0 x1 y0 y1 → ContinuousAt f z) : RIable f x0 x1 y0 y1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable <;> intro t ht <;>
    apply ContinuousAt.continuousWithinAt <;> apply ContinuousAt.comp _ (by fun_prop) <;>
    apply hf <;> simp [OnBdry, ht]

theorem RI_congr_bdry {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (h : ∀ z, OnBdry z x0 x1 y0 y1 → f z = g z) : RI f x0 x1 y0 y1 = RI g x0 x1 y0 y1 := by
  unfold RI
  have e1 : ∫ x : ℝ in x0..x1, f (x + y0 * I) = ∫ x : ℝ in x0..x1, g (x + y0 * I) :=
    intervalIntegral.integral_congr fun t ht => h _ (by simp [OnBdry, ht])
  have e2 : ∫ x : ℝ in x0..x1, f (x + y1 * I) = ∫ x : ℝ in x0..x1, g (x + y1 * I) :=
    intervalIntegral.integral_congr fun t ht => h _ (by simp [OnBdry, ht])
  have e3 : ∫ y : ℝ in y0..y1, f (x1 + y * I) = ∫ y : ℝ in y0..y1, g (x1 + y * I) :=
    intervalIntegral.integral_congr fun t ht => h _ (by simp [OnBdry, ht])
  have e4 : ∫ y : ℝ in y0..y1, f (x0 + y * I) = ∫ y : ℝ in y0..y1, g (x0 + y * I) :=
    intervalIntegral.integral_congr fun t ht => h _ (by simp [OnBdry, ht])
  rw [e1, e2, e3, e4]

theorem RI_splitY {f : ℂ → ℂ} {x0 x1 y0 m y1 : ℝ}
    (h1 : IntervalIntegrable (fun y : ℝ => f (x1 + y * I)) volume y0 m)
    (h2 : IntervalIntegrable (fun y : ℝ => f (x1 + y * I)) volume m y1)
    (h3 : IntervalIntegrable (fun y : ℝ => f (x0 + y * I)) volume y0 m)
    (h4 : IntervalIntegrable (fun y : ℝ => f (x0 + y * I)) volume m y1) :
    RI f x0 x1 y0 y1 = RI f x0 x1 y0 m + RI f x0 x1 m y1 := by
  unfold RI
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  ring

theorem RI_translate (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) (u : ℂ) :
    RI f x0 x1 y0 y1 =
      RI (fun z => f (z + u)) (x0 - u.re) (x1 - u.re) (y0 - u.im) (y1 - u.im) := by
  unfold RI
  have hx : ∀ c : ℝ, (∫ x : ℝ in (x0 - u.re)..(x1 - u.re), f (x + (c - u.im) * I + u)) =
      ∫ x : ℝ in x0..x1, f (x + c * I) := by
    intro c
    rw [← intervalIntegral.integral_comp_sub_right (fun x : ℝ => f (x + (c - u.im) * I + u)) u.re]
    congr 1; funext x
    congr 1
    apply Complex.ext <;> simp
  have hy : ∀ c : ℝ, (∫ y : ℝ in (y0 - u.im)..(y1 - u.im), f ((c - u.re : ℝ) + y * I + u)) =
      ∫ y : ℝ in y0..y1, f (c + y * I) := by
    intro c
    rw [← intervalIntegral.integral_comp_sub_right (fun y : ℝ => f ((c - u.re : ℝ) + y * I + u)) u.im]
    congr 1; funext y
    congr 1
    apply Complex.ext <;> simp
  have hx' := hx y0
  have hx'' := hx y1
  have hy' := hy x0
  have hy'' := hy x1
  push_cast at hx' hx'' hy' hy'' ⊢
  rw [hx', hx'', hy', hy'']

theorem inv_contAt {z : ℂ} (h : z ≠ 0) : ContinuousAt (fun z : ℂ => z⁻¹) z :=
  continuousAt_inv₀ h

theorem RI_inv_gen {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    RI (fun z => z⁻¹) (-a) c (-b) d = 2 * Real.pi * I := by
  set e := min (min a c) (min b d) with he
  have he0 : 0 < e := lt_min (lt_min ha hc) (lt_min hb hd)
  have hea : e ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hec : e ≤ c := (min_le_left _ _).trans (min_le_right _ _)
  have heb : e ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hed : e ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  have hdiff : ∀ {p q r s : ℝ}, (0 ∉ [[p, q]] ×ℂ [[r, s]]) →
      RI (fun z => z⁻¹) p q r s = 0 := by
    intro p q r s h0
    apply RI_eq_zero
    intro z hz
    exact (differentiableAt_inv (fun h => h0 (h ▸ hz))).differentiableWithinAt
  have hH : ∀ y : ℝ, y ≠ 0 → ∀ p q : ℝ,
      IntervalIntegrable (fun x : ℝ => ((x : ℂ) + y * I)⁻¹) volume p q :=
    fun y hy p q => ii_inv_horiz hy p q
  have hV : ∀ x : ℝ, x ≠ 0 → ∀ p q : ℝ,
      IntervalIntegrable (fun y : ℝ => ((x : ℂ) + y * I)⁻¹) volume p q :=
    fun x hx p q => ii_inv_vert hx p q
  have hb0 : (-b) ≠ 0 := by linarith
  have hd0 : d ≠ 0 := by linarith
  have he0' : e ≠ 0 := he0.ne'
  have hme0 : (-e) ≠ 0 := by linarith
  rw [RI_split (m := -e) (hH _ hb0 _ _) (hH _ hb0 _ _) (hH _ hd0 _ _) (hH _ hd0 _ _),
    RI_split (x0 := -e) (m := e) (hH _ hb0 _ _) (hH _ hb0 _ _) (hH _ hd0 _ _) (hH _ hd0 _ _),
    RI_splitY (m := -e) (hV _ he0' _ _) (hV _ he0' _ _) (hV _ hme0 _ _) (hV _ hme0 _ _),
    RI_splitY (y0 := -e) (m := e) (hV _ he0' _ _) (hV _ he0' _ _) (hV _ hme0 _ _)
      (hV _ hme0 _ _),
    RI_inv_sym he0 he0]
  have z1 : RI (fun z => z⁻¹) (-a) (-e) (-b) d = 0 := hdiff (by
    intro h; rw [mem_reProdIm] at h; simp [uIcc_of_le (by linarith : -a ≤ -e)] at h; linarith)
  have z2 : RI (fun z => z⁻¹) e c (-b) d = 0 := hdiff (by
    intro h; rw [mem_reProdIm] at h; simp [uIcc_of_le hec] at h; linarith)
  have z3 : RI (fun z => z⁻¹) (-e) e (-b) (-e) = 0 := hdiff (by
    intro h; rw [mem_reProdIm] at h; simp [uIcc_of_le (by linarith : -b ≤ -e)] at h; linarith)
  have z4 : RI (fun z => z⁻¹) (-e) e e d = 0 := hdiff (by
    intro h; rw [mem_reProdIm] at h; simp [uIcc_of_le hed] at h; linarith)
  rw [z1, z2, z3, z4]
  ring

theorem RI_pole_gen {H : ℂ → ℂ} {V : Set ℂ} {x0 x1 y0 y1 : ℝ} {u : ℂ}
    (hx0 : x0 < u.re) (hx1 : u.re < x1) (hy0 : y0 < u.im) (hy1 : u.im < y1)
    (hV : IsOpen V) (hR : [[x0, x1]] ×ℂ [[y0, y1]] ⊆ V) (hH : DifferentiableOn ℂ H V) :
    RI (fun z => H z / (z - u)) x0 x1 y0 y1 = 2 * Real.pi * I * H u := by
  have huV : u ∈ V := hR (by
    rw [mem_reProdIm]
    exact ⟨mem_uIcc.2 (Or.inl ⟨hx0.le, hx1.le⟩), mem_uIcc.2 (Or.inl ⟨hy0.le, hy1.le⟩)⟩)
  have hg : DifferentiableOn ℂ (dslope H u) V :=
    (differentiableOn_dslope (hV.mem_nhds huV)).2 hH
  have hne : ∀ z, OnBdry z x0 x1 y0 y1 → z ≠ u := by
    intro z hz hzu
    subst hzu
    rcases hz with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> linarith
  have hcongr : RI (fun z => H z / (z - u)) x0 x1 y0 y1 =
      RI (fun z => dslope H u z + H u * (z - u)⁻¹) x0 x1 y0 y1 := by
    apply RI_congr_bdry
    intro z hz
    have h1 : z - u ≠ 0 := sub_ne_zero.2 (hne z hz)
    rw [dslope_of_ne _ (hne z hz), slope_def_field]
    field_simp
    ring
  have hR1 : RIable (dslope H u) x0 x1 y0 y1 := RIable_of_bdry fun z hz => by
    have : z ∈ V := hR (by
      rw [mem_reProdIm]
      rcases hz with ⟨h1, h | h⟩ | ⟨h1, h | h⟩ <;> simp_all [left_mem_uIcc, right_mem_uIcc])
    exact (hg.differentiableAt (hV.mem_nhds this)).continuousAt
  have hR2 : RIable (fun z => H u * (z - u)⁻¹) x0 x1 y0 y1 := RIable_of_bdry fun z hz =>
    (continuousAt_const.mul ((continuous_id.sub continuous_const).continuousAt.inv₀
      (sub_ne_zero.2 (hne z hz))))
  rw [hcongr, RI_add hR1 hR2, RI_eq_zero (hg.mono hR), RI_const_mul, zero_add]
  rw [RI_translate (fun z => (z - u)⁻¹) x0 x1 y0 y1 u]
  simp only [add_sub_cancel_right]
  have := RI_inv_gen (a := u.re - x0) (b := u.im - y0) (c := x1 - u.re) (d := y1 - u.im)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [neg_sub, neg_sub] at this
  rw [this]
  ring

/-! ## Shared definitions for the explicit formula -/

/-- `log⁺`. -/
def lp (y : ℝ) : ℝ := max (Real.log y) 0

/-- Trapezoid-in-log weight supported on `(x, x(1+δ)^4)`. -/
def gw (x δ u : ℝ) : ℝ :=
  lp (x * (1 + δ) ^ 4 / u) - lp (x * (1 + δ) ^ 3 / u) - lp (x * (1 + δ) / u) + lp (x / u)

/-- The Mellin transform of `gw`: `(x₃^s - x₂^s - x₁^s + x₀^s)/s²`. -/
def Wk (x δ : ℝ) (s : ℂ) : ℂ :=
  (((x * (1 + δ) ^ 4 : ℝ) : ℂ) ^ s - ((x * (1 + δ) ^ 3 : ℝ) : ℂ) ^ s -
    ((x * (1 + δ) : ℝ) : ℂ) ^ s + ((x : ℝ) : ℂ) ^ s) / s ^ 2

/-- Normalised Gamma-type weight `Λ(n)/n · (η log n)^k e^{-η log n} / k!`. -/
def wt (η : ℝ) (k n : ℕ) : ℂ :=
  (((ArithmeticFunction.vonMangoldt n : ℝ) / n * (η * Real.log n) ^ k *
    Real.exp (-(η * Real.log n)) / (k.factorial : ℝ) : ℝ) : ℂ)



-- ===== from HT.lean =====


namespace HT

open Polynomial

/-! ### Node lemma -/

lemma node_exists (S : Finset ℂ) (a : ℂ → ℝ) (hn : 1 ≤ S.card) :
    ∃ k : ℕ, k ≤ S.card ∧
      (S.card.factorial : ℝ) / (4 * S.card) ^ S.card ≤
        ∏ z ∈ S, |(1 / 2 + (k : ℝ) / (2 * S.card)) - a z| := by
  set n := S.card with hn_def
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ := 1 / (2 * n) with hh
  have hpos : 0 < h := by positivity
  set P : ℝ[X] := ∏ z ∈ S, (C h * X + C (1 / 2 - a z)) with hPdef
  have hP : ∀ x : ℝ, P.eval x = ∏ z ∈ S, (h * x + (1 / 2 - a z)) := by
    intro x; simp [P, eval_prod]
  have hdeg : P.natDegree = n := by
    rw [hPdef, natDegree_prod _ _ (fun i _ => ?_)]
    · rw [Finset.sum_congr rfl (fun i _ => natDegree_linear (b := 1 / 2 - a i) hpos.ne')]
      simp [n]
    · intro h0
      have := natDegree_linear (b := 1 / 2 - a i) hpos.ne'
      rw [h0] at this; simp at this
  have hlead : P.leadingCoeff = h ^ n := by
    rw [hPdef, leadingCoeff_prod,
      Finset.prod_congr rfl (fun i _ => leadingCoeff_linear (b := 1 / 2 - a i) hpos.ne'),
      Finset.prod_const]
  have key := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial P) 0
  rw [hdeg, fwdDiff_iter_eq_sum_shift, hlead] at key
  simp only [Pi.smul_apply, zero_add, smul_eq_mul, zsmul_eq_mul, Pi.natCast_apply] at key
  by_contra hcon
  push Not at hcon
  set M : ℝ := (n.factorial : ℝ) / (4 * n) ^ n with hM
  have hbound : ∀ k ∈ Finset.range (n + 1), |(((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) : ℤ) : ℝ) *
      P.eval (k • (1 : ℝ))| < (n.choose k : ℝ) * M := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    rw [abs_mul]
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    refine mul_lt_mul_of_pos_left ?_ hc
    rw [hP, Finset.abs_prod, nsmul_eq_mul, mul_one]
    convert hcon k hkn using 2 with z hz
    rw [hh]; ring_nf
  have hsum := Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hbound
  have h2 := (Finset.abs_sum_le_sum_abs _ _).trans_lt hsum
  rw [← Finset.sum_mul] at h2
  have hch : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hch] at h2
  have : ∑ x ∈ Finset.range (n + 1), (((-1 : ℤ) ^ (n - x) * (n.choose x : ℤ) : ℤ) : ℝ) *
      P.eval (x • (1 : ℝ)) = h ^ n * (n.factorial : ℝ) := by
    exact_mod_cast key
  rw [this, abs_of_pos (by positivity)] at h2
  have e : (2 : ℝ) ^ n * M = h ^ n * n.factorial := by
    have h2n : (2 : ℝ) * n ≠ 0 := by positivity
    rw [hM, hh, show (4 : ℝ) * n = 2 * (2 * n) by ring, mul_pow, div_pow, one_pow]
    field_simp
  linarith

lemma fact_bound (n : ℕ) : (1 / 11 : ℝ) ^ n ≤ (n.factorial : ℝ) / (4 * n) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hnp.le n
  have he : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have he1 := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hf : (0 : ℝ) < n.factorial := by positivity
  rw [div_le_iff₀ hf, he] at h1
  rw [le_div_iff₀ (by positivity), mul_pow, ← mul_assoc, ← mul_pow]
  calc (1 / 11 * 4 : ℝ) ^ n * (n : ℝ) ^ n ≤ (1 / 11 * 4) ^ n * (Real.exp 1 ^ n * n.factorial) := by
        gcongr
    _ = ((1 / 11 * 4) * Real.exp 1) ^ n * n.factorial := by ring
    _ ≤ 1 ^ n * n.factorial := by
        gcongr
        linarith
    _ = n.factorial := by simp

/-! ### Coefficient bound -/

lemma sum_coeff_X_mul (P : ℂ[X]) (K : ℕ) :
    ∑ m ∈ Finset.range K, ‖(X * P).coeff m‖ ≤ ∑ m ∈ Finset.range K, ‖P.coeff m‖ := by
  cases K with
  | zero => simp
  | succ K =>
    have h := Finset.sum_range_succ' (fun m => ‖(X * P).coeff m‖) K
    rw [h]
    simp only [coeff_X_mul, mul_coeff_zero, coeff_X_zero, zero_mul, norm_zero, add_zero]
    rw [Finset.sum_range_succ]
    linarith [norm_nonneg (P.coeff K)]

lemma l1_prod (S : Finset ℂ) (hS : ∀ y ∈ S, ‖y‖ ≤ 1) (K : ℕ) :
    ∑ m ∈ Finset.range K, ‖(∏ y ∈ S, (X - C y)).coeff m‖ ≤ 2 ^ S.card := by
  induction S using Finset.induction_on generalizing K with
  | empty =>
    rcases K with _ | K
    · simp
    · rw [Finset.sum_range_succ']; simp [coeff_one]
  | insert y S hy ih =>
    rw [Finset.prod_insert hy, Finset.card_insert_of_notMem hy, pow_succ]
    have ih' := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hy1 : ‖y‖ ≤ 1 := hS y (Finset.mem_insert_self y S)
    set P := ∏ y ∈ S, (X - C y)
    have e : ∀ m, ((X - C y) * P).coeff m = (X * P).coeff m - y * P.coeff m := by
      intro m; rw [sub_mul, coeff_sub, coeff_C_mul]
    have hP0 : 0 ≤ ∑ m ∈ Finset.range K, ‖P.coeff m‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc ∑ m ∈ Finset.range K, ‖((X - C y) * P).coeff m‖
        ≤ ∑ m ∈ Finset.range K, (‖(X * P).coeff m‖ + ‖y‖ * ‖P.coeff m‖) := by
          gcongr with m
          rw [e, ← norm_mul]; exact norm_sub_le _ _
      _ = ∑ m ∈ Finset.range K, ‖(X * P).coeff m‖ +
            ‖y‖ * ∑ m ∈ Finset.range K, ‖P.coeff m‖ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ m ∈ Finset.range K, ‖P.coeff m‖ + 1 * ∑ m ∈ Finset.range K, ‖P.coeff m‖ := by
          exact add_le_add (sum_coeff_X_mul P K) (mul_le_mul_of_nonneg_right hy1 hP0)
      _ ≤ 2 ^ S.card * 2 := by linarith [ih' K]

lemma eval_div_identity (F : ℂ[X]) (n : ℕ) (hF : F.natDegree < n + 1) (z w : ℂ)
    (hz : F.eval z = 0) :
    F.eval w = (w - z) *
      ∑ m ∈ Finset.range (n + 1), F.coeff m * ∑ l ∈ Finset.range m, z ^ l * w ^ (m - 1 - l) := by
  have h1 := eval_eq_sum_range' hF w
  have h2 := eval_eq_sum_range' hF z
  rw [Finset.mul_sum]
  have : F.eval w = F.eval w - F.eval z := by rw [hz, sub_zero]
  rw [this, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_left_comm, (Commute.all z w).mul_neg_geom_sum₂ m]; ring

/-! ### The circle integral -/

def gz (N : ℕ) (z w : ℂ) : ℂ := z ^ (N + 1) * ((w ^ (N + 1))⁻¹ * (w - z)⁻¹)

lemma gz_decomp_aux (M : ℕ) (z w : ℂ) (hw : w ≠ 0) (hwz : w - z ≠ 0) :
    z ^ M * ((w ^ M)⁻¹ * (w - z)⁻¹) =
      (w - z)⁻¹ - ∑ j ∈ Finset.range M, z ^ j * (w ^ (j + 1))⁻¹ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ← ih]
    field_simp
    ring

lemma gz_decomp (N : ℕ) (z w : ℂ) (hw : w ≠ 0) (hwz : w - z ≠ 0) :
    gz N z w = (w - z)⁻¹ - ∑ j ∈ Finset.range (N + 1), z ^ j * (w - 0) ^ (-(j : ℤ) - 1) := by
  rw [gz, gz_decomp_aux _ _ _ hw hwz]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_zero, show -(j : ℤ) - 1 = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

lemma gz_continuousOn (N : ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ ≠ r) :
    ContinuousOn (gz N z) (sphere 0 r) := by
  have hne0 : ∀ w ∈ sphere (0 : ℂ) r, w ^ (N + 1) ≠ 0 := by
    intro w hw
    have : ‖w‖ = r := by simpa using hw
    refine pow_ne_zero _ ?_
    rintro rfl; simp at this; linarith
  have hnez : ∀ w ∈ sphere (0 : ℂ) r, w - z ≠ 0 := by
    intro w hw h
    have : ‖w‖ = r := by simpa using hw
    rw [sub_eq_zero] at h; subst h; exact hzr this
  unfold gz
  exact continuousOn_const.mul (((continuousOn_id.pow _).inv₀ hne0).mul
    ((continuousOn_id.sub continuousOn_const).inv₀ hnez))

lemma integral_zpow_center (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (∮ w in C(0, r), (w - 0) ^ (-(j : ℤ) - 1)) = if j = 0 then 2 * Real.pi * I else 0 := by
  split_ifs with hj
  · subst hj
    simp only [Nat.cast_zero, neg_zero, zero_sub, zpow_neg_one]
    exact circleIntegral.integral_sub_center_inv 0 hr.ne'
  · exact circleIntegral.integral_sub_zpow_of_ne (by omega) _ _ _

lemma integral_inv_sub (z : ℂ) {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ ≠ r) :
    (∮ w in C(0, r), (w - z)⁻¹) = if ‖z‖ < r then 2 * Real.pi * I else 0 := by
  split_ifs with h
  · exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h)
  · have h' : r < ‖z‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hzr)
    refine DiffContOnCl.circleIntegral_eq_zero hr.le ?_
    refine DifferentiableOn.diffContOnCl_ball (U := closedBall 0 r) ?_ subset_rfl
    refine (differentiableOn_id.sub_const z).inv fun w hw h0 => ?_
    have h0' : w = z := by simpa [sub_eq_zero] using h0
    have : ‖w‖ ≤ r := by simpa using hw
    rw [h0'] at this; linarith

lemma zpow_contOn (z : ℂ) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ContinuousOn (fun w : ℂ => z ^ j * (w - 0) ^ (-(j : ℤ) - 1)) (sphere 0 r) := by
  refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _ ?_)
  intro w hw; left
  have : ‖w‖ = r := by simpa using hw
  intro h
  have hw0 : w = 0 := by simpa using h
  subst hw0; simp at this; linarith

lemma integral_gz (N : ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ ≠ r) :
    (∮ w in C(0, r), gz N z w) = 2 * Real.pi * I * ((if ‖z‖ < r then 1 else 0) - 1) := by
  have hcongr : EqOn (gz N z) (fun w => (w - z)⁻¹ -
      ∑ j ∈ Finset.range (N + 1), z ^ j * (w - 0) ^ (-(j : ℤ) - 1)) (sphere 0 r) := by
    intro w hw
    have hw' : ‖w‖ = r := by simpa using hw
    apply gz_decomp
    · rintro rfl; simp at hw'; linarith
    · intro h; rw [sub_eq_zero] at h; subst h; exact hzr hw'
  rw [circleIntegral.integral_congr hr.le hcongr]
  have hint1 : CircleIntegrable (fun w => (w - z)⁻¹) 0 r := by
    rw [circleIntegrable_sub_inv_iff]; right
    rw [abs_of_pos hr]; simpa using hzr
  have hint2 : ∀ j ∈ Finset.range (N + 1),
      CircleIntegrable (fun w => z ^ j * (w - 0) ^ (-(j : ℤ) - 1)) 0 r :=
    fun j _ => ContinuousOn.circleIntegrable hr.le (zpow_contOn z hr j)
  have hint3 : CircleIntegrable (fun w => ∑ j ∈ Finset.range (N + 1),
      z ^ j * (w - 0) ^ (-(j : ℤ) - 1)) 0 r :=
    ContinuousOn.circleIntegrable hr.le
      (continuousOn_finsetSum _ fun j _ => zpow_contOn z hr j)
  rw [circleIntegral.integral_sub hint1 hint3, circleIntegral.integral_fun_sum hint2,
    integral_inv_sub z hr hzr]
  simp only [circleIntegral.integral_const_mul, integral_zpow_center r hr]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, mul_zero, Finset.sum_const_zero, zero_add,
    if_true, pow_zero, one_mul]
  split_ifs <;> ring

/-! ### Assembly -/

lemma prod_bound_sphere (S : Finset ℂ) {r : ℝ} (w : ℂ) (hw : ‖w‖ = r) :
    ∏ z ∈ S, |r - ‖z‖| ≤ ‖∏ z ∈ S, (w - z)‖ := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun z _ => ?_
  rw [← hw]; exact abs_norm_sub_norm_le w z

lemma sum_swap (S : Finset ℂ) (b : ℂ → ℝ) (N n : ℕ) (f : ℕ → ℂ) (w : ℂ) :
    ∑ z ∈ S, (b z : ℂ) * z ^ (N + 1) *
        ∑ m ∈ Finset.range (n + 1), f m * ∑ l ∈ Finset.range m, z ^ l * w ^ (m - 1 - l) =
      ∑ m ∈ Finset.range (n + 1), f m * ∑ l ∈ Finset.range m,
        w ^ (m - 1 - l) * ∑ z ∈ S, (b z : ℂ) * z ^ (N + 1 + l) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun z _ => ?_
  ring

lemma H_bound (n : ℕ) (f : ℕ → ℂ) (w : ℂ) (hw : ‖w‖ ≤ 1) (s : ℕ → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hs : ∀ l < n, ‖s l‖ ≤ E) (hf : ∑ m ∈ Finset.range (n + 1), ‖f m‖ ≤ 2 ^ n) :
    ‖∑ m ∈ Finset.range (n + 1), f m * ∑ l ∈ Finset.range m, w ^ (m - 1 - l) * s l‖ ≤
      n * 2 ^ n * E := by
  have hin : ∀ m ∈ Finset.range (n + 1),
      ‖f m * ∑ l ∈ Finset.range m, w ^ (m - 1 - l) * s l‖ ≤ ‖f m‖ * (n * E) := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖∑ l ∈ Finset.range m, w ^ (m - 1 - l) * s l‖
        ≤ ∑ l ∈ Finset.range m, ‖w ^ (m - 1 - l) * s l‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.range m, E := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l < n := lt_of_lt_of_le (Finset.mem_range.mp hl) hmn
          rw [norm_mul, norm_pow]
          calc ‖w‖ ^ (m - 1 - l) * ‖s l‖ ≤ 1 * E := by
                gcongr
                · exact pow_le_one₀ (norm_nonneg _) hw
                · exact hs l hl'
            _ = E := one_mul E
      _ = m * E := by simp
      _ ≤ n * E := by gcongr
  calc _ ≤ ∑ m ∈ Finset.range (n + 1), ‖f m * ∑ l ∈ Finset.range m, w ^ (m - 1 - l) * s l‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (n + 1), ‖f m‖ * (n * E) := Finset.sum_le_sum hin
    _ = (∑ m ∈ Finset.range (n + 1), ‖f m‖) * (n * E) := by rw [Finset.sum_mul]
    _ ≤ 2 ^ n * (n * E) := by gcongr
    _ = n * 2 ^ n * E := by ring

lemma G_pointwise (S : Finset ℂ) (b : ℂ → ℝ) (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hS1 : ∀ z ∈ S, ‖z‖ ≤ 1) (hzr : ∀ z ∈ S, ‖z‖ ≠ r) (E : ℝ) (hE : 0 ≤ E)
    (hs : ∀ l < S.card, ‖∑ z ∈ S, (b z : ℂ) * z ^ (N + 1 + l)‖ ≤ E)
    (hPr0 : 0 < ∏ z ∈ S, |r - ‖z‖|) (w : ℂ) (hw : ‖w‖ = r) :
    ‖∑ z ∈ S, (b z : ℂ) * gz N z w‖ ≤
      (r ^ (N + 1))⁻¹ * (∏ z ∈ S, |r - ‖z‖|)⁻¹ * (S.card * 2 ^ S.card * E) := by
  set n := S.card with hn
  set F : ℂ[X] := ∏ y ∈ S, (X - C y) with hF
  have hFdeg : F.natDegree < n + 1 := by
    refine lt_of_le_of_lt (natDegree_prod_le _ _) ?_
    simp [n]
  have hFz : ∀ z ∈ S, F.eval z = 0 := by
    intro z hz
    rw [hF, eval_prod]
    exact Finset.prod_eq_zero hz (by simp)
  have hFw : F.eval w = ∏ y ∈ S, (w - y) := by rw [hF, eval_prod]; simp
  have hFn : ∏ z ∈ S, |r - ‖z‖| ≤ ‖F.eval w‖ := by rw [hFw]; exact prod_bound_sphere S w hw
  have hFw0 : F.eval w ≠ 0 := by
    intro h; rw [h, norm_zero] at hFn; linarith
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  set D : ℂ → ℂ := fun z => ∑ m ∈ Finset.range (n + 1), F.coeff m *
    ∑ l ∈ Finset.range m, z ^ l * w ^ (m - 1 - l) with hD
  have hgz : ∀ z ∈ S, (b z : ℂ) * gz N z w =
      (w ^ (N + 1))⁻¹ * (F.eval w)⁻¹ * ((b z : ℂ) * z ^ (N + 1) * D z) := by
    intro z hz
    have hwz : w - z ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; subst h; exact hzr _ hz hw
    have hid : F.eval w = (w - z) * D z := eval_div_identity F n hFdeg z w (hFz z hz)
    have hDz : D z ≠ 0 := by
      intro h; rw [h, mul_zero] at hid; exact hFw0 hid
    rw [gz, hid]
    field_simp
  rw [Finset.sum_congr rfl hgz, ← Finset.mul_sum, hD, sum_swap S b N n (fun m => F.coeff m) w]
  rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, hw]
  have hH := H_bound n (fun m => F.coeff m) w (hw.le.trans hr1)
    (fun l => ∑ z ∈ S, (b z : ℂ) * z ^ (N + 1 + l)) E hE hs (l1_prod S hS1 (n + 1))
  have hinv : ‖F.eval w‖⁻¹ ≤ (∏ z ∈ S, |r - ‖z‖|)⁻¹ := inv_anti₀ hPr0 hFn
  exact mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) hH (norm_nonneg _)
    (by positivity)

lemma core (S : Finset ℂ) (b : ℂ → ℝ) (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hS1 : ∀ z ∈ S, ‖z‖ ≤ 1) (hb : ∀ z ∈ S, 1 ≤ b z) (hzr : ∀ z ∈ S, ‖z‖ ≠ r)
    (z0 : ℂ) (hz0S : z0 ∈ S) (hz0 : r < ‖z0‖) (E : ℝ)
    (hs : ∀ l < S.card, ‖∑ z ∈ S, (b z : ℂ) * z ^ (N + 1 + l)‖ ≤ E) :
    r ^ N * ∏ z ∈ S, |r - ‖z‖| ≤ S.card * 2 ^ S.card * E := by
  have hn1 : 0 < S.card := Finset.card_pos.mpr ⟨z0, hz0S⟩
  have hE : 0 ≤ E := (norm_nonneg _).trans (hs 0 hn1)
  have hPr0 : 0 < ∏ z ∈ S, |r - ‖z‖| :=
    Finset.prod_pos fun z hz => abs_pos.mpr (sub_ne_zero.mpr (hzr z hz).symm)
  set T : ℝ := ∑ z ∈ S, b z * ((if ‖z‖ < r then 1 else 0) - 1) with hT
  have hI : (∮ w in C(0, r), ∑ z ∈ S, (b z : ℂ) * gz N z w) = 2 * Real.pi * I * (T : ℂ) := by
    rw [circleIntegral.integral_fun_sum (f := fun z w => (b z : ℂ) * gz N z w) (fun z hz => ContinuousOn.circleIntegrable hr0.le
      (continuousOn_const.mul (gz_continuousOn N z hr0 (hzr z hz))))]
    simp only [circleIntegral.integral_const_mul]
    rw [hT]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [integral_gz N z hr0 (hzr z hz)]
    split_ifs <;> push_cast <;> ring
  have hTle : T ≤ -1 := by
    have hle : ∀ z ∈ S, b z * ((if ‖z‖ < r then 1 else 0) - 1) ≤ 0 := by
      intro z hz
      have := hb z hz
      split_ifs <;> nlinarith
    rw [hT, ← Finset.add_sum_erase S _ hz0S, if_neg (not_lt.mpr hz0.le)]
    have h1 := Finset.sum_nonpos (s := S.erase z0) fun z (hz : z ∈ S.erase z0) => hle z (Finset.mem_of_mem_erase hz)
    have h2 := hb z0 hz0S
    linarith
  have hnorm : ‖∮ w in C(0, r), ∑ z ∈ S, (b z : ℂ) * gz N z w‖ = 2 * Real.pi * |T| := by
    rw [hI, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  have hup := circleIntegral.norm_integral_le_of_norm_le_const
    (f := fun w => ∑ z ∈ S, (b z : ℂ) * gz N z w) (c := 0) hr0.le
    (fun w hw => G_pointwise S b N hr0 hr1 hS1 hzr E hE hs hPr0 w (by simpa using hw))
  rw [hnorm] at hup
  have hT1 : 1 ≤ |T| := by rw [abs_of_neg (by linarith)]; linarith
  have hpi := Real.pi_pos
  set Pr := ∏ z ∈ S, |r - ‖z‖|
  set K : ℝ := S.card * 2 ^ S.card * E
  have h1 : 1 ≤ r * ((r ^ (N + 1))⁻¹ * Pr⁻¹ * K) := by nlinarith
  have e : r * ((r ^ (N + 1))⁻¹ * Pr⁻¹ * K) = K / (r ^ N * Pr) := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity), one_mul] at h1
  exact h1

end HT

theorem turan : ∃ c : ℝ, 0 < c ∧ ∀ (S : Finset ℂ) (b : ℂ → ℝ) (N : ℕ), S.card ≤ N →
    (∀ z ∈ S, ‖z‖ ≤ 1) → (∀ z ∈ S, 1 ≤ b z) → (∃ z ∈ S, ‖z‖ = 1) →
    ∃ ν : ℕ, N + 1 ≤ ν ∧ ν ≤ 2 * N ∧ c ^ N ≤ ‖∑ z ∈ S, (b z : ℂ) * z ^ ν‖ := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro S b N hSN hS1 hb hex
  obtain ⟨z0, hz0S, hz0⟩ := hex
  have hn1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨z0, hz0S⟩
  obtain ⟨k, hk, hprod⟩ := HT.node_exists S (fun z => ‖z‖) hn1
  set n := S.card with hn
  set r : ℝ := 1 / 2 + (k : ℝ) / (2 * n) with hr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hr12 : 1 / 2 ≤ r := by
    have : 0 ≤ (k : ℝ) / (2 * n) := by positivity
    linarith
  have hr1 : r ≤ 1 := by
    have : (k : ℝ) / (2 * n) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (k : ℝ) ≤ n := by exact_mod_cast hk
      linarith
    linarith
  have hPr : (1 / 11 : ℝ) ^ n ≤ ∏ z ∈ S, |r - ‖z‖| := (HT.fact_bound n).trans hprod
  have hPr0 : 0 < ∏ z ∈ S, |r - ‖z‖| := lt_of_lt_of_le (by positivity) hPr
  have hzr : ∀ z ∈ S, ‖z‖ ≠ r := by
    intro z hz h
    have := Finset.prod_eq_zero (f := fun z => |r - ‖z‖|) hz (show |r - ‖z‖| = 0 by rw [h, sub_self, abs_zero])
    linarith
  have hr1' : r < 1 := lt_of_le_of_ne hr1 (fun h => hzr z0 hz0S (hz0.trans h.symm))
  by_contra hcon
  push Not at hcon
  have hs : ∀ l < n, ‖∑ z ∈ S, (b z : ℂ) * z ^ (N + 1 + l)‖ ≤ (1 / 100 : ℝ) ^ N := by
    intro l hl
    exact (hcon (N + 1 + l) (by omega) (by omega)).le
  have hcore := HT.core S b N (by linarith) hr1 hS1 hb hzr z0 hz0S (by rw [hz0]; exact hr1') _ hs
  have h1 : (1 / 2 : ℝ) ^ N * (1 / 11) ^ n ≤ n * 2 ^ n * (1 / 100) ^ N := by
    calc (1 / 2 : ℝ) ^ N * (1 / 11) ^ n ≤ r ^ N * ∏ z ∈ S, |r - ‖z‖| := by gcongr
      _ ≤ _ := hcore
  have hn2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h44 : (1 / 44 : ℝ) ^ N ≤ (1 / 44) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hSN
  have e : (1 / 11 : ℝ) ^ n = (1 / 44) ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
  have h3 : (1 / 2 : ℝ) ^ N * (1 / 44) ^ n * 4 ^ n ≤ (1 / 100) ^ N * 4 ^ n := by
    calc _ = (1 / 2 : ℝ) ^ N * (1 / 11) ^ n := by rw [e]; ring
      _ ≤ n * 2 ^ n * (1 / 100) ^ N := h1
      _ ≤ 2 ^ n * 2 ^ n * (1 / 100) ^ N := by gcongr
      _ = (1 / 100) ^ N * 4 ^ n := by rw [← mul_pow]; norm_num; ring
  have h4 : (1 / 2 : ℝ) ^ N * (1 / 44) ^ n ≤ (1 / 100) ^ N :=
    le_of_mul_le_mul_right h3 (by positivity)
  have h5 : (1 / 2 * (1 / 44) : ℝ) ^ N ≤ (1 / 100) ^ N := by
    rw [mul_pow]
    calc _ ≤ (1 / 2 : ℝ) ^ N * (1 / 44) ^ n := by gcongr
      _ ≤ _ := h4
  have hN : N ≠ 0 := by omega
  have := pow_lt_pow_left₀ (show (1 / 100 : ℝ) < 1 / 2 * (1 / 44) by norm_num) (by norm_num) hN
  linarith



-- ===== from HM.lean =====


namespace HM

open Finset


/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- Distance to the nearest integer. -/
noncomputable def dist1 (x : ℝ) : ℝ := |x - round x|

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (k : ℤ) : e k = 1 := by
  unfold e
  rw [show (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_add_int (x : ℝ) (k : ℤ) : e (x + k) = e x := by
  rw [e_add, e_int, mul_one]

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [show (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast; ring

lemma e_nat_mul (n : ℕ) (x : ℝ) : e (n * x) = e x ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma dist1_nonneg (x : ℝ) : 0 ≤ dist1 x := abs_nonneg _

lemma dist1_le (x : ℝ) (k : ℤ) : dist1 x ≤ |x - k| := round_le x k

lemma dist1_le_half (x : ℝ) : dist1 x ≤ 1 / 2 := abs_sub_round x

lemma dist1_neg (x : ℝ) : dist1 (-x) = dist1 x := by
  apply le_antisymm
  · have := dist1_le (-x) (-round x)
    rw [show -x - ((-round x : ℤ) : ℝ) = -(x - round x) by push_cast; ring, abs_neg] at this
    exact this
  · have := dist1_le x (-round (-x))
    rw [show x - ((-round (-x) : ℤ) : ℝ) = -(-x - round (-x)) by push_cast; ring, abs_neg] at this
    exact this

lemma dist1_sub_comm (x y : ℝ) : dist1 (x - y) = dist1 (y - x) := by
  rw [← dist1_neg, neg_sub]

/-- `|e(x) - 1| ≥ 4 ‖x‖`. -/
lemma four_dist1_le_norm_e_sub_one (x : ℝ) : 4 * dist1 x ≤ ‖e x - 1‖ := by
  set t := x - round x with ht
  have hx : e x = e t := by
    rw [ht, show x - (round x : ℝ) = x + ((-round x : ℤ) : ℝ) by push_cast; ring, e_add_int]
  have ht2 : |t| ≤ 1 / 2 := abs_sub_round x
  have hnorm : ‖e t - 1‖ = ‖2 * Real.sin (Real.pi * t)‖ := by
    unfold e
    rw [show (2 * Real.pi * Complex.I * (t : ℂ)) = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one]
    congr 2; ring_nf
  rw [hx, hnorm, Real.norm_eq_abs, abs_mul, abs_two]
  unfold dist1
  rw [← ht]
  have hpi := Real.pi_pos
  rcases le_total 0 t with h0 | h0
  · have h1 : 0 ≤ Real.pi * t := by positivity
    have h2 : Real.pi * t ≤ Real.pi / 2 := by
      rw [abs_of_nonneg h0] at ht2; nlinarith
    have := Real.mul_le_sin h1 h2
    rw [abs_of_nonneg h0, abs_of_nonneg (le_trans (mul_nonneg (by positivity) h1) this)]
    have : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    linarith
  · have h1 : 0 ≤ Real.pi * (-t) := by nlinarith
    have h2 : Real.pi * (-t) ≤ Real.pi / 2 := by
      rw [abs_of_nonpos h0] at ht2; nlinarith
    have := Real.mul_le_sin h1 h2
    rw [show Real.pi * (-t) = -(Real.pi * t) by ring, Real.sin_neg] at this
    have hs : 0 ≤ -Real.sin (Real.pi * t) :=
      le_trans (mul_nonneg (by positivity) (by linarith : 0 ≤ -(Real.pi * t))) this
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith)]
    have : 2 / Real.pi * -(Real.pi * t) = 2 * (-t) := by field_simp
    linarith

/-- Geometric sum bound `|∑_{m<A} e(mx)| ≤ 1/(2‖x‖)`. -/
lemma norm_sum_e_le (A : ℕ) (x : ℝ) (hx : 0 < dist1 x) :
    ‖∑ m ∈ range A, e (m * x)‖ ≤ 1 / (2 * dist1 x) := by
  have h4 := four_dist1_le_norm_e_sub_one x
  have hne : e x - 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at h4; linarith
  have hne' : e x ≠ 1 := sub_ne_zero.mp hne
  simp_rw [e_nat_mul]
  rw [geom_sum_eq hne', norm_div]
  have hnum : ‖e x ^ A - 1‖ ≤ 2 := by
    calc ‖e x ^ A - 1‖ ≤ ‖e x ^ A‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hpos : 0 < ‖e x - 1‖ := by linarith
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-! ### Counting separated points -/

lemma sum_inv_sq_nat_le (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i) :
    ∑ i ∈ s, ((i : ℝ) ^ 2)⁻¹ ≤ 2 := by
  set K := s.sup id
  have hsub : s ⊆ Ioo 0 (K + 1) := by
    intro i hi
    rw [Finset.mem_Ioo]
    exact ⟨hs i hi, Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
  calc ∑ i ∈ s, ((i : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Ioo 0 (K + 1), ((i : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / ((0 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 0 (K + 1)
    _ = 2 := by norm_num

/-- Points `t_s ≥ δ`, pairwise `δ`-separated: `∑ 1/t_s² ≤ 2/δ²`. -/
lemma sum_inv_sq_sep {ι : Type*} (S : Finset ι) (t : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hpos : ∀ s ∈ S, δ ≤ t s)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → δ ≤ |t s - t s'|) :
    ∑ s ∈ S, 1 / t s ^ 2 ≤ 2 / δ ^ 2 := by
  set k : ι → ℕ := fun s => ⌊t s / δ⌋₊ with hk
  have hk1 : ∀ s ∈ S, 1 ≤ k s := by
    intro s hs
    have : (1 : ℝ) ≤ t s / δ := by rw [le_div_iff₀ hδ]; linarith [hpos s hs]
    exact Nat.le_floor (by exact_mod_cast this)
  have hkle : ∀ s ∈ S, (k s : ℝ) * δ ≤ t s := by
    intro s hs
    have h0 : 0 ≤ t s / δ := div_nonneg (by linarith [hpos s hs]) hδ.le
    have := Nat.floor_le h0
    rw [le_div_iff₀ hδ] at this
    exact this
  have hinj : Set.InjOn k S := by
    intro s hs s' hs' hss
    by_contra hne
    have h1 := Nat.floor_le (div_nonneg (by linarith [hpos s hs]) hδ.le : 0 ≤ t s / δ)
    have h2 := Nat.lt_floor_add_one (t s / δ)
    have h3 := Nat.floor_le (div_nonneg (by linarith [hpos s' hs']) hδ.le : 0 ≤ t s' / δ)
    have h4 := Nat.lt_floor_add_one (t s' / δ)
    have hkk : (⌊t s / δ⌋₊ : ℝ) = ⌊t s' / δ⌋₊ := by exact_mod_cast hss
    have hlt : |t s / δ - t s' / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have := hsep s hs s' hs' hne
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hlt
    linarith
  have hterm : ∀ s ∈ S, 1 / t s ^ 2 ≤ (1 / δ ^ 2) * ((k s : ℝ) ^ 2)⁻¹ := by
    intro s hs
    have hk0 : (0 : ℝ) < k s := by exact_mod_cast hk1 s hs
    have hkd := hkle s hs
    have hpos' : 0 < (k s : ℝ) * δ := by positivity
    have : ((k s : ℝ) * δ) ^ 2 ≤ t s ^ 2 := pow_le_pow_left₀ hpos'.le hkd 2
    calc 1 / t s ^ 2 ≤ 1 / ((k s : ℝ) * δ) ^ 2 := one_div_le_one_div_of_le (by positivity) this
      _ = (1 / δ ^ 2) * ((k s : ℝ) ^ 2)⁻¹ := by rw [mul_pow]; field_simp
  calc ∑ s ∈ S, 1 / t s ^ 2 ≤ ∑ s ∈ S, (1 / δ ^ 2) * ((k s : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (1 / δ ^ 2) * ∑ i ∈ S.image k, ((i : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
    _ ≤ (1 / δ ^ 2) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_inv_sq_nat_le
        intro i hi
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
        exact hk1 s hs
    _ = 2 / δ ^ 2 := by ring

/-- Separated points on the circle: `∑_{s ≠ r} 1/‖x_r - x_s‖² ≤ 4/δ²`. -/
lemma sum_inv_sq_dist1_le {ι : Type*} [DecidableEq ι] (R : Finset ι) (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → δ ≤ dist1 (x r - x s)) (r : ι)
    (hr : r ∈ R) :
    ∑ s ∈ R.erase r, 1 / dist1 (x r - x s) ^ 2 ≤ 4 / δ ^ 2 := by
  set t : ι → ℝ := fun s => (x s - x r) - round (x s - x r) with ht
  have habs : ∀ s, dist1 (x r - x s) = |t s| := by
    intro s; rw [dist1_sub_comm]; rfl
  have hge : ∀ s ∈ R.erase r, δ ≤ |t s| := by
    intro s hs
    rw [← habs]
    obtain ⟨hne, hs'⟩ := Finset.mem_erase.mp hs
    exact hsep r hr s hs' (Ne.symm hne)
  have hsep' : ∀ s ∈ R.erase r, ∀ s' ∈ R.erase r, s ≠ s' → δ ≤ |t s - t s'| := by
    intro s hs s' hs' hne
    have h1 := hsep s (Finset.mem_of_mem_erase hs) s' (Finset.mem_of_mem_erase hs') hne
    have h2 := dist1_le (x s - x s') (round (x s - x r) - round (x s' - x r))
    have : t s - t s' = (x s - x s') - (((round (x s - x r) - round (x s' - x r) : ℤ)) : ℝ) := by
      simp only [ht]; push_cast; ring
    rw [this]; linarith
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun s => 0 < t s)]
  have hP : ∑ s ∈ (R.erase r).filter (fun s => 0 < t s), 1 / dist1 (x r - x s) ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((R.erase r).filter (fun s => 0 < t s)) t δ hδ
      (by
        intro s hs
        obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
        have := hge s hs1; rwa [abs_of_pos hs2] at this)
      (by
        intro s hs s' hs' hne
        exact hsep' s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1 hne)
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro s hs
    rw [habs, abs_of_pos (Finset.mem_filter.mp hs).2]
  have hN : ∑ s ∈ (R.erase r).filter (fun s => ¬ 0 < t s), 1 / dist1 (x r - x s) ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((R.erase r).filter (fun s => ¬ 0 < t s)) (fun s => - t s) δ hδ
      (by
        intro s hs
        obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
        have := hge s hs1; rwa [abs_of_nonpos (not_lt.mp hs2)] at this)
      (by
        intro s hs s' hs' hne
        have := hsep' s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1 hne
        rwa [show -t s - -t s' = -(t s - t s') by ring, abs_neg])
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro s hs
    rw [habs, abs_of_nonpos (not_lt.mp (Finset.mem_filter.mp hs).2)]
  have h4 : 4 / δ ^ 2 = 2 / δ ^ 2 + 2 / δ ^ 2 := by ring
  linarith

/-! ### The dual inequality -/

/-- The trapezoid kernel `K(θ) = ∑_{j<H} ∑_{m<A} e((M+m-j)θ)`. -/
noncomputable def kernel (M : ℤ) (A H : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ range H, ∑ m ∈ range A, e (((M + m - j : ℤ) : ℝ) * θ)

lemma norm_kernel_le_triv (M : ℤ) (A H : ℕ) (θ : ℝ) : ‖kernel M A H θ‖ ≤ H * A := by
  unfold kernel
  calc ‖∑ j ∈ range H, ∑ m ∈ range A, e (((M + m - j : ℤ) : ℝ) * θ)‖
      ≤ ∑ j ∈ range H, ‖∑ m ∈ range A, e (((M + m - j : ℤ) : ℝ) * θ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range H, ∑ m ∈ range A, ‖e (((M + m - j : ℤ) : ℝ) * θ)‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ = H * A := by simp [norm_e]

lemma norm_kernel_le (M : ℤ) (A H : ℕ) (θ : ℝ) (hθ : 0 < dist1 θ) :
    ‖kernel M A H θ‖ ≤ 1 / (4 * dist1 θ ^ 2) := by
  unfold kernel
  have hrw : ∀ j m : ℕ, e (((M + m - j : ℤ) : ℝ) * θ) =
      e (M * θ) * (e (m * θ) * e (j * (-θ))) := by
    intro j m; rw [← e_add, ← e_add]; congr 1; push_cast; ring
  simp_rw [hrw]
  have hfac : (∑ j ∈ range H, ∑ m ∈ range A, e (M * θ) * (e (m * θ) * e (j * (-θ)))) =
      e (M * θ) * ((∑ m ∈ range A, e (m * θ)) * ∑ j ∈ range H, e (j * (-θ))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  rw [hfac, norm_mul, norm_mul, norm_e, one_mul]
  have h1 := norm_sum_e_le A θ hθ
  have h2 := norm_sum_e_le H (-θ) (by rwa [dist1_neg])
  rw [dist1_neg] at h2
  calc ‖∑ m ∈ range A, e (m * θ)‖ * ‖∑ j ∈ range H, e (j * (-θ))‖
      ≤ (1 / (2 * dist1 θ)) * (1 / (2 * dist1 θ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 1 / (4 * dist1 θ ^ 2) := by field_simp; ring

lemma sum_sym_le {ι : Type*} (R : Finset ι) (u : ι → ℝ) (κ : ι → ι → ℝ)
    (hκ : ∀ r s, κ r s = κ s r) (hκ0 : ∀ r s, 0 ≤ κ r s) :
    ∑ r ∈ R, ∑ s ∈ R, u r * u s * κ r s ≤ ∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s := by
  have h2 : ∑ r ∈ R, ∑ s ∈ R, u s ^ 2 * κ r s = ∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => by rw [hκ]))
  calc ∑ r ∈ R, ∑ s ∈ R, u r * u s * κ r s
      ≤ ∑ r ∈ R, ∑ s ∈ R, (u r ^ 2 * κ r s / 2 + u s ^ 2 * κ r s / 2) := by
        apply Finset.sum_le_sum; intro r _; apply Finset.sum_le_sum; intro s _
        have := hκ0 r s
        nlinarith [sq_nonneg (u r - u s), mul_nonneg this (sq_nonneg (u r - u s))]
    _ = (∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s) / 2 + (∑ r ∈ R, ∑ s ∈ R, u s ^ 2 * κ r s) / 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s := by rw [h2]; ring

/-- **Dual large sieve** for `δ`-separated points. -/
theorem dual_large_sieve {ι : Type*} [DecidableEq ι] (R : Finset ι) (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → δ ≤ dist1 (x r - x s)) (M : ℤ) (N : ℕ)
    (b : ι → ℂ) :
    ∑ n ∈ range N, ‖∑ r ∈ R, b r * e (((M + n : ℤ) : ℝ) * x r)‖ ^ 2
      ≤ (N + 2 / δ) * ∑ r ∈ R, ‖b r‖ ^ 2 := by
  set T : ℤ → ℂ := fun t => ∑ r ∈ R, b r * e ((t : ℝ) * x r) with hT
  show ∑ n ∈ range N, ‖T (M + n)‖ ^ 2 ≤ (N + 2 / δ) * ∑ r ∈ R, ‖b r‖ ^ 2
  set H := ⌈1 / δ⌉₊ with hHdef
  have hH1 : 1 ≤ H := Nat.ceil_pos.mpr (by positivity)
  have hHge : 1 / δ ≤ H := Nat.le_ceil _
  have hHlt : (H : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  set A := N + H - 1 with hAdef
  have hAcast : (A : ℝ) = N + H - 1 := by
    rw [hAdef, Nat.cast_sub (by omega)]; push_cast; ring
  set X := ∑ n ∈ range N, ‖T (M + n)‖ ^ 2 with hX
  set B := ∑ r ∈ R, ‖b r‖ ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  -- step 1: averaging over shifts
  have step1 : (H : ℝ) * X ≤ ∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 := by
    have : (H : ℝ) * X = ∑ j ∈ range H, X := by simp
    rw [this]
    apply Finset.sum_le_sum
    intro j hj
    have hjH := Finset.mem_range.mp hj
    calc X = ∑ m ∈ Ico j (j + N), ‖T (M + m - j)‖ ^ 2 := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, hX]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          congr 3; push_cast; ring
      _ ≤ ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; rw [Finset.mem_Ico] at hm; rw [Finset.mem_range]; omega
          · intros; positivity
  -- step 2: expansion
  have hexp : ∀ t : ℤ, ((‖T t‖ ^ 2 : ℝ) : ℂ) = ∑ p ∈ R ×ˢ R,
      b p.1 * (starRingEnd ℂ) (b p.2) * e ((t : ℝ) * (x p.1 - x p.2)) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_product]
    simp only [hT, map_sum, map_mul, conj_e, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [show (t : ℝ) * (x r - x s) = t * x r + -(t * x s) by ring, e_add]; ring
  have step2 : ((∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ R ×ˢ R, b p.1 * (starRingEnd ℂ) (b p.2) * kernel M A H (x p.1 - x p.2) := by
    simp_rw [Complex.ofReal_sum, hexp, kernel, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  -- step 3: bound the kernel
  set κ : ι → ι → ℝ := fun r s => if r = s then (H : ℝ) * A else 1 / (4 * dist1 (x r - x s) ^ 2)
    with hκ
  have hκsym : ∀ r s, κ r s = κ s r := by
    intro r s
    simp only [hκ]
    by_cases h : r = s
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), dist1_sub_comm]
  have hκ0 : ∀ r s, 0 ≤ κ r s := by
    intro r s; simp only [hκ]; split_ifs <;> positivity
  have hK : ∀ r ∈ R, ∀ s ∈ R, ‖kernel M A H (x r - x s)‖ ≤ κ r s := by
    intro r hr s hs
    simp only [hκ]
    split_ifs with h
    · exact norm_kernel_le_triv M A H _
    · exact norm_kernel_le M A H _ (lt_of_lt_of_le hδ (hsep r hr s hs h))
  have step3 : ∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 ≤
      ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * κ r s := by
    set Y := ∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2
    calc Y ≤ ‖(Y : ℂ)‖ := by rw [Complex.norm_real]; exact le_abs_self _
      _ = ‖∑ p ∈ R ×ˢ R, b p.1 * (starRingEnd ℂ) (b p.2) * kernel M A H (x p.1 - x p.2)‖ := by
          rw [step2]
      _ ≤ ∑ p ∈ R ×ˢ R, ‖b p.1 * (starRingEnd ℂ) (b p.2) * kernel M A H (x p.1 - x p.2)‖ :=
          norm_sum_le _ _
      _ = ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * ‖kernel M A H (x r - x s)‖ := by
          rw [Finset.sum_product]; simp
      _ ≤ ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * κ r s := by
          apply Finset.sum_le_sum; intro r hr; apply Finset.sum_le_sum; intro s hs
          exact mul_le_mul_of_nonneg_left (hK r hr s hs) (by positivity)
  have step4 : ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * κ r s ≤ (H * A + 1 / δ ^ 2) * B := by
    refine (sum_sym_le R (fun r => ‖b r‖) κ hκsym hκ0).trans ?_
    rw [hB, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    rw [← Finset.mul_sum, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← Finset.add_sum_erase _ _ hr]
    have hrr : κ r r = H * A := by simp [hκ]
    have herase : ∑ s ∈ R.erase r, κ r s = (1 / 4) * ∑ s ∈ R.erase r, 1 / dist1 (x r - x s) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hne : r ≠ s := Ne.symm (Finset.ne_of_mem_erase hs)
      simp only [hκ, if_neg hne]
      field_simp
    rw [hrr, herase]
    have := sum_inv_sq_dist1_le R x δ hδ hsep r hr
    have h4 : (1 / 4 : ℝ) * (4 / δ ^ 2) = 1 / δ ^ 2 := by field_simp
    nlinarith
  -- step 5: conclude
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
  have hfin : (H : ℝ) * A + 1 / δ ^ 2 ≤ H * (N + 2 / δ) := by
    rw [hAcast]
    set d := 1 / δ with hd
    have hd2 : 1 / δ ^ 2 = d ^ 2 := by rw [hd]; field_simp
    have h2d : 2 / δ = 2 * d := by rw [hd]; ring
    rw [hd2, h2d]
    have hdpos : 0 < d := by rw [hd]; positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hHge) (by linarith : (0:ℝ) ≤ d + 1 - H)]
  have : (H : ℝ) * X ≤ H * ((N + 2 / δ) * B) := by
    calc (H : ℝ) * X ≤ (H * A + 1 / δ ^ 2) * B := step1.trans (step3.trans step4)
      _ ≤ (H * (N + 2 / δ)) * B := mul_le_mul_of_nonneg_right hfin hB0
      _ = H * ((N + 2 / δ) * B) := by ring
  exact le_of_mul_le_mul_left this hHpos

/-- **Analytic large sieve** for `δ`-separated points: for `F` inside an interval of `N`
consecutive integers, `∑_r |∑_{n∈F} c_n e(n x_r)|² ≤ (N + 2/δ) ∑_{n∈F} |c_n|²`. -/
theorem large_sieve_points {ι : Type*} [DecidableEq ι] (R : Finset ι) (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → δ ≤ dist1 (x r - x s)) (M N : ℕ)
    (F : Finset ℕ) (hF : F ⊆ Ico M (M + N)) (c : ℕ → ℂ) :
    ∑ r ∈ R, ‖∑ n ∈ F, c n * e (n * x r)‖ ^ 2 ≤ (N + 2 / δ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  set S : ι → ℂ := fun r => ∑ n ∈ F, c n * e (n * x r) with hS
  show ∑ r ∈ R, ‖S r‖ ^ 2 ≤ (N + 2 / δ) * ∑ n ∈ F, ‖c n‖ ^ 2
  set B := ∑ r ∈ R, ‖S r‖ ^ 2 with hB
  set C := ∑ n ∈ F, ‖c n‖ ^ 2 with hC
  set T : ℕ → ℂ := fun n => ∑ r ∈ R, (starRingEnd ℂ) (S r) * e (n * x r) with hT
  have hBC : (B : ℂ) = ∑ n ∈ F, c n * T n := by
    rw [hB, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hS, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => by ring)
  have hB0 : 0 ≤ B := by positivity
  have h1 : B ≤ ∑ n ∈ F, ‖c n‖ * ‖T n‖ := by
    calc B = ‖(B : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hB0]
      _ = ‖∑ n ∈ F, c n * T n‖ := by rw [hBC]
      _ ≤ ∑ n ∈ F, ‖c n * T n‖ := norm_sum_le _ _
      _ = ∑ n ∈ F, ‖c n‖ * ‖T n‖ := by simp
  have h2 : B ^ 2 ≤ C * ∑ n ∈ F, ‖T n‖ ^ 2 :=
    (pow_le_pow_left₀ hB0 h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ n ∈ F, ‖T n‖ ^ 2 ≤ (N + 2 / δ) * B := by
    calc ∑ n ∈ F, ‖T n‖ ^ 2 ≤ ∑ n ∈ Ico M (M + N), ‖T n‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hF (by intros; positivity)
      _ = ∑ i ∈ range N, ‖∑ r ∈ R, (starRingEnd ℂ) (S r) * e ((((M : ℤ) + i : ℤ) : ℝ) * x r)‖ ^ 2 := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hT]; push_cast; rfl
      _ ≤ (N + 2 / δ) * ∑ r ∈ R, ‖(starRingEnd ℂ) (S r)‖ ^ 2 :=
          dual_large_sieve R x δ hδ hsep M N _
      _ = (N + 2 / δ) * B := by simp [hB]
  have hK : 0 ≤ (N : ℝ) + 2 / δ := by positivity
  rcases hB0.lt_or_eq with hBpos | hBz
  · have : B * B ≤ (C * (N + 2 / δ)) * B := by
      calc B * B = B ^ 2 := by ring
        _ ≤ C * ((N + 2 / δ) * B) := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
        _ = (C * (N + 2 / δ)) * B := by ring
    have := le_of_mul_le_mul_right this hBpos
    linarith
  · rw [← hBz]; positivity

/-- Farey fractions `a/q`, `q ≤ Q`, `(a,q) = 1`, are `1/Q²`-separated. -/
lemma farey_sep (Q : ℕ) (q a q' a' : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a < q)
    (hc : a.Coprime q) (hq' : 1 ≤ q') (hqQ' : q' ≤ Q) (ha' : a' < q') (hc' : a'.Coprime q')
    (hne : ¬ (q = q' ∧ a = a')) :
    1 / (Q : ℝ) ^ 2 ≤ dist1 ((a : ℝ) / q - (a' : ℝ) / q') := by
  set k := round ((a : ℝ) / q - (a' : ℝ) / q')
  set z : ℤ := a * q' - a' * q - k * q * q' with hz
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hval : (a : ℝ) / q - (a' : ℝ) / q' - k = (z : ℝ) / (q * q') := by
    rw [hz]; push_cast; field_simp
  have hz0 : z ≠ 0 := by
    intro h0
    have hqdvd : (q : ℤ) ∣ (a : ℤ) * q' := ⟨a' + k * q', by rw [hz] at h0; linarith⟩
    have hqdvd' : (q' : ℤ) ∣ (a' : ℤ) * q := ⟨a - k * q, by rw [hz] at h0; linarith⟩
    have c1 : IsCoprime (q : ℤ) (a : ℤ) := (Nat.isCoprime_iff_coprime.mpr hc.symm)
    have c2 : IsCoprime (q' : ℤ) (a' : ℤ) := (Nat.isCoprime_iff_coprime.mpr hc'.symm)
    have d1 : (q : ℤ) ∣ q' := c1.dvd_of_dvd_mul_left hqdvd
    have d2 : (q' : ℤ) ∣ q := c2.dvd_of_dvd_mul_left hqdvd'
    have hqq : q = q' := Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp d1)
      (Int.natCast_dvd_natCast.mp d2)
    subst hqq
    have h2 : ((a : ℤ) - a' - k * q) * q = 0 := by rw [hz] at h0; linarith
    have h3 : (a : ℤ) - a' = k * q := by
      have := (mul_eq_zero.mp h2).resolve_right (by exact_mod_cast (by omega : q ≠ 0))
      linarith
    have hk : k = 0 := by
      have hlt1 : (a : ℤ) - a' < q := by omega
      have hlt2 : -(q : ℤ) < (a : ℤ) - a' := by omega
      rw [h3] at hlt1 hlt2
      have hqz : (0 : ℤ) < q := by exact_mod_cast hq
      by_contra hk0
      rcases lt_or_gt_of_ne hk0 with hkn | hkp
      · nlinarith
      · nlinarith
    rw [hk, zero_mul] at h3
    exact hne ⟨rfl, by omega⟩
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have := Int.one_le_abs hz0
    exact_mod_cast this
  unfold dist1
  rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  have hQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have : (q' : ℝ) ≤ Q := by exact_mod_cast hqQ'
    nlinarith
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- **Analytic large sieve, Farey form**:
`∑_{q ≤ Q} ∑_{a mod q, (a,q)=1} |∑_{n∈F} c_n e(an/q)|² ≤ (N + 2Q²) ∑ |c_n|²`
for `F` contained in `N` consecutive integers. -/
theorem large_sieve_farey (Q M N : ℕ) (F : Finset ℕ) (hF : F ⊆ Ico M (M + N)) (c : ℕ → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      ‖∑ n ∈ F, c n * e (n * ((a : ℝ) / q))‖ ^ 2 ≤ (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ; simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty]
    positivity
  set R := (Finset.Icc 1 Q).sigma (fun q => (range q).filter (fun a => a.Coprime q))
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have := large_sieve_points R (fun p => (p.2 : ℝ) / p.1) (1 / (Q : ℝ) ^ 2) (by positivity)
    (by
      rintro ⟨q, a⟩ hr ⟨q', a'⟩ hs hne
      simp only [R, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hr hs
      apply farey_sep Q q a q' a' hr.1.1 hr.1.2 hr.2.1 hr.2.2 hs.1.1 hs.1.2 hs.2.1 hs.2.2
      rintro ⟨rfl, rfl⟩; exact hne rfl) M N F hF c
  rw [Finset.sum_sigma] at this
  have h2 : 2 / (1 / (Q : ℝ) ^ 2) = 2 * (Q : ℝ) ^ 2 := by field_simp
  rw [h2] at this
  exact this

/-! ### Montgomery's lemma and the arithmetic large sieve -/

/-- Reduced residues `0 ≤ a < q`, `(a,q) = 1`. -/
def U (q : ℕ) : Finset ℕ := (range q).filter (fun a => a.Coprime q)

lemma card_U (q : ℕ) : (U q).card = Nat.totient q := by
  rw [Nat.totient_eq_card_coprime, U]
  congr 1
  apply Finset.filter_congr
  intro a _
  exact Nat.coprime_comm

/-- Orthogonality: `∑_{a<p} e(a(b-b')/p) = p·[b = b']` for `b, b' < p`. -/
lemma sum_e_orth (p b b' : ℕ) (hb : b < p) (hb' : b' < p) :
    ∑ a ∈ range p, e (a * (((b : ℝ) - b') / p)) = if b = b' then (p : ℂ) else 0 := by
  have hp : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  split_ifs with h
  · subst h; simp [e_zero]
  · set θ : ℝ := ((b : ℝ) - b') / p
    have hpow : e θ ^ p = 1 := by
      rw [← e_nat_mul]
      have : (p : ℝ) * θ = (((b : ℤ) - b' : ℤ) : ℝ) := by
        simp only [θ]; push_cast; field_simp
      rw [this, e_int]
    have hd : 0 < dist1 θ := by
      unfold dist1
      apply abs_pos.mpr
      intro h0
      have : ((b : ℤ) - b' - round θ * p : ℤ) = 0 := by
        have h1 : θ * p = (round θ : ℝ) * p := congrArg (· * (p : ℝ)) (sub_eq_zero.mp h0)
        simp only [θ] at h1
        field_simp at h1
        exact_mod_cast (by linarith : ((b : ℝ) - b' - (round θ : ℝ) * p) = 0)
      have hk : round θ = 0 := by
        by_contra hk0
        rcases lt_or_gt_of_ne hk0 with hkn | hkp
        · have : (round θ) * (p : ℤ) ≤ -p := by nlinarith
          omega
        · have : (p : ℤ) ≤ (round θ) * (p : ℤ) := by nlinarith
          omega
      rw [hk] at this
      omega
    have h4 := four_dist1_le_norm_e_sub_one θ
    have hne : e θ ≠ 1 := by
      intro h1; rw [h1, sub_self, norm_zero] at h4; linarith
    simp_rw [e_nat_mul]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

lemma e_mod (n p a : ℕ) (hp : 0 < p) :
    e (n * ((a : ℝ) / p)) = e ((n % p : ℕ) * ((a : ℝ) / p)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have : (n : ℝ) * ((a : ℝ) / p) = (n % p : ℕ) * ((a : ℝ) / p) + (((n / p * a : ℕ) : ℤ) : ℝ) := by
    have h := Nat.mod_add_div n p
    have h' : (n : ℝ) = (n % p : ℕ) + p * (n / p : ℕ) := by exact_mod_cast h.symm
    have h2 : ((((n / p * a : ℕ) : ℤ) : ℝ)) = ((n / p : ℕ) : ℝ) * a := by
      rw [Int.cast_natCast, Nat.cast_mul]
    rw [h2, h']; field_simp
  rw [this, e_add_int]

/-- Discrete Parseval for `ℤ/p`. -/
lemma parseval_mod (p : ℕ) (Z : ℕ → ℂ) :
    ∑ a ∈ range p, ‖∑ b ∈ range p, Z b * e (b * ((a : ℝ) / p))‖ ^ 2
      = p * ∑ b ∈ range p, ‖Z b‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, conj_e, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ b ∈ range p, ∀ b' ∈ range p, ∑ a ∈ range p, Z b * e (b * ((a : ℝ) / p)) *
      ((starRingEnd ℂ) (Z b') * e (-(b' * ((a : ℝ) / p))))
      = Z b * (starRingEnd ℂ) (Z b') * (if b = b' then (p : ℂ) else 0) := by
    intro b hb b' hb'
    rw [← sum_e_orth p b b' (Finset.mem_range.mp hb) (Finset.mem_range.mp hb'), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show (a : ℝ) * (((b : ℝ) - b') / p) = b * ((a : ℝ) / p) + -(b' * ((a : ℝ) / p)) by ring,
      e_add]
    ring
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Finset.sum_comm, Finset.sum_congr rfl (this b hb)]
  simp [hb]
  ring

/-- **Montgomery's lemma, prime modulus**: if the support of `c` avoids the classes `Ω` mod `p`,
then `ω/(p-ω) |∑ c_n e(nβ)|² ≤ ∑_{(a,p)=1} |∑ c_n e(n(β + a/p))|²`. -/
lemma montgomery_prime (p : ℕ) (hp : p.Prime) (Ω : Finset ℕ) (hΩ : Ω ⊆ range p)
    (F : Finset ℕ) (c : ℕ → ℂ) (hF : ∀ n ∈ F, n % p ∉ Ω) (β : ℝ) :
    (Ω.card : ℝ) / (p - Ω.card) * ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2 ≤
      ∑ a ∈ U p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 := by
  have hp0 : 0 < p := hp.pos
  set d : ℕ → ℂ := fun n => c n * e (n * β) with hd
  set Z : ℕ → ℂ := fun b => ∑ n ∈ F.filter (fun n => n % p = b), d n with hZ
  have hS : ∀ a : ℕ, ∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p)) =
      ∑ b ∈ range p, Z b * e (b * ((a : ℝ) / p)) := by
    intro a
    have : ∀ n : ℕ, c n * e (n * (β + (a : ℝ) / p)) = d n * e ((n % p : ℕ) * ((a : ℝ) / p)) := by
      intro n; rw [hd, ← e_mod n p a hp0, mul_add, e_add]; ring
    simp_rw [this]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := range p)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp0))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hZ, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [(Finset.mem_filter.mp hn).2]
  have hS0 : ∑ n ∈ F, c n * e (n * β) = ∑ b ∈ range p, Z b := by
    have := hS 0
    simp only [Nat.cast_zero, zero_div, add_zero, mul_zero, e_zero, mul_one] at this
    exact this
  have hZΩ : ∀ b ∈ Ω, Z b = 0 := by
    intro b hb
    rw [hZ]; apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hnF, hnb⟩ := Finset.mem_filter.mp hn
    exact absurd (hnb ▸ hb) (hF n hnF)
  set W := ∑ b ∈ range p, ‖Z b‖ ^ 2 with hW
  set s0 := ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2 with hs0
  have hωp : Ω.card ≤ p := by simpa using Finset.card_le_card hΩ
  have hcs : s0 ≤ (p - Ω.card) * W := by
    have hsplit : ∑ b ∈ range p, Z b = ∑ b ∈ range p \ Ω, Z b := by
      rw [← Finset.sum_sdiff hΩ, Finset.sum_eq_zero hZΩ, add_zero]
    have hcard : ((range p \ Ω).card : ℝ) = p - Ω.card := by
      rw [Finset.card_sdiff_of_subset hΩ, Finset.card_range, Nat.cast_sub hωp]
    calc s0 = ‖∑ b ∈ range p \ Ω, Z b‖ ^ 2 := by rw [hs0, hS0, hsplit]
      _ ≤ (∑ b ∈ range p \ Ω, ‖Z b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (range p \ Ω).card * ∑ b ∈ range p \ Ω, ‖Z b‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (p - Ω.card) * W := by
          rw [hcard]; apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              (fun _ _ _ => by positivity)
          · rw [← hcard]; positivity
  have hpars : ∑ a ∈ range p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 = p * W := by
    simp_rw [hS]; exact parseval_mod p Z
  have hsplit : ∑ a ∈ range p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 =
      s0 + ∑ a ∈ U p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 := by
    rw [U, ← Finset.sum_filter_add_sum_filter_not (range p) (fun a => a.Coprime p), add_comm]
    congr 1
    have : (range p).filter (fun a => ¬ a.Coprime p) = {0} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hc⟩
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not] at hc
        exact Nat.eq_zero_of_dvd_of_lt hc ha
      · rintro rfl; exact ⟨hp0, by rw [Nat.coprime_zero_left]; exact hp.one_lt.ne'⟩
    rw [this, Finset.sum_singleton]; simp [hs0]
  have hω : (Ω.card : ℝ) ≤ p := by exact_mod_cast hωp
  have hW0 : 0 ≤ W := by positivity
  set T := ∑ a ∈ U p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2
  have hT : T = p * W - s0 := by linarith
  rcases (sub_nonneg.mpr hω).lt_or_eq with hpos | hzero
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos, hT]
    have hp0' : (0 : ℝ) ≤ p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcs hp0']
  · rw [← hzero, _root_.div_zero, zero_mul, hT]
    rw [← hzero, zero_mul] at hcs
    nlinarith

/-- Chinese remainder theorem for reduced fractions mod 1. -/
lemma sum_U_mul (q1 q2 : ℕ) (h1 : 0 < q1) (h2 : 0 < q2) (hc : q1.Coprime q2) (f : ℝ → ℝ)
    (hf : ∀ x (k : ℕ), f (x + k) = f x) :
    ∑ c ∈ U (q1 * q2), f ((c : ℝ) / ((q1 * q2 : ℕ) : ℝ)) =
      ∑ a1 ∈ U q1, ∑ a2 ∈ U q2, f ((a1 : ℝ) / q1 + (a2 : ℝ) / q2) := by
  have hm0 : 0 < q1 * q2 := Nat.mul_pos h1 h2
  set g : ℕ × ℕ → ℕ := fun p => (p.1 * q2 + p.2 * q1) % (q1 * q2) with hg
  have hq1 : (q1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have hq2 : (q2 : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
  have hval : ∀ a1 a2 : ℕ, f ((a1 : ℝ) / q1 + (a2 : ℝ) / q2) =
      f ((g (a1, a2) : ℝ) / ((q1 * q2 : ℕ) : ℝ)) := by
    intro a1 a2
    have hmod := Nat.mod_add_div (a1 * q2 + a2 * q1) (q1 * q2)
    have hcast : ((a1 * q2 + a2 * q1 : ℕ) : ℝ) = (g (a1, a2) : ℝ) +
        ((q1 * q2 : ℕ) : ℝ) * (((a1 * q2 + a2 * q1) / (q1 * q2) : ℕ) : ℝ) := by
      rw [hg]; exact_mod_cast hmod.symm
    have h3 : (a1 : ℝ) / q1 + (a2 : ℝ) / q2 =
        ((a1 * q2 + a2 * q1 : ℕ) : ℝ) / ((q1 * q2 : ℕ) : ℝ) := by
      push_cast; field_simp
    have h4 : (a1 : ℝ) / q1 + (a2 : ℝ) / q2 = (g (a1, a2) : ℝ) / ((q1 * q2 : ℕ) : ℝ) +
        (((a1 * q2 + a2 * q1) / (q1 * q2) : ℕ) : ℝ) := by
      rw [h3, hcast, add_div, mul_div_cancel_left₀]
      exact_mod_cast hm0.ne'
    rw [h4, hf]
  have hinj : Set.InjOn g ↑(U q1 ×ˢ U q2) := by
    rintro ⟨a1, a2⟩ hp ⟨b1, b2⟩ hq heq
    simp only [Finset.mem_coe, Finset.mem_product, U, Finset.mem_filter,
      Finset.mem_range] at hp hq
    have hmod : (a1 * q2 + a2 * q1) ≡ (b1 * q2 + b2 * q1) [MOD q1 * q2] := heq
    have e1 : a1 * q2 ≡ b1 * q2 [MOD q1] := by
      have := hmod.of_mul_right q2
      unfold Nat.ModEq at this ⊢
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at this
    have e2 : a2 * q1 ≡ b2 * q1 [MOD q2] := by
      have := hmod.of_mul_left q1
      unfold Nat.ModEq at this ⊢
      rwa [add_comm (a1 * q2), add_comm (b1 * q2), Nat.add_mul_mod_self_right,
        Nat.add_mul_mod_self_right] at this
    have f1 := Nat.ModEq.cancel_right_of_coprime (by exact hc) e1
    have f2 := Nat.ModEq.cancel_right_of_coprime (by exact hc.symm) e2
    unfold Nat.ModEq at f1 f2
    rw [Nat.mod_eq_of_lt hp.1.1, Nat.mod_eq_of_lt hq.1.1] at f1
    rw [Nat.mod_eq_of_lt hp.2.1, Nat.mod_eq_of_lt hq.2.1] at f2
    rw [f1, f2]
  have hmaps : ∀ p ∈ U q1 ×ˢ U q2, g p ∈ U (q1 * q2) := by
    rintro ⟨a1, a2⟩ hp
    simp only [Finset.mem_product, U, Finset.mem_filter, Finset.mem_range] at hp
    simp only [U, Finset.mem_filter, Finset.mem_range, hg]
    refine ⟨Nat.mod_lt _ hm0, ?_⟩
    have hA : Nat.Coprime (a1 * q2 + a2 * q1) q1 :=
      (Nat.coprime_add_mul_right_left (a1 * q2) q1 a2).mpr (Nat.Coprime.mul_left hp.1.2 hc.symm)
    have hB : Nat.Coprime (a1 * q2 + a2 * q1) q2 := by
      rw [add_comm]
      exact (Nat.coprime_add_mul_right_left (a2 * q1) q2 a1).mpr (Nat.Coprime.mul_left hp.2.2 hc)
    have hcop := Nat.Coprime.mul_right hA hB
    unfold Nat.Coprime at hcop ⊢
    rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hcop
  have himage : (U q1 ×ˢ U q2).image g = U (q1 * q2) := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc; exact hmaps p hp
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_U, card_U, card_U,
        Nat.totient_mul hc]
  rw [← himage, Finset.sum_image hinj, Finset.sum_product]
  exact Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => (hval a1 a2).symm))

/-- The local sieve factor `h(p) = ω(p)/(p - ω(p))`. -/
noncomputable def hfac (Ω : ℕ → Finset ℕ) (p : ℕ) : ℝ := ((Ω p).card : ℝ) / (p - (Ω p).card)

lemma hfac_nonneg (Ω : ℕ → Finset ℕ) (p : ℕ) (h : Ω p ⊆ range p) : 0 ≤ hfac Ω p := by
  unfold hfac
  have : (Ω p).card ≤ p := by simpa using Finset.card_le_card h
  have : ((Ω p).card : ℝ) ≤ p := by exact_mod_cast this
  apply div_nonneg (by positivity); linarith

/-- **Montgomery's lemma** for squarefree moduli:
`∏_{p | q} h(p) · |∑ c_n e(nβ)|² ≤ ∑_{(a,q)=1} |∑ c_n e(n(β + a/q))|²`. -/
theorem montgomery (Ω : ℕ → Finset ℕ) (F : Finset ℕ) (c : ℕ → ℂ) :
    ∀ q : ℕ, 0 < q → Squarefree q → (∀ p ∈ q.primeFactors, Ω p ⊆ range p) →
    (∀ n ∈ F, ∀ p ∈ q.primeFactors, n % p ∉ Ω p) → ∀ β : ℝ,
    (∏ p ∈ q.primeFactors, hfac Ω p) * ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2 ≤
      ∑ a ∈ U q, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / q))‖ ^ 2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq0 hsq hΩ hF β
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · have : q = 1 := by omega
    subst this
    have hU : U 1 = {0} := by decide
    simp [hU]
  · set p := q.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    set q' := q / p with hq'def
    have hpq : p * q' = q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
    have hq'0 : 0 < q' := by
      rcases Nat.eq_zero_or_pos q' with h | h
      · rw [h, mul_zero] at hpq; omega
      · exact h
    have hcop : p.Coprime q' := by
      rw [hp.coprime_iff_not_dvd]
      rintro ⟨t, ht⟩
      have : p * p ∣ q := ⟨t, by rw [← hpq, ht]; ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
    have hq'lt : q' < q := Nat.div_lt_self hq0 hp.one_lt
    have hsq' : Squarefree q' := hsq.squarefree_of_dvd ⟨p, by rw [← hpq]; ring⟩
    have hpf : q.primeFactors = {p} ∪ q'.primeFactors := by
      rw [← hpq, Nat.Coprime.primeFactors_mul hcop, hp.primeFactors]
    have hdisj : Disjoint {p} q'.primeFactors := by
      rw [← hp.primeFactors]; exact hcop.disjoint_primeFactors
    have hsub : q'.primeFactors ⊆ q.primeFactors := by rw [hpf]; exact Finset.subset_union_right
    have hpmem : p ∈ q.primeFactors := by rw [hpf]; simp
    rw [hpf, Finset.prod_union hdisj, Finset.prod_singleton]
    set f : ℝ → ℝ := fun x => ‖∑ n ∈ F, c n * e (n * (β + x))‖ ^ 2 with hfdef
    have hfper : ∀ x (k : ℕ), f (x + k) = f x := by
      intro x k; simp only [hfdef]; congr 2; refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show (n : ℝ) * (β + (x + k)) = n * (β + x) + ((n * k : ℕ) : ℤ) by push_cast; ring,
        e_add_int]
    have hcrt := sum_U_mul p q' hp.pos hq'0 hcop f hfper
    rw [hpq] at hcrt
    show _ ≤ ∑ a ∈ U q, f ((a : ℝ) / q)
    rw [hcrt, Finset.sum_comm]
    have hih := ih q' hq'lt hq'0 hsq' (fun p hp => hΩ p (hsub hp))
      (fun n hn p hp => hF n hn p (hsub hp)) β
    have hh0 := hfac_nonneg Ω p (hΩ p hpmem)
    calc hfac Ω p * (∏ x ∈ q'.primeFactors, hfac Ω x) * ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2
        ≤ hfac Ω p * ∑ a ∈ U q', ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / q'))‖ ^ 2 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hih hh0
      _ = ∑ a2 ∈ U q', hfac Ω p * ‖∑ n ∈ F, c n * e (n * (β + (a2 : ℝ) / q'))‖ ^ 2 :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ a2 ∈ U q', ∑ a1 ∈ U p, f ((a1 : ℝ) / p + (a2 : ℝ) / q') := by
          apply Finset.sum_le_sum
          intro a2 _
          have := montgomery_prime p hp (Ω p) (hΩ p hpmem) F c (fun n hn => hF n hn p hpmem)
            (β + (a2 : ℝ) / q')
          refine this.trans (le_of_eq (Finset.sum_congr rfl (fun a1 _ => ?_)))
          simp only [hfdef]
          rw [show β + (a2 : ℝ) / q' + (a1 : ℝ) / p = β + ((a1 : ℝ) / p + (a2 : ℝ) / q') by ring]

/-- **Arithmetic large sieve (Montgomery)**: if `A ⊆ [M, M+N)` avoids the residue classes
`Ω p` mod every prime `p ≤ Q`, then `|A| · L ≤ N + 2Q²` with
`L = ∑_{q ≤ Q squarefree} ∏_{p | q} ω(p)/(p - ω(p))`. -/
theorem arith_large_sieve (Q M N : ℕ) (A : Finset ℕ) (hA : A ⊆ Ico M (M + N))
    (Ω : ℕ → Finset ℕ) (hΩ : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ range p)
    (hAΩ : ∀ n ∈ A, ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p) :
    (A.card : ℝ) * ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Ω p
      ≤ N + 2 * (Q : ℝ) ^ 2 := by
  have hfarey := large_sieve_farey Q M N A hA (fun _ => 1)
  simp only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hfarey
  have hmont : ∀ q ∈ (Finset.Icc 1 Q).filter Squarefree, (∏ p ∈ q.primeFactors, hfac Ω p) *
      (A.card : ℝ) ^ 2 ≤ ∑ a ∈ U q, ‖∑ n ∈ A, e (n * ((a : ℝ) / q))‖ ^ 2 := by
    intro q hq
    obtain ⟨hq1, hsq⟩ := Finset.mem_filter.mp hq
    have hqQ := Finset.mem_Icc.mp hq1
    have hpf : ∀ p ∈ q.primeFactors, p.Prime ∧ p ≤ Q := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.le_of_mem_primeFactors hp).trans hqQ.2⟩
    have := montgomery Ω A (fun _ => 1) q hqQ.1 hsq
      (fun p hp => hΩ p (hpf p hp).1 (hpf p hp).2)
      (fun n hn p hp => hAΩ n hn p (hpf p hp).1 (hpf p hp).2) 0
    simp only [one_mul, mul_zero, e_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
      Complex.norm_natCast] at this
    exact this
  set L := ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Ω p
  have hL : L * (A.card : ℝ) ^ 2 ≤ (N + 2 * (Q : ℝ) ^ 2) * A.card := by
    calc L * (A.card : ℝ) ^ 2 = ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree,
          (∏ p ∈ q.primeFactors, hfac Ω p) * (A.card : ℝ) ^ 2 := Finset.sum_mul _ _ _
      _ ≤ ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ∑ a ∈ U q, ‖∑ n ∈ A, e (n * ((a : ℝ) / q))‖ ^ 2 :=
          Finset.sum_le_sum hmont
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ U q, ‖∑ n ∈ A, e (n * ((a : ℝ) / q))‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ (N + 2 * (Q : ℝ) ^ 2) * A.card := hfarey
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp; positivity
  · have hApos : (0 : ℝ) < A.card := by exact_mod_cast hpos
    have : (A.card * L) * A.card ≤ (N + 2 * (Q : ℝ) ^ 2) * A.card := by nlinarith
    exact le_of_mul_le_mul_right this hApos


/-! ### Brun–Titchmarsh for `Λ` from the arithmetic large sieve -/

/-- The sieved residue class `{0}`. -/
def Om0 : ℕ → Finset ℕ := fun _ => {0}

theorem sum_inv_le_two_sqfree (Q : ℕ) :
    ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n ≤
      2 * ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, (1:ℝ) / q := by
  classical
  have hdec : ∀ n ∈ Finset.Icc 1 Q, ∃ p : ℕ × ℕ,
      p ∈ ((Finset.Icc 1 Q).filter Squarefree) ×ˢ (Finset.Icc 1 Q) ∧ p.2 ^ 2 * p.1 = n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < n)
    refine ⟨(a, b), ?_, hab⟩
    have hb2 : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
    have h1 : b ^ 2 ≤ n := by rw [← hab]; exact Nat.le_mul_of_pos_right _ ha
    have h2 : a ≤ n := by rw [← hab]; exact Nat.le_mul_of_pos_left _ (by positivity)
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨ha, by omega⟩, hsq⟩, hb, by omega⟩
  choose! φ hφ hφeq using hdec
  set S := (Finset.Icc 1 Q).filter Squarefree
  have hinj : Set.InjOn φ (Finset.Icc 1 Q) := by
    intro x hx y hy hxy
    rw [← hφeq x hx, ← hφeq y hy, hxy]
  calc ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n
        = ∑ n ∈ Finset.Icc 1 Q,
            (fun p : ℕ × ℕ => (1:ℝ) / p.1 * (1 / ((p.2:ℝ) ^ 2))) (φ n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hc : ((n:ℕ):ℝ) = ((φ n).2:ℝ) ^ 2 * (φ n).1 := by exact_mod_cast (hφeq n hn).symm
        simp only
        rw [hc]; ring
    _ = ∑ p ∈ (Finset.Icc 1 Q).image φ, (1:ℝ) / p.1 * (1 / ((p.2:ℝ) ^ 2)) :=
        (Finset.sum_image (f := fun p : ℕ × ℕ => (1:ℝ) / p.1 * (1 / ((p.2:ℝ) ^ 2))) hinj).symm
    _ ≤ ∑ p ∈ S ×ˢ Finset.Icc 1 Q, (1:ℝ) / p.1 * (1 / ((p.2:ℝ) ^ 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_image] at hp
          obtain ⟨n, hn, rfl⟩ := hp
          exact hφ n hn
        · intro _ _ _; positivity
    _ = (∑ q ∈ S, (1:ℝ) / q) * ∑ m ∈ Finset.Icc 1 Q, 1 / ((m:ℝ) ^ 2) := by
        rw [Finset.sum_product, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
    _ ≤ (∑ q ∈ S, (1:ℝ) / q) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => by positivity))
        have := sum_inv_sq_nat_le (Finset.Icc 1 Q)
          (fun i hi => by rw [Finset.mem_Icc] at hi; omega)
        simpa [one_div] using this
    _ = _ := by ring

theorem hfac_Om0_ge (p : ℕ) (hp : p.Prime) : (1:ℝ) / p ≤ hfac Om0 p := by
  unfold hfac Om0
  simp only [Finset.card_singleton, Nat.cast_one]
  have : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

theorem sieve_L_ge (Q : ℕ) :
    (1 / 2 : ℝ) * Real.log (Q + 1) ≤
      ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Om0 p := by
  have h1 : Real.log (Q + 1) ≤ ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n := by
    have := log_add_one_le_harmonic Q
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [one_div] using this
  have h2 := sum_inv_le_two_sqfree Q
  have h3 : ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, (1:ℝ) / q ≤
      ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Om0 p := by
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_filter] at hq
    have hprod : ((q:ℕ):ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq.2]
    rw [hprod, one_div, ← Finset.prod_inv_distrib]
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      rw [← one_div]
      exact hfac_Om0_ge p (Nat.prime_of_mem_primeFactors hp)
  linarith

theorem vM_le_log_two_mul (A n : ℕ) (hn : n ≤ 2 * A) :
    (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log (2 * A) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp only [ArithmeticFunction.map_zero]
    rcases Nat.eq_zero_or_pos A with hA | hA
    · subst hA; simp
    · apply Real.log_nonneg
      have : (1:ℝ) ≤ A := by exact_mod_cast hA
      linarith
  · refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hpos) ?_)
    exact_mod_cast hn

/-- Prime powers in `(A, 2A]` with smallest prime factor `≤ Q`: at most `Q` of them. -/
theorem card_small_pp (A H Q : ℕ) (hHA : H ≤ A) :
    (((Finset.Ioc A (A + H)).filter (fun n => ¬ Q < n.minFac)).filter IsPrimePow).card ≤ Q := by
  set T := ((Finset.Ioc A (A + H)).filter (fun n => ¬ Q < n.minFac)).filter IsPrimePow
  have hmaps : ∀ n ∈ T, n.minFac ∈ Finset.Icc 1 Q := by
    intro n hn
    simp only [T, Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.minFac_pos n, by omega⟩
  have hinj : Set.InjOn Nat.minFac T := by
    have key : ∀ n ∈ T, ∀ n' ∈ T, n.minFac = n'.minFac → n < n' → False := by
      intro n hn n' hn' heq hlt
      simp only [T, Finset.mem_filter, Finset.mem_Ioc] at hn hn'
      have e1 := hn.2.minFac_pow_factorization_eq
      have e2 := hn'.2.minFac_pow_factorization_eq
      have hpp : 2 ≤ n.minFac := (Nat.minFac_prime (by
        intro h1; rw [h1] at hn; exact not_isPrimePow_one hn.2)).two_le
      obtain ⟨p, hp⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k, k = n.factorization n.minFac := ⟨_, rfl⟩
      obtain ⟨k', hk'⟩ : ∃ k, k = n'.factorization n'.minFac := ⟨_, rfl⟩
      rw [← hk] at e1
      rw [← hk', ← heq] at e2
      rw [← hp] at e1 e2 hpp
      have hkk : k < k' := by
        by_contra hc
        push Not at hc
        have : p ^ k' ≤ p ^ k := Nat.pow_le_pow_right (by omega) hc
        rw [e1, e2] at this
        omega
      have h3 : p ^ (k + 1) ≤ p ^ k' := Nat.pow_le_pow_right (by omega) hkk
      have h5 : p ^ k * 2 ≤ p ^ k * p := Nat.mul_le_mul_left _ hpp
      have h6 : 2 * n ≤ n' := by
        calc 2 * n = p ^ k * 2 := by rw [e1]; ring
          _ ≤ p ^ k * p := h5
          _ = p ^ (k + 1) := (pow_succ p k).symm
          _ ≤ p ^ k' := h3
          _ = n' := e2
      omega
    intro n hn n' hn' heq
    rcases lt_trichotomy n n' with h | h | h
    · exact (key n hn n' hn' heq h).elim
    · exact h
    · exact (key n' hn' n hn heq.symm h).elim
  calc T.card ≤ (Finset.Icc 1 Q).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = Q := by simp

theorem bt_core (A H : ℕ) (hA : 32 ≤ A) (hAH : A ^ 9 ≤ H ^ 10) (hHA : H ≤ A) :
    ∑ n ∈ Finset.Ioc A (A + H), (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 56 * H := by
  set Q := Nat.sqrt H with hQ
  have hQ1 : Q * Q ≤ H := Nat.sqrt_le H
  have hQ2 : H < (Q + 1) * (Q + 1) := Nat.lt_succ_sqrt H
  have hH1 : 1 ≤ H := by
    by_contra h
    have : H = 0 := by omega
    rw [this] at hAH
    have : 0 < A ^ 9 := by positivity
    simp at hAH; omega
  have hQpos : 1 ≤ Q := by
    by_contra h
    have : Q = 0 := by omega
    rw [this] at hQ2; omega
  -- A^9 < 4^10 Q^20
  have hAQ : A ^ 9 < 4 ^ 10 * Q ^ 20 := by
    have h1 : H ^ 10 < ((Q + 1) * (Q + 1)) ^ 10 := Nat.pow_lt_pow_left hQ2 (by norm_num)
    have h2 : (Q + 1) * (Q + 1) ≤ 4 * Q ^ 2 := by nlinarith
    have h3 : ((Q + 1) * (Q + 1)) ^ 10 ≤ (4 * Q ^ 2) ^ 10 := Nat.pow_le_pow_left h2 10
    have h4 : (4 * Q ^ 2) ^ 10 = 4 ^ 10 * Q ^ 20 := by ring
    omega
  have hAr : (32:ℝ) ≤ A := by exact_mod_cast hA
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQpos
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : 9 * Real.log A ≤ 20 * Real.log 2 + 20 * Real.log Q := by
    have h0 : A ^ 9 ≤ 2 ^ 20 * Q ^ 20 := by
      calc A ^ 9 ≤ 4 ^ 10 * Q ^ 20 := hAQ.le
        _ = 2 ^ 20 * Q ^ 20 := by norm_num
    have h0' : (A:ℝ) ^ 9 ≤ (2:ℝ) ^ 20 * (Q:ℝ) ^ 20 := by exact_mod_cast h0
    have h := Real.log_le_log (by positivity) h0'
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hlog32 : 5 * Real.log 2 ≤ Real.log A := by
    have := Real.log_le_log (by norm_num) hAr
    rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have hlogQ : Real.log A / 4 ≤ Real.log Q := by linarith
  have hlogQ' : Real.log Q ≤ Q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogA_Q : Real.log A ≤ 3 * Q := by nlinarith
  have hlog2A : Real.log (2 * A) ≤ 2 * Real.log A := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hQH : (Q:ℝ) * Q ≤ H := by exact_mod_cast hQ1
  have hΛle : ∀ n ∈ Finset.Ioc A (A + H), (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 2 * Real.log A :=
    fun n hn => (vM_le_log_two_mul A n (by rw [Finset.mem_Ioc] at hn; omega)).trans hlog2A
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun n => Q < n.minFac)]
  -- sieved part
  set S := (Finset.Ioc A (A + H)).filter (fun n => Q < n.minFac)
  have hls := arith_large_sieve Q (A + 1) H S
    (by
      intro n hn
      simp only [S, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico] at hn ⊢
      omega)
    Om0 (by intro p hp _; simp [Om0, hp.pos])
    (by
      intro n hn p hp hpQ hmem
      simp only [Om0, Finset.mem_singleton] at hmem
      simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hn
      have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero hmem
      have := Nat.minFac_le_of_dvd hp.two_le hdvd
      omega)
  have hL := sieve_L_ge Q
  have hlogQ1 : Real.log Q ≤ Real.log (Q + 1) := Real.log_le_log (by linarith) (by linarith)
  set L := ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Om0 p
  have hLA : Real.log A / 8 ≤ L := by linarith
  have hcard : (S.card : ℝ) * (Real.log A / 8) ≤ 3 * H := by
    have h0 : (0:ℝ) ≤ S.card := by positivity
    calc (S.card : ℝ) * (Real.log A / 8) ≤ S.card * L := mul_le_mul_of_nonneg_left hLA h0
      _ ≤ H + 2 * (Q:ℝ) ^ 2 := hls
      _ ≤ 3 * H := by nlinarith
  have hS : ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 48 * H := by
    calc ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ ∑ n ∈ S, 2 * Real.log A :=
          Finset.sum_le_sum (fun n hn => hΛle n (Finset.mem_of_mem_filter n hn))
      _ = S.card * (2 * Real.log A) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 16 * ((S.card : ℝ) * (Real.log A / 8)) := by ring
      _ ≤ 16 * (3 * H) := by linarith
      _ = 48 * H := by ring
  -- prime powers with a small prime factor
  set S' := (Finset.Ioc A (A + H)).filter (fun n => ¬ Q < n.minFac)
  have hS' : ∑ n ∈ S', (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 6 * H := by
    rw [← Finset.sum_filter_of_ne (p := IsPrimePow) (fun n _ hne => by
      by_contra h
      exact hne (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h))]
    have hc := card_small_pp A H Q hHA
    have hcr : ((S'.filter IsPrimePow).card : ℝ) ≤ Q := by exact_mod_cast hc
    calc ∑ n ∈ S'.filter IsPrimePow, (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ ∑ n ∈ S'.filter IsPrimePow, 2 * Real.log A :=
          Finset.sum_le_sum (fun n hn => hΛle n
            (Finset.mem_of_mem_filter n (Finset.mem_of_mem_filter n hn)))
      _ = (S'.filter IsPrimePow).card * (2 * Real.log A) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Q * (2 * (3 * Q)) := by
          apply mul_le_mul hcr (by linarith) (by linarith) (by positivity)
      _ ≤ 6 * H := by nlinarith
  have : (0:ℝ) ≤ H := by positivity
  linarith

theorem sum_Ioc_vM_le_cheb (A B : ℕ) :
    ∑ n ∈ Finset.Ioc A B, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ (Real.log 4 + 4) * B := by
  have h := Chebyshev.psi_le_const_mul_self (x := (B:ℝ)) (by positivity)
  unfold Chebyshev.psi at h
  rw [Nat.floor_natCast] at h
  refine le_trans ?_ h
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    omega
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Brun–Titchmarsh, robust form. -/
theorem bt_gen : ∃ C : ℝ, 0 < C ∧ ∀ A H : ℕ, ∀ R : ℝ, 1 ≤ R → R ^ 10 ≤ A →
    ∑ n ∈ Finset.Ioc A (A + H), (ArithmeticFunction.vonMangoldt n : ℝ) ≤
      C * (H + A / R + 1) := by
  set c := Real.log 4 + 4 with hc
  have hc0 : 0 < c := by have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
  refine ⟨56 + 32 * c, by positivity, ?_⟩
  intro A H R hR hRA
  have hAR : 0 ≤ (A:ℝ) / R := by positivity
  have hH0 : (0:ℝ) ≤ H := by positivity
  have hcheb := sum_Ioc_vM_le_cheb A (A + H)
  push_cast at hcheb
  rcases Nat.lt_or_ge A 32 with hA | hA
  · have : (A:ℝ) ≤ 32 := by exact_mod_cast hA.le
    calc _ ≤ c * (A + H) := hcheb
      _ ≤ c * (32 * (H + A / R + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le; nlinarith
      _ ≤ (56 + 32 * c) * (H + A / R + 1) := by nlinarith
  set H' := max H ⌈(A:ℝ) / R⌉₊ with hH'
  have hceil : ((⌈(A:ℝ) / R⌉₊ : ℕ) : ℝ) < A / R + 1 := Nat.ceil_lt_add_one hAR
  have hH'le : (H' : ℝ) ≤ H + A / R + 1 := by
    rw [hH', Nat.cast_max]
    apply max_le <;> linarith
  rcases Nat.lt_or_ge A H' with hAH | hAH
  · have : (A:ℝ) < H' := by exact_mod_cast hAH
    calc _ ≤ c * (A + H) := hcheb
      _ ≤ c * (2 * (H + A / R + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le; linarith
      _ ≤ (56 + 32 * c) * (H + A / R + 1) := by nlinarith
  · have hA0 : (0:ℝ) < A := lt_of_lt_of_le (by norm_num) (show (32:ℝ) ≤ A by exact_mod_cast hA)
    have h9 : A ^ 9 ≤ H' ^ 10 := by
      have h1 : (A:ℝ) / R ≤ H' := by
        rw [hH', Nat.cast_max]; exact (Nat.le_ceil _).trans (le_max_right _ _)
      have hR10 : 0 < R ^ 10 := by positivity
      have h2 : (A:ℝ) ^ 9 ≤ ((A:ℝ) / R) ^ 10 := by
        rw [div_pow, le_div_iff₀ hR10]
        calc (A:ℝ) ^ 9 * R ^ 10 ≤ (A:ℝ) ^ 9 * A := mul_le_mul_of_nonneg_left hRA (by positivity)
          _ = (A:ℝ) ^ 10 := by ring
      have h3 : ((A:ℝ) / R) ^ 10 ≤ (H':ℝ) ^ 10 := pow_le_pow_left₀ hAR h1 10
      exact_mod_cast h2.trans h3
    have hcore := bt_core A H' hA h9 hAH
    have hsub : ∑ n ∈ Finset.Ioc A (A + H), (ArithmeticFunction.vonMangoldt n : ℝ) ≤
        ∑ n ∈ Finset.Ioc A (A + H'), (ArithmeticFunction.vonMangoldt n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_Ioc] at hn ⊢
        have : H ≤ H' := le_max_left _ _
        omega
      · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg
    calc _ ≤ 56 * (H':ℝ) := hsub.trans hcore
      _ ≤ 56 * (H + A / R + 1) := by linarith
      _ ≤ (56 + 32 * c) * (H + A / R + 1) := by nlinarith

/-! ### Mertens-type bound `∑ Λ(n)/n ≤ C log N` -/

theorem sum_vM_div_aux (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤
      2 * (Real.log 4 + 4) * (Real.log N / Real.log 2 + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have hc0 : 0 < Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · have h1 : N = 1 := by omega
    subst h1
    have h0 : ∑ n ∈ Finset.Ioc 0 1, (ArithmeticFunction.vonMangoldt n : ℝ) / n = 0 := by simp
    have h0' : Real.log ((1:ℕ):ℝ) = 0 := by simp
    rw [h0, h0']
    norm_num
    positivity
  set M := N / 2 with hM
  have hMN : M < N := Nat.div_lt_self (by omega) (by norm_num)
  have hM1 : 1 ≤ M := by omega
  have hsplit := Finset.sum_Ioc_consecutive
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) / n) (Nat.zero_le M) hMN.le
  rw [← hsplit]
  have h1 := ih M hMN hM1
  have h2 : ∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤
      2 * (Real.log 4 + 4) := by
    calc ∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) / n
          ≤ ∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) / ((M:ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ioc] at hn
          have : (M:ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn.1
          exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (by positivity) this
      _ = (∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ)) / ((M:ℝ) + 1) := by
          rw [Finset.sum_div]
      _ ≤ (Real.log 4 + 4) * N / ((M:ℝ) + 1) := by
          gcongr; exact sum_Ioc_vM_le_cheb M N
      _ ≤ 2 * (Real.log 4 + 4) := by
          rw [div_le_iff₀ (by positivity)]
          have : (N:ℝ) ≤ 2 * M + 1 := by exact_mod_cast (by omega : N ≤ 2 * M + 1)
          nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM1
  have h3 : Real.log M + Real.log 2 ≤ Real.log N := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    apply Real.log_le_log (by positivity)
    have : (M:ℝ) * 2 ≤ N := by exact_mod_cast (by omega : M * 2 ≤ N)
    linarith
  calc _ ≤ 2 * (Real.log 4 + 4) * (Real.log M / Real.log 2 + 1) + 2 * (Real.log 4 + 4) :=
        add_le_add h1 h2
    _ = 2 * (Real.log 4 + 4) * ((Real.log M + Real.log 2) / Real.log 2 + 1) := by
        field_simp
    _ ≤ _ := by gcongr

theorem sum_vM_div_le : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤ C * Real.log N := by
  have hc0 : 0 < Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * (Real.log 4 + 4) / Real.log 2, by positivity, ?_⟩
  intro N hN
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have h := sum_vM_div_aux N (by omega)
  have hlog : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have h1 : Real.log N / Real.log 2 + 1 ≤ 2 * (Real.log N / Real.log 2) := by
    have : 1 ≤ Real.log N / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    linarith
  calc _ ≤ 2 * (Real.log 4 + 4) * (Real.log N / Real.log 2 + 1) := h
    _ ≤ 2 * (Real.log 4 + 4) * (2 * (Real.log N / Real.log 2)) := by gcongr
    _ = _ := by ring

/-! ### The Schur row bound -/

/-- The Gaussian kernel `exp(-T₁²(log m - log n)²/4)`. -/
def Kg (T1 : ℝ) (m n : ℕ) : ℝ := Real.exp (-(T1 ^ 2 * (Real.log m - Real.log n) ^ 2 / 4))

theorem gauss_tail_scalar (j : ℕ) (x : ℝ) (hx : x ≤ ((j:ℝ) + 1) / 4) :
    Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) * (2 * j + 5) ≤
      5 * Real.exp 7 * (1 / 2) ^ j := by
  have h1 : (2 * (j:ℝ) + 5) ≤ 5 * Real.exp j := by
    have := Real.add_one_le_exp (j:ℝ)
    have : (0:ℝ) ≤ j := by positivity
    linarith
  have h2 : Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) * Real.exp j ≤
      Real.exp 7 * Real.exp (-(j:ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((j:ℝ) - 5)]
  have h3 : Real.exp (-(j:ℝ)) ≤ (1 / 2) ^ j := by
    rw [show (-(j:ℝ)) = j * (-1) by ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have hE : 0 ≤ Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) := by positivity
  calc Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) * (2 * j + 5)
      ≤ Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) * (5 * Real.exp j) :=
        mul_le_mul_of_nonneg_left h1 hE
    _ = 5 * (Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) * Real.exp j) := by ring
    _ ≤ 5 * (Real.exp 7 * Real.exp (-(j:ℝ))) := by linarith
    _ ≤ 5 * (Real.exp 7 * (1 / 2) ^ j) := by
        gcongr
    _ = _ := by ring

theorem window_bound (CB : ℝ) (hCB : 0 < CB)
    (hbt : ∀ A H : ℕ, ∀ R : ℝ, 1 ≤ R → R ^ 10 ≤ A →
      ∑ n ∈ Finset.Ioc A (A + H), (ArithmeticFunction.vonMangoldt n : ℝ) ≤ CB * (H + A / R + 1))
    (T1 : ℝ) (hT1 : 4 ≤ T1) (N0 N1 m : ℕ) (hN0 : T1 ^ 10 ≤ N0) (hm : m ∈ Finset.Ioc N0 N1)
    (x : ℝ) (hx : 0 ≤ x) :
    ∑ n ∈ (Finset.Ioc N0 N1).filter (fun n : ℕ => |Real.log n - Real.log m| < x),
      (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤
      CB * Real.exp (2 * x) * (2 * x + 3 / T1) := by
  rw [Finset.mem_Ioc] at hm
  have hT1pos : 0 < T1 := by linarith
  have hT1_10 : T1 ≤ T1 ^ 10 := by
    calc T1 = T1 ^ 1 := (pow_one _).symm
      _ ≤ T1 ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hmr : (N0:ℝ) < m := by exact_mod_cast hm.1
  have hmT : T1 ≤ m := by linarith
  have hm0 : 0 < (m:ℝ) := by linarith
  set ex := Real.exp x with hexdef
  set emx := Real.exp (-x) with hemxdef
  have hex : 0 < ex := Real.exp_pos x
  have hemx : 0 < emx := Real.exp_pos _
  have hexmx : ex * emx = 1 := by rw [hexdef, hemxdef, ← Real.exp_add]; simp
  have hemx1 : emx ≤ 1 := by rw [hemxdef]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hex1 : 1 ≤ ex := Real.one_le_exp hx
  set filt := (Finset.Ioc N0 N1).filter (fun n : ℕ => |Real.log n - Real.log m| < x) with hfilt
  have hmem : ∀ n ∈ filt, N0 < n ∧ (0:ℝ) < n ∧ (m:ℝ) * emx < n ∧ (n:ℝ) < m * ex := by
    intro n hn
    rw [hfilt, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn1, _⟩, hv⟩ := hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [abs_lt] at hv
    refine ⟨hn1, hnpos, ?_, ?_⟩
    · have : Real.log m + -x < Real.log n := by linarith
      calc (m:ℝ) * emx = Real.exp (Real.log m + -x) := by rw [Real.exp_add, Real.exp_log hm0]
        _ < Real.exp (Real.log n) := Real.exp_lt_exp.mpr this
        _ = n := Real.exp_log hnpos
    · have : Real.log n < Real.log m + x := by linarith
      calc (n:ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ < Real.exp (Real.log m + x) := Real.exp_lt_exp.mpr this
        _ = m * ex := by rw [Real.exp_add, Real.exp_log hm0]
  set F0 := ⌊(m:ℝ) * emx⌋₊ with hF0
  set F1 := ⌊(m:ℝ) * ex⌋₊ with hF1
  set A := max N0 F0 with hAdef
  set H := F1 - A with hHdef
  have hsub : filt ⊆ Finset.Ioc A (A + H) := by
    intro n hn
    obtain ⟨hn1, hnpos, hlo, hup⟩ := hmem n hn
    have h1 : F0 < n := (Nat.floor_lt (by positivity)).mpr hlo
    have h2 : n ≤ F1 := Nat.le_floor hup.le
    have hA : A < n := max_lt hn1 h1
    rw [Finset.mem_Ioc]
    exact ⟨hA, by omega⟩
  have hF01 : F0 ≤ F1 := Nat.floor_le_floor (by nlinarith)
  have hHle : (H:ℝ) ≤ m * ex - m * emx + 1 := by
    have h1 : H ≤ F1 - F0 := by have : F0 ≤ A := le_max_right _ _
                                omega
    have h2 : (H:ℝ) ≤ ((F1 - F0 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub hF01] at h2
    have h3 : (F1:ℝ) ≤ m * ex := Nat.floor_le (by positivity)
    have h4 : (m:ℝ) * emx < F0 + 1 := Nat.lt_floor_add_one _
    linarith
  have hAm : (A:ℝ) ≤ m := by
    have : A ≤ m := max_le hm.1.le (Nat.floor_le_of_le (by nlinarith))
    exact_mod_cast this
  have hterm : ∀ n ∈ filt, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤
      ex / m * (ArithmeticFunction.vonMangoldt n : ℝ) := by
    intro n hn
    obtain ⟨_, hnpos, hlo, _⟩ := hmem n hn
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
    rw [div_le_div_iff₀ hnpos hm0]
    nlinarith
  have hsum : ∑ n ∈ filt, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ CB * (H + A / T1 + 1) := by
    calc ∑ n ∈ filt, (ArithmeticFunction.vonMangoldt n : ℝ)
        ≤ ∑ n ∈ Finset.Ioc A (A + H), (ArithmeticFunction.vonMangoldt n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ ≤ _ := hbt A H T1 (by linarith) (by
          have : (N0:ℝ) ≤ A := by exact_mod_cast le_max_left N0 F0
          linarith)
  have hexp2 : Real.exp (2 * x) = ex * ex := by rw [two_mul, Real.exp_add]
  have hdiff : ex - emx ≤ 2 * x * ex := by
    have h1 := Real.add_one_le_exp (-2 * x)
    have h2 : emx = ex * Real.exp (-2 * x) := by
      rw [hemxdef, hexdef, ← Real.exp_add]; ring_nf
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hex.le]
  have hAT : (A:ℝ) / T1 ≤ m / T1 := div_le_div_of_nonneg_right hAm hT1pos.le
  have hinvm : 1 / (m:ℝ) ≤ 1 / T1 := one_div_le_one_div_of_le hT1pos hmT
  calc ∑ n ∈ filt, (ArithmeticFunction.vonMangoldt n : ℝ) / n
      ≤ ∑ n ∈ filt, ex / m * (ArithmeticFunction.vonMangoldt n : ℝ) := Finset.sum_le_sum hterm
    _ = ex / m * ∑ n ∈ filt, (ArithmeticFunction.vonMangoldt n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ex / m * (CB * (H + A / T1 + 1)) := by
        apply mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ex / m * (CB * ((m * ex - m * emx + 1) + m / T1 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hCB.le
        linarith
    _ = CB * (ex * (ex - emx) + 2 * ex * (1 / m) + ex / T1) := by
        field_simp
        ring
    _ ≤ CB * (ex * (2 * x * ex) + 2 * (ex * ex) * (1 / T1) + (ex * ex) / T1) := by
        apply mul_le_mul_of_nonneg_left _ hCB.le
        have e1 : ex * (ex - emx) ≤ ex * (2 * x * ex) := mul_le_mul_of_nonneg_left hdiff hex.le
        have e2 : 2 * ex * (1 / m) ≤ 2 * (ex * ex) * (1 / T1) := by
          apply mul_le_mul _ hinvm (by positivity) (by positivity)
          nlinarith
        have e3 : ex / T1 ≤ (ex * ex) / T1 := div_le_div_of_nonneg_right (by nlinarith) hT1pos.le
        linarith
    _ = CB * Real.exp (2 * x) * (2 * x + 3 / T1) := by rw [hexp2]; ring

theorem schur_row : ∃ C : ℝ, 0 < C ∧ ∀ T1 : ℝ, 4 ≤ T1 → ∀ N0 N1 m : ℕ, T1 ^ 10 ≤ N0 →
    m ∈ Finset.Ioc N0 N1 →
    ∑ n ∈ Finset.Ioc N0 N1, (ArithmeticFunction.vonMangoldt n : ℝ) / n * Kg T1 m n ≤ C / T1 := by
  obtain ⟨CB, hCB, hbt⟩ := bt_gen
  refine ⟨CB * (5 * Real.exp 7) * 2, by positivity, ?_⟩
  intro T1 hT1 N0 N1 m hN0 hm
  have hT1pos : 0 < T1 := by linarith
  have hmI := Finset.mem_Ioc.mp hm
  set F := Finset.Ioc N0 N1 with hF
  set J := ⌊T1 * Real.log N1⌋₊ + 1 with hJ
  have hw0 : ∀ n : ℕ, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n :=
    fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hmN : (m:ℝ) ≤ N1 := by exact_mod_cast hmI.2
  -- step A
  have hA : ∀ n ∈ F, (ArithmeticFunction.vonMangoldt n : ℝ) / n * Kg T1 m n ≤
      ∑ j ∈ Finset.range J, if T1 * |Real.log n - Real.log m| < j + 1 then
        Real.exp (-((j:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) else 0 := by
    intro n hn
    have hnI := Finset.mem_Ioc.mp hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnN : (n:ℝ) ≤ N1 := by exact_mod_cast hnI.2
    set v := |Real.log n - Real.log m| with hv
    set j0 := ⌊T1 * v⌋₊ with hj0
    have hv0 : 0 ≤ v := abs_nonneg _
    have hj0le : (j0:ℝ) ≤ T1 * v := Nat.floor_le (by positivity)
    have hj0lt : T1 * v < j0 + 1 := Nat.lt_floor_add_one _
    have hvN : v ≤ Real.log N1 := by
      have a1 := Real.log_nonneg hn1
      have a2 := Real.log_nonneg hm1
      have a3 := Real.log_le_log (by linarith) hnN
      have a4 := Real.log_le_log (by linarith) hmN
      rw [hv, abs_le]; constructor <;> linarith
    have hj0J : j0 ∈ Finset.range J := by
      rw [Finset.mem_range]
      have : j0 ≤ ⌊T1 * Real.log N1⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_left hvN hT1pos.le)
      omega
    have hK : Kg T1 m n ≤ Real.exp (-((j0:ℝ) ^ 2 / 4)) := by
      unfold Kg
      apply Real.exp_le_exp.mpr
      have h1 : (j0:ℝ) ^ 2 ≤ (T1 * v) ^ 2 := pow_le_pow_left₀ (by positivity) hj0le 2
      have h2 : (T1 * v) ^ 2 = T1 ^ 2 * (Real.log m - Real.log n) ^ 2 := by
        rw [hv, mul_pow, sq_abs]; ring
      linarith
    have hnn : ∀ j ∈ Finset.range J, 0 ≤ (if T1 * v < j + 1 then
        Real.exp (-((j:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) else 0) := by
      intro j _
      split_ifs
      · exact mul_nonneg (Real.exp_pos _).le (hw0 n)
      · exact le_refl _
    calc (ArithmeticFunction.vonMangoldt n : ℝ) / n * Kg T1 m n
        ≤ Real.exp (-((j0:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right hK (hw0 n)
      _ = if T1 * v < j0 + 1 then
            Real.exp (-((j0:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n)
          else 0 := by rw [if_pos hj0lt]
      _ ≤ _ := Finset.single_le_sum (f := fun j : ℕ => if T1 * v < j + 1 then
            Real.exp (-((j:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) else 0)
            hnn hj0J
  -- step B
  have hB : ∑ n ∈ F, (ArithmeticFunction.vonMangoldt n : ℝ) / n * Kg T1 m n ≤
      ∑ j ∈ Finset.range J, Real.exp (-((j:ℝ) ^ 2 / 4)) *
        ∑ n ∈ F.filter (fun n : ℕ => |Real.log n - Real.log m| < ((j:ℝ) + 1) / T1),
          (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
    calc _ ≤ ∑ n ∈ F, ∑ j ∈ Finset.range J, (if T1 * |Real.log n - Real.log m| < j + 1 then
            Real.exp (-((j:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) else 0) :=
          Finset.sum_le_sum hA
      _ = ∑ j ∈ Finset.range J, ∑ n ∈ F, (if T1 * |Real.log n - Real.log m| < j + 1 then
            Real.exp (-((j:ℝ) ^ 2 / 4)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / n) else 0) :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          have hiff : T1 * |Real.log n - Real.log m| < j + 1 ↔
              |Real.log n - Real.log m| < ((j:ℝ) + 1) / T1 := by
            rw [lt_div_iff₀ hT1pos, mul_comm]
          by_cases h : |Real.log n - Real.log m| < ((j:ℝ) + 1) / T1
          · rw [if_pos (hiff.mpr h), if_pos h]
          · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  -- step C, D
  have hC : ∀ j ∈ Finset.range J, Real.exp (-((j:ℝ) ^ 2 / 4)) *
        ∑ n ∈ F.filter (fun n : ℕ => |Real.log n - Real.log m| < ((j:ℝ) + 1) / T1),
          (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤
        CB / T1 * (5 * Real.exp 7 * (1 / 2) ^ j) := by
    intro j _
    set x := ((j:ℝ) + 1) / T1 with hx
    have hx0 : 0 ≤ x := by positivity
    have hW := window_bound CB hCB hbt T1 hT1 N0 N1 m hN0 hm x hx0
    have hx4 : x ≤ ((j:ℝ) + 1) / 4 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hT1
    have hs := gauss_tail_scalar j x hx4
    have hE0 : 0 ≤ Real.exp (-((j:ℝ) ^ 2 / 4)) := (Real.exp_pos _).le
    have heq : 2 * x + 3 / T1 = (2 * j + 5) / T1 := by rw [hx]; field_simp; ring
    calc Real.exp (-((j:ℝ) ^ 2 / 4)) *
          ∑ n ∈ F.filter (fun n : ℕ => |Real.log n - Real.log m| < x),
            (ArithmeticFunction.vonMangoldt n : ℝ) / n
        ≤ Real.exp (-((j:ℝ) ^ 2 / 4)) * (CB * Real.exp (2 * x) * (2 * x + 3 / T1)) :=
          mul_le_mul_of_nonneg_left hW hE0
      _ = CB / T1 * (Real.exp (-((j:ℝ) ^ 2 / 4)) * Real.exp (2 * x) * (2 * j + 5)) := by
          rw [heq]; field_simp
      _ ≤ CB / T1 * (5 * Real.exp 7 * (1 / 2) ^ j) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
  calc _ ≤ _ := hB
    _ ≤ ∑ j ∈ Finset.range J, CB / T1 * (5 * Real.exp 7 * (1 / 2) ^ j) := Finset.sum_le_sum hC
    _ = CB / T1 * (5 * Real.exp 7) * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ CB / T1 * (5 * Real.exp 7) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le J) (by positivity)
    _ = CB * (5 * Real.exp 7) * 2 / T1 := by ring

/-! ### Gaussian-weighted mean value -/

/-- `e^{-iut}`. -/
def ee (u t : ℝ) : ℂ := Complex.exp (-(u:ℂ) * I * (t:ℂ))

theorem norm_ee (u t : ℝ) : ‖ee u t‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

theorem continuous_ee (u : ℝ) : Continuous (fun t : ℝ => ee u t) := by
  unfold ee
  fun_prop

theorem cpow_eq_ee (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n:ℂ) ^ (-((t:ℂ) * I)) = ee (Real.log n) t := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  unfold ee
  congr 1
  ring

theorem ee_conj_gauss (u v t T1 : ℝ) :
    ee u t * (starRingEnd ℂ) (ee v t) * ((Real.exp (-(t ^ 2 / T1 ^ 2)) : ℝ) : ℂ) =
      Complex.exp (-(1 / (T1:ℂ) ^ 2) * (t:ℂ) ^ 2 + (-(((u - v : ℝ) : ℂ) * I)) * (t:ℂ) + 0) := by
  unfold ee
  rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem gauss_hb (T1 : ℝ) (hT1 : 0 < T1) : (-(1 / (T1:ℂ) ^ 2)).re < 0 := by
  have h : (1 / (T1:ℂ) ^ 2) = ((1 / T1 ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.neg_re, Complex.ofReal_re]
  have : 0 < 1 / T1 ^ 2 := by positivity
  linarith

theorem gauss_term (a : ℝ) (T1 : ℝ) (hT1 : 0 < T1) :
    ∫ t : ℝ, Complex.exp (-(1 / (T1:ℂ) ^ 2) * (t:ℂ) ^ 2 + (-((a:ℂ) * I)) * (t:ℂ) + 0) =
      ((Real.pi * T1 ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ((Real.exp (-(T1 ^ 2 * a ^ 2 / 4)) : ℝ) : ℂ) := by
  rw [integral_cexp_quadratic (gauss_hb T1 hT1)]
  have hT : (T1:ℂ) ≠ 0 := by exact_mod_cast hT1.ne'
  congr 1
  · congr 1
    push_cast
    field_simp
  · rw [Complex.ofReal_exp]
    congr 1
    have hsq : (-((a:ℂ) * I)) ^ 2 = -(a:ℂ) ^ 2 := by
      rw [neg_sq, mul_pow, Complex.I_sq]; ring
    rw [hsq]
    push_cast
    field_simp
    ring

theorem gauss_mv (F : Finset ℕ) (b : ℕ → ℂ) (u : ℕ → ℝ) (T1 : ℝ) (hT1 : 0 < T1) :
    ∫ t in (-T1)..T1, ‖∑ n ∈ F, b n * ee (u n) t‖ ^ 2 ≤
      Real.exp 1 * (2 * T1) * ∑ m ∈ F, ∑ n ∈ F,
        ‖b m‖ * ‖b n‖ * Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4)) := by
  set D := fun t : ℝ => ∑ n ∈ F, b n * ee (u n) t with hD
  set w := fun t : ℝ => Real.exp (-(t ^ 2 / T1 ^ 2)) with hw
  set g := fun t : ℝ => ‖D t‖ ^ 2 * w t with hg
  set q := fun (m n : ℕ) (t : ℝ) => b m * (starRingEnd ℂ) (b n) *
      Complex.exp (-(1 / (T1:ℂ) ^ 2) * (t:ℂ) ^ 2 + (-(((u m - u n : ℝ) : ℂ) * I)) * (t:ℂ) + 0)
    with hq
  have hpt : ∀ t, ((g t : ℝ) : ℂ) = ∑ m ∈ F, ∑ n ∈ F, q m n t := by
    intro t
    simp only [hg, hD, hw, hq]
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_mul, ← ee_conj_gauss (u m) (u n) t T1]
    ring
  have hqi : ∀ m n, Integrable (q m n) := by
    intro m n
    exact (integrable_cexp_quadratic' (gauss_hb T1 hT1) _ _).const_mul _
  have hfun : (fun t => ((g t : ℝ) : ℂ)) = fun t => ∑ m ∈ F, ∑ n ∈ F, q m n t := funext hpt
  have hgc : Integrable (fun t => ((g t : ℝ) : ℂ)) := by
    rw [hfun]
    apply integrable_finsetSum
    intro m _
    apply integrable_finsetSum
    intro n _
    exact hqi m n
  have hgi : Integrable g := by
    have := hgc.re
    simpa using this
  have hint : ((∫ t, g t : ℝ) : ℂ) = ∑ m ∈ F, ∑ n ∈ F, b m * (starRingEnd ℂ) (b n) *
      (((Real.pi * T1 ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ((Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4)) : ℝ) : ℂ)) := by
    rw [← integral_complex_ofReal, hfun, integral_finsetSum _ (fun m _ => integrable_finsetSum _
      (fun n _ => hqi m n))]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_finsetSum _ (fun n _ => hqi m n)]
    apply Finset.sum_congr rfl
    intro n _
    simp only [hq]
    rw [integral_const_mul, gauss_term _ T1 hT1]
  have hnormG : ‖((Real.pi * T1 ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ ≤ 2 * T1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [h12, ← Real.sqrt_eq_rpow]
    calc √(Real.pi * T1 ^ 2) ≤ √((2 * T1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.pi_le_four])
      _ = 2 * T1 := Real.sqrt_sq (by linarith)
  have hgle : ∫ t, g t ≤ 2 * T1 * ∑ m ∈ F, ∑ n ∈ F,
      ‖b m‖ * ‖b n‖ * Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4)) := by
    have h1 : ∫ t, g t = (((∫ t, g t : ℝ)) : ℂ).re := by simp
    rw [h1, hint]
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h0 : 0 ≤ ‖b m‖ * ‖b n‖ * Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4)) := by positivity
    calc ‖b m‖ * ‖b n‖ * (‖((Real.pi * T1 ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ *
          Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4)))
        = (‖b m‖ * ‖b n‖ * Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4))) *
            ‖((Real.pi * T1 ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ := by ring
      _ ≤ (‖b m‖ * ‖b n‖ * Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4))) * (2 * T1) :=
          mul_le_mul_of_nonneg_left hnormG h0
      _ = _ := by ring
  have hDcont : Continuous D := by
    simp only [hD]
    exact continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_ee (u n)))
  have hgcont : Continuous g := by
    simp only [hg, hw]
    fun_prop
  have hw1 : ∀ t ∈ Set.Icc (-T1) T1, ‖D t‖ ^ 2 ≤ Real.exp 1 * g t := by
    intro t ht
    have ht2 : t ^ 2 ≤ T1 ^ 2 := by nlinarith [ht.1, ht.2]
    have hwt : Real.exp (-1) ≤ w t := by
      simp only [hw]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, div_le_one (by positivity)]
      exact ht2
    calc ‖D t‖ ^ 2 = Real.exp 1 * (Real.exp (-1) * ‖D t‖ ^ 2) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp 1 * (w t * ‖D t‖ ^ 2) := by gcongr
      _ = Real.exp 1 * g t := by simp only [hg]; ring
  calc ∫ t in (-T1)..T1, ‖D t‖ ^ 2 ≤ ∫ t in (-T1)..T1, Real.exp 1 * g t :=
        intervalIntegral.integral_mono_on (by linarith)
          ((hDcont.norm.pow 2).intervalIntegrable _ _)
          ((continuous_const.mul hgcont).intervalIntegrable _ _) hw1
    _ = Real.exp 1 * ∫ t in (-T1)..T1, g t := intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp 1 * ∫ t, g t := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hgi (Eventually.of_forall (fun t => by positivity))
    _ ≤ Real.exp 1 * (2 * T1 * ∑ m ∈ F, ∑ n ∈ F,
          ‖b m‖ * ‖b n‖ * Real.exp (-(T1 ^ 2 * (u m - u n) ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_left hgle (Real.exp_pos _).le
    _ = _ := by ring

theorem L2 : ∃ C : ℝ, 0 < C ∧ ∀ T1 : ℝ, 4 ≤ T1 → ∀ N0 N1 : ℕ, T1 ^ 10 ≤ N0 →
    ∀ B : ℝ, 0 ≤ B → ∀ b : ℕ → ℂ,
    (∀ n ∈ Finset.Ioc N0 N1, ‖b n‖ ≤ B * ((ArithmeticFunction.vonMangoldt n : ℝ) / n)) →
    ∫ t in (-T1)..T1, ‖∑ n ∈ Finset.Ioc N0 N1, b n * ee (Real.log n) t‖ ^ 2 ≤
      C * B ^ 2 * Real.log N1 := by
  obtain ⟨CS, hCS, hsch⟩ := schur_row
  obtain ⟨CM, hCM, hmert⟩ := sum_vM_div_le
  refine ⟨Real.exp 1 * 2 * CS * CM, by positivity, ?_⟩
  intro T1 hT1 N0 N1 hN0 B hB b hb
  have hT1pos : 0 < T1 := by linarith
  set F := Finset.Ioc N0 N1 with hF
  have hlogN1 : 0 ≤ Real.log N1 := Real.log_natCast_nonneg N1
  rcases Nat.lt_or_ge N1 2 with hN1 | hN1
  · have hN0' : 1 ≤ N0 := by
      have : (1:ℝ) ≤ N0 := le_trans (one_le_pow₀ (by linarith)) hN0
      exact_mod_cast this
    have hFe : F = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hFe]
    simp only [Finset.sum_empty, norm_zero]
    norm_num
    positivity
  have hrow : ∀ m ∈ F, ∑ n ∈ F, ‖b n‖ * Kg T1 m n ≤ B * (CS / T1) := by
    intro m hm
    calc ∑ n ∈ F, ‖b n‖ * Kg T1 m n
        ≤ ∑ n ∈ F, B * ((ArithmeticFunction.vonMangoldt n : ℝ) / n * Kg T1 m n) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hb n hn) (Real.exp_pos _).le
      _ = B * ∑ n ∈ F, (ArithmeticFunction.vonMangoldt n : ℝ) / n * Kg T1 m n := by
          rw [Finset.mul_sum]
      _ ≤ B * (CS / T1) := mul_le_mul_of_nonneg_left (hsch T1 hT1 N0 N1 m hN0 hm) hB
  have hcol : ∑ m ∈ F, ‖b m‖ ≤ B * (CM * Real.log N1) := by
    calc ∑ m ∈ F, ‖b m‖ ≤ ∑ m ∈ F, B * ((ArithmeticFunction.vonMangoldt m : ℝ) / m) :=
          Finset.sum_le_sum hb
      _ = B * ∑ m ∈ F, (ArithmeticFunction.vonMangoldt m : ℝ) / m := by rw [Finset.mul_sum]
      _ ≤ B * ∑ m ∈ Finset.Ioc 0 N1, (ArithmeticFunction.vonMangoldt m : ℝ) / m := by
          apply mul_le_mul_of_nonneg_left _ hB
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            simp only [hF, Finset.mem_Ioc] at hm ⊢
            omega
          · intro m _ _
            exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg m)
      _ ≤ B * (CM * Real.log N1) := mul_le_mul_of_nonneg_left (hmert N1 hN1) hB
  have hg := gauss_mv F b (fun n => Real.log n) T1 hT1pos
  have hdouble : ∑ m ∈ F, ∑ n ∈ F, ‖b m‖ * ‖b n‖ *
      Real.exp (-(T1 ^ 2 * (Real.log m - Real.log n) ^ 2 / 4)) ≤
      (B * (CS / T1)) * (B * (CM * Real.log N1)) := by
    calc _ = ∑ m ∈ F, ‖b m‖ * ∑ n ∈ F, ‖b n‖ * Kg T1 m n := by
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          unfold Kg
          ring
      _ ≤ ∑ m ∈ F, ‖b m‖ * (B * (CS / T1)) :=
          Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (norm_nonneg _))
      _ = (∑ m ∈ F, ‖b m‖) * (B * (CS / T1)) := by rw [Finset.sum_mul]
      _ ≤ (B * (CM * Real.log N1)) * (B * (CS / T1)) :=
          mul_le_mul_of_nonneg_right hcol (by positivity)
      _ = _ := by ring
  calc _ ≤ _ := hg
    _ ≤ Real.exp 1 * (2 * T1) * ((B * (CS / T1)) * (B * (CM * Real.log N1))) :=
        mul_le_mul_of_nonneg_left hdouble (by positivity)
    _ = Real.exp 1 * 2 * CS * CM * B ^ 2 * Real.log N1 := by
        field_simp

/-! ### Derivatives of Dirichlet polynomials -/

/-- The Dirichlet polynomial `∑_{n ∈ F} c_n n^{-it}`. -/
def Dp (F : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ := ∑ n ∈ F, c n * ee (Real.log n) t

/-- Coefficients of the derivative. -/
def cD (c : ℕ → ℂ) : ℕ → ℂ := fun n => c n * (-((Real.log n : ℝ) : ℂ) * I)

theorem hasDerivAt_ee (u t : ℝ) :
    HasDerivAt (fun s : ℝ => ee u s) ((-(u:ℂ) * I) * ee u t) t := by
  have h1 : HasDerivAt (fun s : ℂ => -(u:ℂ) * I * s) (-(u:ℂ) * I * 1) (t:ℂ) :=
    (hasDerivAt_id (t:ℂ)).const_mul (-(u:ℂ) * I)
  have h2 := h1.cexp.comp_ofReal
  have h3 : Complex.exp (-(u:ℂ) * I * (t:ℂ)) * (-(u:ℂ) * I * 1) = (-(u:ℂ) * I) * ee u t := by
    unfold ee; ring
  exact h2.congr_deriv h3

theorem hasDerivAt_Dp (F : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (Dp F c) (Dp F (cD c) t) t := by
  have h := HasDerivAt.sum (u := F) (A := fun n s => c n * ee (Real.log n) s)
    (fun n _ => (hasDerivAt_ee (Real.log n) t).const_mul (c n))
  have hfun : (∑ i ∈ F, fun s => c i * ee (Real.log i) s) = Dp F c := by
    funext s
    simp [Dp, Finset.sum_apply]
  rw [hfun] at h
  refine h.congr_deriv ?_
  unfold Dp cD
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem continuous_Dp (F : Finset ℕ) (c : ℕ → ℂ) : Continuous (Dp F c) := by
  unfold Dp
  exact continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_ee _))

/-! ### Gallagher's lemma -/

theorem gallagher_pt (f g f' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f')
    (hfc : Continuous f) (hgc : Continuous g) (hfg : ∀ t, |f' t| ≤ g t) (δ : ℝ) (hδ : 0 < δ)
    (t0 : ℝ) :
    f t0 ≤ ∫ t in (t0 - δ / 2)..(t0 + δ / 2), (f t / δ + g t) := by
  have hab : t0 - δ / 2 ≤ t0 + δ / 2 := by linarith
  have hfi : ∀ x y, IntervalIntegrable f' volume x y := fun x y => hf'c.intervalIntegrable x y
  have hgi : ∀ x y, IntervalIntegrable g volume x y := fun x y => hgc.intervalIntegrable x y
  have hg0 : ∀ t, 0 ≤ g t := fun t => (abs_nonneg _).trans (hfg t)
  have hpt : ∀ t ∈ Set.Icc (t0 - δ / 2) (t0 + δ / 2),
      f t0 ≤ f t + ∫ s in (t0 - δ / 2)..(t0 + δ / 2), g s := by
    intro t ht
    rcases le_total t t0 with h | h
    · have e1 : ∫ s in t..t0, f' s = f t0 - f t :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hfi _ _)
      have e2 : ∫ s in t..t0, f' s ≤ ∫ s in t..t0, g s :=
        intervalIntegral.integral_mono_on h (hfi _ _) (hgi _ _)
          (fun x _ => (le_abs_self _).trans (hfg x))
      have e3 : ∫ s in t..t0, g s ≤ ∫ s in (t0 - δ / 2)..(t0 + δ / 2), g s :=
        intervalIntegral.integral_mono_interval ht.1 h (by linarith)
          (Eventually.of_forall (fun x => by simpa using hg0 x)) (hgi _ _)
      linarith
    · have e1 : ∫ s in t0..t, f' s = f t - f t0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hfi _ _)
      have e2 : ∫ s in t0..t, (-g s) ≤ ∫ s in t0..t, f' s :=
        intervalIntegral.integral_mono_on h (hgi _ _).neg (hfi _ _)
          (fun x _ => by have := neg_abs_le (f' x); have := hfg x; linarith)
      rw [intervalIntegral.integral_neg] at e2
      have e3 : ∫ s in t0..t, g s ≤ ∫ s in (t0 - δ / 2)..(t0 + δ / 2), g s :=
        intervalIntegral.integral_mono_interval (by linarith) h ht.2
          (Eventually.of_forall (fun x => by simpa using hg0 x)) (hgi _ _)
      linarith
  have hint : ∫ _ in (t0 - δ / 2)..(t0 + δ / 2), f t0 ≤
      ∫ t in (t0 - δ / 2)..(t0 + δ / 2), (f t + ∫ s in (t0 - δ / 2)..(t0 + δ / 2), g s) :=
    intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable _ _)
    ((hfc.add continuous_const).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hfc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hba : t0 + δ / 2 - (t0 - δ / 2) = δ := by ring
  rw [hba] at hint
  rw [intervalIntegral.integral_add ((hfc.div_const δ).intervalIntegrable _ _) (hgi _ _),
    intervalIntegral.integral_div]
  set I := ∫ t in (t0 - δ / 2)..(t0 + δ / 2), f t
  set c := ∫ t in (t0 - δ / 2)..(t0 + δ / 2), g t
  have h2 : f t0 * δ ≤ I + δ * c := by linarith
  calc f t0 = (f t0 * δ) / δ := by field_simp
    _ ≤ (I + δ * c) / δ := by gcongr
    _ = I / δ + c := by field_simp

theorem sum_disjoint_intervals (h : ℝ → ℝ) (hc : Continuous h) (h0 : ∀ t, 0 ≤ h t)
    (P : Finset ℝ) (δ T1 : ℝ) (hδ : 0 < δ) (hT1 : 0 ≤ T1)
    (hP : ∀ t ∈ P, -T1 ≤ t - δ / 2 ∧ t + δ / 2 ≤ T1)
    (hsep : ∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → δ ≤ |t - t'|) :
    ∑ t ∈ P, ∫ s in (t - δ / 2)..(t + δ / 2), h s ≤ ∫ s in (-T1)..T1, h s := by
  have hdisj : Set.Pairwise (↑P)
      (Function.onFun Disjoint fun t => Set.Ioc (t - δ / 2) (t + δ / 2)) := by
    intro t ht t' ht' hne
    rw [Function.onFun, Set.disjoint_left]
    intro s hs hs'
    rw [Set.mem_Ioc] at hs hs'
    have h1 := hsep t ht t' ht' hne
    have h2 : |t - t'| < δ := by
      rw [abs_sub_lt_iff]; constructor <;> linarith
    linarith
  calc ∑ t ∈ P, ∫ s in (t - δ / 2)..(t + δ / 2), h s
      = ∑ t ∈ P, ∫ s in Set.Ioc (t - δ / 2) (t + δ / 2), h s := by
        apply Finset.sum_congr rfl
        intro t _
        rw [intervalIntegral.integral_of_le (by linarith)]
    _ = ∫ s in ⋃ t ∈ P, Set.Ioc (t - δ / 2) (t + δ / 2), h s := by
        rw [integral_biUnion_finset P (fun t _ => measurableSet_Ioc) hdisj
          (fun t _ => hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)]
    _ ≤ ∫ s in Set.Ioc (-T1) T1, h s := by
        apply setIntegral_mono_set (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
          (Eventually.of_forall (fun x => by simpa using h0 x))
        apply LE.le.eventuallyLE
        exact Set.iUnion₂_subset (fun t ht => Set.Ioc_subset_Ioc (hP t ht).1 (hP t ht).2)
    _ = ∫ s in (-T1)..T1, h s := (intervalIntegral.integral_of_le (by linarith)).symm

/-! ### Assembly -/

theorem mv_core (CL : ℝ) (hCL : 0 < CL)
    (hL2 : ∀ T1 : ℝ, 4 ≤ T1 → ∀ N0 N1 : ℕ, T1 ^ 10 ≤ N0 → ∀ B : ℝ, 0 ≤ B → ∀ b : ℕ → ℂ,
      (∀ n ∈ Finset.Ioc N0 N1, ‖b n‖ ≤ B * ((ArithmeticFunction.vonMangoldt n : ℝ) / n)) →
      ∫ t in (-T1)..T1, ‖∑ n ∈ Finset.Ioc N0 N1, b n * ee (Real.log n) t‖ ^ 2 ≤
        CL * B ^ 2 * Real.log N1)
    (T : ℝ) (hT : 3 ≤ T) (N0 N1 : ℕ) (hN0 : (T + 3) ^ 10 ≤ (N0 : ℝ)) (hN01 : N0 < N1)
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n)
    (P : Finset ℝ) (hPT : ∀ t ∈ P, |t| ≤ T)
    (hPsep : ∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → 1 / Real.log (T + 3) ≤ |t - t'|) :
    ∑ t ∈ P, ‖Dp (Finset.Ioc N0 N1) a t‖ ^ 2 ≤ 3 * CL * Real.log N1 ^ 2 := by
  obtain ⟨F, hF⟩ : ∃ F, F = Finset.Ioc N0 N1 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log N1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 1 / Real.log (T + 3) := ⟨_, rfl⟩
  rw [← hF, ← hL]
  have hlT : 1 ≤ Real.log (T + 3) := by
    have h1 : Real.exp 1 ≤ T + 3 := by have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one (by linarith)]; exact hlT
  have hN1r : (T + 3) ^ 10 < (N1 : ℝ) := lt_of_le_of_lt hN0 (by exact_mod_cast hN01)
  have hLT : Real.log (T + 3) ≤ L := by
    have h1 : T + 3 ≤ (T + 3) ^ 10 := by
      calc T + 3 = (T + 3) ^ 1 := (pow_one _).symm
        _ ≤ (T + 3) ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hL]
    exact Real.log_le_log (by linarith) (by linarith)
  have hLpos : 0 < L := by linarith
  have h1δ : 1 / δ = Real.log (T + 3) := by rw [hδ, one_div_one_div]
  have hT10 : (T + 1) ^ 10 ≤ (N0 : ℝ) :=
    le_trans (pow_le_pow_left₀ (by linarith) (by linarith) 10) hN0
  have hDc := continuous_Dp F a
  have hD'c := continuous_Dp F (cD a)
  have hfd : ∀ t, HasDerivAt (fun s => ‖Dp F a s‖ ^ 2)
      (2 * inner ℝ (Dp F a t) (Dp F (cD a) t)) t := fun t => (hasDerivAt_Dp F a t).norm_sq
  have hfg : ∀ t, |2 * inner ℝ (Dp F a t) (Dp F (cD a) t)| ≤
      L * ‖Dp F a t‖ ^ 2 + ‖Dp F (cD a) t‖ ^ 2 / L := by
    intro t
    have h1 := abs_real_inner_le_norm (Dp F a t) (Dp F (cD a) t)
    have h2 : 2 * (‖Dp F a t‖ * ‖Dp F (cD a) t‖) ≤
        L * ‖Dp F a t‖ ^ 2 + ‖Dp F (cD a) t‖ ^ 2 / L := by
      have key : L * ‖Dp F a t‖ ^ 2 + ‖Dp F (cD a) t‖ ^ 2 / L -
          2 * (‖Dp F a t‖ * ‖Dp F (cD a) t‖) = (L * ‖Dp F a t‖ - ‖Dp F (cD a) t‖) ^ 2 / L := by
        field_simp
        ring
      have : 0 ≤ (L * ‖Dp F a t‖ - ‖Dp F (cD a) t‖) ^ 2 / L := by positivity
      linarith
    rw [abs_mul, abs_two]
    linarith
  have hfc : Continuous (fun s => ‖Dp F a s‖ ^ 2) := hDc.norm.pow 2
  have hgc : Continuous (fun s => L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L) :=
    (continuous_const.mul (hDc.norm.pow 2)).add ((hD'c.norm.pow 2).div_const L)
  have hf'c : Continuous (fun s => 2 * inner ℝ (Dp F a s) (Dp F (cD a) s)) :=
    continuous_const.mul (hDc.inner hD'c)
  have hpt : ∀ t ∈ P, ‖Dp F a t‖ ^ 2 ≤ ∫ s in (t - δ / 2)..(t + δ / 2),
      (‖Dp F a s‖ ^ 2 / δ + (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)) :=
    fun t _ => gallagher_pt (fun s => ‖Dp F a s‖ ^ 2)
      (fun s => L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)
      (fun s => 2 * inner ℝ (Dp F a s) (Dp F (cD a) s)) hfd hf'c hfc hgc hfg δ hδpos t
  have hhc : Continuous (fun s => ‖Dp F a s‖ ^ 2 / δ +
      (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)) := (hfc.div_const δ).add hgc
  have hh0 : ∀ s, 0 ≤ ‖Dp F a s‖ ^ 2 / δ + (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L) :=
    fun s => add_nonneg (div_nonneg (by positivity) hδpos.le)
      (add_nonneg (mul_nonneg hLpos.le (by positivity)) (div_nonneg (by positivity) hLpos.le))
  have hsum : ∑ t ∈ P, ∫ s in (t - δ / 2)..(t + δ / 2),
      (‖Dp F a s‖ ^ 2 / δ + (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)) ≤
      ∫ s in (-(T + 1))..(T + 1),
      (‖Dp F a s‖ ^ 2 / δ + (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)) :=
    sum_disjoint_intervals _ hhc hh0 P δ (T + 1) hδpos (by linarith)
      (fun t ht => by
        have := abs_le.mp (hPT t ht)
        constructor <;> linarith)
      (fun t ht t' ht' hne => by rw [hδ]; exact hPsep t ht t' ht' hne)
  have hI0 : (∫ s in (-(T + 1))..(T + 1), ‖Dp F a s‖ ^ 2) ≤ CL * 1 ^ 2 * L := by
    rw [hL, hF]
    exact hL2 (T + 1) (by linarith) N0 N1 hT10 1 zero_le_one a
      (fun n _ => by rw [one_mul]; exact ha n)
  have hI1 : (∫ s in (-(T + 1))..(T + 1), ‖Dp F (cD a) s‖ ^ 2) ≤ CL * L ^ 2 * L := by
    rw [hL, hF]
    refine hL2 (T + 1) (by linarith) N0 N1 hT10 (Real.log N1) (Real.log_natCast_nonneg N1)
      (cD a) (fun n hn => ?_)
    have hn' := Finset.mem_Ioc.mp hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlogN : Real.log n ≤ Real.log N1 :=
      Real.log_le_log (by linarith) (by exact_mod_cast hn'.2)
    unfold cD
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlogn]
    calc ‖a n‖ * Real.log n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n * Real.log N1 :=
          mul_le_mul (ha n) hlogN hlogn (by positivity)
      _ = _ := by ring
  have hint : ∫ s in (-(T + 1))..(T + 1),
      (‖Dp F a s‖ ^ 2 / δ + (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)) =
      (∫ s in (-(T + 1))..(T + 1), ‖Dp F a s‖ ^ 2) / δ +
        L * (∫ s in (-(T + 1))..(T + 1), ‖Dp F a s‖ ^ 2) +
        (∫ s in (-(T + 1))..(T + 1), ‖Dp F (cD a) s‖ ^ 2) / L := by
    have hc0 : Continuous (fun s => ‖Dp F a s‖ ^ 2 / δ) := by fun_prop
    have hc1 : Continuous (fun s => L * ‖Dp F a s‖ ^ 2) := by fun_prop
    have hc2 : Continuous (fun s => ‖Dp F (cD a) s‖ ^ 2 / L) := by fun_prop
    rw [intervalIntegral.integral_add (hc0.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _), intervalIntegral.integral_add
      (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div]
    ring
  set I0 := ∫ s in (-(T + 1))..(T + 1), ‖Dp F a s‖ ^ 2
  set I1 := ∫ s in (-(T + 1))..(T + 1), ‖Dp F (cD a) s‖ ^ 2
  have e1 : I0 / δ ≤ CL * L * L := by
    rw [div_eq_mul_one_div, h1δ]
    calc I0 * Real.log (T + 3) ≤ (CL * 1 ^ 2 * L) * Real.log (T + 3) :=
          mul_le_mul_of_nonneg_right hI0 (by linarith)
      _ ≤ (CL * 1 ^ 2 * L) * L := mul_le_mul_of_nonneg_left hLT (by positivity)
      _ = CL * L * L := by ring
  have e2 : L * I0 ≤ CL * L * L := by
    calc L * I0 ≤ L * (CL * 1 ^ 2 * L) := mul_le_mul_of_nonneg_left hI0 hLpos.le
      _ = CL * L * L := by ring
  have e3 : I1 / L ≤ CL * L * L := by
    rw [div_le_iff₀ hLpos]
    calc I1 ≤ CL * L ^ 2 * L := hI1
      _ = CL * L * L * L := by ring
  calc ∑ t ∈ P, ‖Dp F a t‖ ^ 2
      ≤ ∑ t ∈ P, ∫ s in (t - δ / 2)..(t + δ / 2),
          (‖Dp F a s‖ ^ 2 / δ + (L * ‖Dp F a s‖ ^ 2 + ‖Dp F (cD a) s‖ ^ 2 / L)) :=
        Finset.sum_le_sum hpt
    _ ≤ _ := hsum
    _ = I0 / δ + L * I0 + I1 / L := hint
    _ ≤ CL * L * L + CL * L * L + CL * L * L := by linarith
    _ = 3 * CL * L ^ 2 := by ring

end HM

/-- [HM] Mean value of prime Dirichlet polynomials at well-spaced points (log-free). -/
theorem mean_value : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T → ∀ N0 N1 : ℕ, (T + 3) ^ 10 ≤ (N0 : ℝ) →
    ∀ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n) →
    ∀ P : Finset ℝ, (∀ t ∈ P, |t| ≤ T) →
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → 1 / Real.log (T + 3) ≤ |t - t'|) →
    ∑ t ∈ P, ‖∑ n ∈ Finset.Ioc N0 N1, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 ≤
      C * Real.log N1 ^ 2 := by
  obtain ⟨CL, hCL, hL2⟩ := HM.L2
  refine ⟨3 * CL, by positivity, ?_⟩
  intro T hT N0 N1 hN0 a ha P hPT hPsep
  have hrw : ∀ t : ℝ, ∑ n ∈ Finset.Ioc N0 N1, a n * (n : ℂ) ^ (-((t : ℂ) * I)) =
      HM.Dp (Finset.Ioc N0 N1) a t := by
    intro t
    unfold HM.Dp
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    rw [HM.cpow_eq_ee n hn0 t]
  simp_rw [hrw]
  rcases Nat.lt_or_ge N0 N1 with h01 | h01
  · exact HM.mv_core CL hCL hL2 T hT N0 N1 hN0 h01 a ha P hPT hPsep
  · have hE : Finset.Ioc N0 N1 = ∅ := Finset.Ioc_eq_empty (by omega)
    have h0 : ∀ t, HM.Dp (Finset.Ioc N0 N1) a t = 0 := by
      intro t
      rw [hE]
      simp [HM.Dp]
    simp only [h0, norm_zero]
    norm_num
    positivity



-- ===== from EM.lean =====


namespace EM

/-! ### Complex powers of positive reals -/

theorem cpow_exp {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ((a : ℝ) : ℂ) ^ s = Complex.exp ((Real.log a : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), Complex.ofReal_log ha.le]

theorem cpow_div' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    ((a / b : ℝ) : ℂ) ^ s = ((a : ℝ) : ℂ) ^ s / ((b : ℝ) : ℂ) ^ s := by
  rw [cpow_exp (div_pos ha hb), cpow_exp ha, cpow_exp hb, Real.log_div ha.ne' hb.ne',
    ← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem inv_cpow_neg {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = ((y : ℝ) : ℂ) ^ s := by
  rw [cpow_exp (inv_pos.mpr hy), cpow_exp hy, Real.log_inv]
  congr 1
  push_cast
  ring

/-! ### The bound for `Wk` -/

theorem norm_exp_sub_one_div_le {M : ℝ} (hM : 0 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖(Complex.exp ((M : ℂ) * s) - 1) / s‖ ≤ (Real.exp (M * s.re) - 1) / s.re := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have h1 : (Complex.exp ((M : ℂ) * s) - 1) / s = ∫ v in (0:ℝ)..M, Complex.exp (s * v) := by
    rw [integral_exp_mul_complex hs0]
    simp [mul_comm]
  have h2 : ∫ v in (0:ℝ)..M, Real.exp (s.re * v) = (Real.exp (M * s.re) - 1) / s.re := by
    rw [intervalIntegral.integral_comp_mul_left (fun v => Real.exp v) hs.ne', integral_exp]
    simp only [smul_eq_mul, mul_zero, Real.exp_zero]
    rw [mul_comm s.re M, div_eq_inv_mul]
  rw [h1, ← h2]
  refine intervalIntegral.norm_integral_le_of_norm_le hM ?_ ?_
  · refine Filter.Eventually.of_forall (fun v _ => ?_)
    rw [Complex.norm_exp]
    simp
  · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (s.re * v)).intervalIntegrable _ _

theorem exp_mul_le {M σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (Real.exp (M * σ) - 1) / σ ≤ Real.exp M - 1 := by
  have h := rpow_one_add_le_one_add_mul_self (s := Real.exp M - 1)
    (by linarith [Real.exp_pos M]) hσ.le hσ1
  have e : (1 + (Real.exp M - 1)) = Real.exp M := by ring
  rw [e, ← Real.exp_mul] at h
  rw [div_le_iff₀ hσ]
  nlinarith

theorem Wk_eq (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) (s : ℂ) :
    Wk x δ s = Complex.exp ((Real.log x : ℂ) * s) *
      ((Complex.exp ((Real.log (1 + δ) : ℂ) * s) - 1) / s) *
      ((Complex.exp (((3 * Real.log (1 + δ) : ℝ) : ℂ) * s) - 1) / s) := by
  have h1 : (0:ℝ) < 1 + δ := by linarith
  have p : ∀ k : ℕ, ((x * (1 + δ) ^ k : ℝ) : ℂ) ^ s =
      Complex.exp ((Real.log x : ℂ) * s) * Complex.exp ((Real.log (1 + δ) : ℂ) * s) ^ k := by
    intro k
    rw [cpow_exp (by positivity), Real.log_mul hx.ne' (by positivity), Real.log_pow,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have p1 : ((x * (1 + δ) : ℝ) : ℂ) ^ s =
      Complex.exp ((Real.log x : ℂ) * s) * Complex.exp ((Real.log (1 + δ) : ℂ) * s) := by
    simpa only [pow_one] using p 1
  have p0 : ((x : ℝ) : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
    simpa only [pow_zero, mul_one] using p 0
  have e3 : Complex.exp (((3 * Real.log (1 + δ) : ℝ) : ℂ) * s) =
      Complex.exp ((Real.log (1 + δ) : ℂ) * s) ^ 3 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold Wk
  rw [p 4, p 3, p1, p0, e3]
  ring

end EM

theorem Wk_bound : ∀ x δ : ℝ, 0 < x → 0 < δ → ∀ s : ℂ, 0 < s.re → s.re ≤ 1 →
    ‖Wk x δ s‖ ≤ x ^ (s.re - 1) * (δ * x * ((1 + δ) ^ 3 - 1)) := by
  intro x δ hx hδ s hs hs1
  have h1 : (0:ℝ) < 1 + δ := by linarith
  have hL : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  rw [EM.Wk_eq x δ hx hδ s, norm_mul, norm_mul]
  have A := EM.norm_exp_sub_one_div_le hL hs
  have B := EM.norm_exp_sub_one_div_le (by linarith : 0 ≤ 3 * Real.log (1 + δ)) hs
  have A' := EM.exp_mul_le (M := Real.log (1 + δ)) hs hs1
  have B' := EM.exp_mul_le (M := 3 * Real.log (1 + δ)) hs hs1
  have e3 : Real.exp (3 * Real.log (1 + δ)) = (1 + δ) ^ 3 := by
    rw [show (3:ℝ) * Real.log (1 + δ) = ((3:ℕ):ℝ) * Real.log (1 + δ) by norm_num,
      Real.exp_nat_mul, Real.exp_log h1]
  rw [Real.exp_log h1] at A'
  rw [e3] at B'
  have hE : ‖Complex.exp ((Real.log x : ℂ) * s)‖ = x ^ s.re := by
    rw [Complex.norm_exp, Complex.re_ofReal_mul, Real.rpow_def_of_pos hx]
  have hN1 : ‖(Complex.exp ((Real.log (1 + δ) : ℂ) * s) - 1) / s‖ ≤ δ := by
    linarith
  have hN2 : ‖(Complex.exp (((3 * Real.log (1 + δ) : ℝ) : ℂ) * s) - 1) / s‖ ≤
      (1 + δ) ^ 3 - 1 := by
    linarith
  rw [hE]
  have hxs : 0 ≤ x ^ s.re := Real.rpow_nonneg hx.le _
  calc x ^ s.re * ‖(Complex.exp ((Real.log (1 + δ) : ℂ) * s) - 1) / s‖ *
        ‖(Complex.exp (((3 * Real.log (1 + δ) : ℝ) : ℂ) * s) - 1) / s‖
      ≤ x ^ s.re * δ * ((1 + δ) ^ 3 - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hN1 hxs) hN2 (norm_nonneg _)
        positivity
    _ = x ^ (s.re - 1) * (δ * x * ((1 + δ) ^ 3 - 1)) := by
        rw [Real.rpow_sub_one hx.ne']
        field_simp

namespace EM

/-! ### Mellin transform of `log⁺(1/u)` -/

/-- indicator of `(0,1]`. -/
def f1 : ℝ → ℂ := Set.indicator (Set.Ioc 0 1) (fun _ => (1 : ℂ))

/-- `u ↦ log⁺ (1/u)`. -/
def gl : ℝ → ℂ := fun t => ((lp t⁻¹ : ℝ) : ℂ)

theorem mellin_log_f1 {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • f1 t) s ∧
      mellin (fun t => Real.log t • f1 t) s = -(s ^ 2)⁻¹ := by
  have hint : Integrable f1 :=
    (integrableOn_const (s := Set.Ioc (0:ℝ) 1) (C := (1:ℂ)) measure_Ioc_lt_top.ne).integrable_indicator
      measurableSet_Ioc
  have hloc : LocallyIntegrableOn f1 (Set.Ioi 0) := hint.locallyIntegrable.locallyIntegrableOn _
  have hzero : ∀ t : ℝ, 1 < t → f1 t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hle : ∀ t, ‖f1 t‖ ≤ 1 := by
    intro t
    unfold f1
    by_cases h : t ∈ Set.Ioc (0:ℝ) 1 <;> simp [h]
  have hf_top : f1 =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
    refine (Asymptotics.isBigO_zero _ _).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact (hzero t ht).symm
  have hf_bot : f1 =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hle t
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hloc hf_top (by linarith) hf_bot hs
  refine ⟨hconv, ?_⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have hev : (fun z : ℂ => z⁻¹) =ᶠ[𝓝 s] mellin f1 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    have := (hasMellin_one_Ioc hz).2
    rw [one_div] at this
    exact this.symm
  exact (hder.congr_of_eventuallyEq hev).unique (hasDerivAt_inv hs0)

theorem gl_eq {t : ℝ} (ht : 0 < t) : gl t = -(Real.log t • f1 t) := by
  unfold gl f1 lp
  by_cases h : t ≤ 1
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) 1 from ⟨ht, h⟩), Real.log_inv,
      max_eq_left (by linarith [Real.log_nonpos ht.le h])]
    simp
  · push Not at h
    rw [Set.indicator_of_notMem (fun hh => by linarith [hh.2]), Real.log_inv,
      max_eq_right (by linarith [Real.log_pos h])]
    simp

theorem mellin_gl {s : ℂ} (hs : 0 < s.re) : MellinConvergent gl s ∧ mellin gl s = 1 / s ^ 2 := by
  obtain ⟨hc, hm⟩ := mellin_log_f1 hs
  constructor
  · unfold MellinConvergent at hc ⊢
    refine hc.neg.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.neg_apply, gl_eq ht, smul_neg]
  · have h1 : mellin gl s = mellin (fun t => -(Real.log t • f1 t)) s := by
      unfold mellin
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [gl_eq ht])
    have h2 : mellin (fun t => -(Real.log t • f1 t)) s = -mellin (fun t => Real.log t • f1 t) s := by
      unfold mellin
      simp only [smul_neg, integral_neg]
    rw [h1, h2, hm, neg_neg, one_div]

/-! ### The kernel `y^s / s^2` on a vertical line -/

/-- `y^(c+it) / (c+it)^2`. -/
def K (y c t : ℝ) : ℂ := ((y : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) ^ 2

theorem normSq_s (c t : ℝ) : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

theorem s_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem norm_K {y : ℝ} (c : ℝ) (hy : 0 < y) (t : ℝ) : ‖K y c t‖ = y ^ c / (c ^ 2 + t ^ 2) := by
  unfold K
  rw [norm_div, norm_pow, normSq_s, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

theorem K_cont {y c : ℝ} (hy : 0 < y) (hc : 0 < c) : Continuous (K y c) := by
  unfold K
  refine Continuous.div ?_ (by fun_prop) (fun t => pow_ne_zero 2 (s_ne_zero hc t))
  exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))

theorem int_inv (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) ∧ ∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹ = Real.pi / a := by
  have heq : (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) = fun t => (a ^ 2)⁻¹ * (1 + (t / a) ^ 2)⁻¹ := by
    funext t
    field_simp
  rw [heq]
  refine ⟨(integrable_inv_one_add_sq.comp_div ha.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) a,
    integral_univ_inv_one_add_sq, abs_of_pos ha, smul_eq_mul]
  field_simp

theorem K_int {y c : ℝ} (hy : 0 < y) (hc : 0 < c) : Integrable (K y c) := by
  refine Integrable.mono' ((int_inv c hc).1.const_mul (y ^ c)) (K_cont hy hc).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_K c hy]
  exact le_of_eq (div_eq_mul_inv _ _)

theorem K_integral {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    ∫ t : ℝ, K y c t = ((2 * Real.pi * lp y : ℝ) : ℂ) := by
  have hcs : 0 < ((c : ℂ)).re := by simpa using hc
  obtain ⟨hconv, -⟩ := mellin_gl hcs
  have hvert : Complex.VerticalIntegrable (mellin gl) c := by
    unfold Complex.VerticalIntegrable
    refine (K_int one_pos hc).congr (Filter.Eventually.of_forall fun t => ?_)
    have hre : 0 < ((c : ℂ) + t * I).re := by simpa using hc
    show K 1 c t = mellin gl ((c : ℂ) + t * I)
    rw [(mellin_gl hre).2]
    unfold K
    rw [Complex.ofReal_one, Complex.one_cpow]
  have hcont : ContinuousAt gl y⁻¹ := by
    unfold gl lp
    have hy' : y⁻¹ ≠ 0 := inv_ne_zero hy.ne'
    have : ContinuousAt (fun t : ℝ => max (Real.log t⁻¹) 0) y⁻¹ :=
      ((Real.continuousAt_log (inv_ne_zero hy')).comp (continuousAt_inv₀ hy')).max
        continuousAt_const
    exact Complex.continuous_ofReal.continuousAt.comp this
  have h := mellinInv_mellin_eq c gl (inv_pos.mpr hy) hconv hvert hcont
  unfold mellinInv at h
  have hint : (∫ t : ℝ, ((y⁻¹ : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin gl ((c : ℂ) + t * I)) =
      ∫ t : ℝ, K y c t := by
    congr 1
    funext t
    have hre : 0 < ((c : ℂ) + t * I).re := by simpa using hc
    rw [(mellin_gl hre).2, inv_cpow_neg hy, smul_eq_mul]
    unfold K
    ring
  rw [hint] at h
  have hgl : gl y⁻¹ = ((lp y : ℝ) : ℂ) := by
    unfold gl
    rw [inv_inv]
  rw [hgl, Complex.real_smul] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at h ⊢
  rw [← h]
  field_simp

theorem K4_integral {a b d e c : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e)
    (hc : 0 < c) :
    Integrable (fun t => K a c t - K b c t - K d c t + K e c t) ∧
      ∫ t : ℝ, (K a c t - K b c t - K d c t + K e c t) =
        ((2 * Real.pi * (lp a - lp b - lp d + lp e) : ℝ) : ℂ) := by
  have ia := K_int ha hc
  have ib := K_int hb hc
  have id := K_int hd hc
  have ie := K_int he hc
  have i1 : Integrable (fun t => K a c t - K b c t) := ia.sub ib
  have i2 : Integrable (fun t => K a c t - K b c t - K d c t) := i1.sub id
  refine ⟨i2.add ie, ?_⟩
  rw [integral_add i2 ie, integral_sub i1 id, integral_sub ia ib, K_integral ha hc,
    K_integral hb hc, K_integral hd hc, K_integral he hc]
  push_cast
  ring

theorem Wk_K (x δ c t : ℝ) : Wk x δ ((c : ℂ) + t * I) =
    K (x * (1 + δ) ^ 4) c t - K (x * (1 + δ) ^ 3) c t - K (x * (1 + δ)) c t + K x c t := by
  unfold Wk K
  ring

theorem norm_Wk_le {x δ c : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hc : 0 < c) (t : ℝ) :
    ‖Wk x δ ((c : ℂ) + t * I)‖ ≤ 4 * (x * (1 + δ) ^ 4) ^ c / (c ^ 2 + t ^ 2) := by
  have h1 : (1:ℝ) ≤ 1 + δ := by linarith
  have l1 : x ≤ x * (1 + δ) := le_mul_of_one_le_right hx.le h1
  have l2 : x * (1 + δ) ≤ x * (1 + δ) ^ 3 :=
    mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 3)) hx.le
  have l3 : x * (1 + δ) ^ 3 ≤ x * (1 + δ) ^ 4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by norm_num)) hx.le
  have hD : 0 < c ^ 2 + t ^ 2 := by positivity
  have b : ∀ y : ℝ, 0 < y → y ≤ x * (1 + δ) ^ 4 →
      ‖K y c t‖ ≤ (x * (1 + δ) ^ 4) ^ c / (c ^ 2 + t ^ 2) := by
    intro y hy hyx
    rw [norm_K c hy]
    gcongr
  rw [Wk_K]
  have n1 := norm_add_le (K (x * (1 + δ) ^ 4) c t - K (x * (1 + δ) ^ 3) c t - K (x * (1 + δ)) c t)
    (K x c t)
  have n2 := norm_sub_le (K (x * (1 + δ) ^ 4) c t - K (x * (1 + δ) ^ 3) c t) (K (x * (1 + δ)) c t)
  have n3 := norm_sub_le (K (x * (1 + δ) ^ 4) c t) (K (x * (1 + δ) ^ 3) c t)
  have b3 := b (x * (1 + δ) ^ 4) (by positivity) le_rfl
  have b2 := b (x * (1 + δ) ^ 3) (by positivity) l3
  have b1 := b (x * (1 + δ)) (by positivity) (l2.trans l3)
  have b0 := b x hx (l1.trans (l2.trans l3))
  have : 4 * (x * (1 + δ) ^ 4) ^ c / (c ^ 2 + t ^ 2) =
      4 * ((x * (1 + δ) ^ 4) ^ c / (c ^ 2 + t ^ 2)) := by ring
  rw [this]
  linarith

end EM

namespace EM

/-! ### Summation over `n` -/

theorem term_n_eq (x δ c : ℝ) (hx : 0 < x) (hδ : 0 < δ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (K (x * (1 + δ) ^ 4 / n) c t - K (x * (1 + δ) ^ 3 / n) c t
          - K (x * (1 + δ) / n) c t + K (x / n) c t) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn]
  unfold K Wk
  rw [cpow_div' (by positivity) hn', cpow_div' (by positivity) hn', cpow_div' (by positivity) hn',
    cpow_div' hx hn', Complex.ofReal_natCast]
  ring

theorem F_integral (x δ c : ℝ) (hx : 0 < x) (hδ : 0 < δ) (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ => Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n) ∧
    ∫ t : ℝ, Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n =
      ((2 * Real.pi * ((ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e : (fun t : ℝ => Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n) =
      fun t => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (K (x * (1 + δ) ^ 4 / n) c t - K (x * (1 + δ) ^ 3 / n) c t
          - K (x * (1 + δ) / n) c t + K (x / n) c t) :=
    funext (term_n_eq x δ c hx hδ hn)
  obtain ⟨hi, hv⟩ := K4_integral (a := x * (1 + δ) ^ 4 / n) (b := x * (1 + δ) ^ 3 / n)
    (d := x * (1 + δ) / n) (e := x / n) (by positivity) (by positivity) (by positivity)
    (by positivity) hc
  rw [e]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hv]
  unfold gw
  push_cast
  ring

theorem gw_zero (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10) (u : ℝ) (hu : 2 * x < u) :
    gw x δ u = 0 := by
  have hu0 : 0 < u := by linarith
  have h4 : (1 + δ) ^ 4 ≤ 2 := by
    have : (1 + δ) ^ 4 ≤ (1 + 1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    linarith [show (1 + 1 / 10 : ℝ) ^ 4 ≤ 2 by norm_num]
  have h1 : (1:ℝ) ≤ 1 + δ := by linarith
  have key : ∀ a : ℝ, 0 < a → a ≤ 2 * x → lp (a / u) = 0 := by
    intro a ha hax
    unfold lp
    apply max_eq_right
    apply Real.log_nonpos (div_pos ha hu0).le
    rw [div_le_one hu0]
    linarith
  have l3 : x * (1 + δ) ^ 3 ≤ x * (1 + δ) ^ 4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by norm_num)) hx.le
  have l2 : x * (1 + δ) ≤ x * (1 + δ) ^ 3 :=
    mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 3)) hx.le
  have l1 : x ≤ x * (1 + δ) := le_mul_of_one_le_right hx.le h1
  have hb : x * (1 + δ) ^ 4 ≤ 2 * x := by nlinarith
  unfold gw
  rw [key _ (by positivity) hb, key _ (by positivity) (l3.trans hb),
    key _ (by positivity) (l2.trans (l3.trans hb)), key _ hx (l1.trans (l2.trans (l3.trans hb)))]
  ring

theorem sum_identity (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10) (c : ℝ) (hc : 1 < c) :
    ∫ t : ℝ, Wk x δ ((c : ℂ) + t * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) =
      ((2 * Real.pi * ∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n : ℝ) : ℂ) := by
  have hc0 : 0 < c := by linarith
  have hF := fun n => F_integral x δ c hx hδ hc0 n
  have hW : Integrable (fun t : ℝ => Wk x δ ((c : ℂ) + t * I)) := by
    have := (K4_integral (a := x * (1 + δ) ^ 4) (b := x * (1 + δ) ^ 3) (d := x * (1 + δ)) (e := x)
      (by positivity) (by positivity) (by positivity) hx hc0).1
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Wk_K]
  have hnorm : ∀ n : ℕ, (fun t : ℝ => ‖Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n‖) =
      fun t : ℝ => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ *
        ‖Wk x δ ((c : ℂ) + t * I)‖ := by
    intro n
    funext t
    rw [norm_mul, mul_comm, LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hsumm : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n‖) := by
    refine ((summable_norm_iff.mpr hsumm).mul_right (∫ t : ℝ, ‖Wk x δ ((c : ℂ) + t * I)‖)).congr
      (fun n => ?_)
    rw [hnorm n, integral_const_mul]
  have key := integral_tsum_of_summable_integral_norm (fun n => (hF n).1) hsum
  have hG : (fun t : ℝ => Wk x δ ((c : ℂ) + t * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)) =
      fun t : ℝ => ∑' n : ℕ, Wk x δ ((c : ℂ) + t * I) *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n := by
    funext t
    rw [LSeries, tsum_mul_left]
  rw [hG, ← key, tsum_congr (fun n => (hF n).2)]
  rw [tsum_eq_sum (s := Finset.range (⌊2 * x⌋₊ + 1)) (fun n hn => ?_)]
  · push_cast
    rw [Finset.mul_sum]
  · have hn2 : 2 * x < n := by
      rw [Finset.mem_range, not_lt] at hn
      exact Nat.lt_of_floor_lt (Nat.lt_of_succ_le hn)
    rw [gw_zero x δ hx hδ hδ1 n hn2]
    simp

/-! ### Bounds near `s = 1` -/

theorem Mbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ 3 →
    ‖deriv Z (σ : ℂ) / Z (σ : ℂ)‖ ≤ M := by
  have hZ : ∀ σ : ℝ, 1 ≤ σ → Z (σ : ℂ) ≠ 0 := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ with h | h
    · rw [← h, Complex.ofReal_one, Z_one]
      exact one_ne_zero
    · have hne : (σ : ℂ) ≠ 1 := by
        intro h'
        have := congrArg Complex.re h'
        simp at this
        linarith
      rw [Z_eq hne]
      refine mul_ne_zero (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re ?_)
      simp
      linarith
  have hd : Continuous (deriv Z) := (Z_diff.contDiff (n := 1)).continuous_deriv le_rfl
  have hcont : ContinuousOn (fun σ : ℝ => deriv Z (σ : ℂ) / Z (σ : ℂ)) (Set.Icc 1 3) :=
    ((hd.comp Complex.continuous_ofReal).continuousOn).div
      ((Z_diff.continuous.comp Complex.continuous_ofReal).continuousOn)
      (fun σ hσ => hZ σ hσ.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max M 0, le_max_right _ _, fun σ h1 h3 => (hM σ ⟨h1, h3⟩).trans (le_max_left _ _)⟩

theorem term_real (c : ℝ) (n : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n =
      ((‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have e : LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n =
      (((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ c : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [e, Complex.norm_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))]

theorem R_bound {M : ℝ} (hM : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 3 → ‖deriv Z (σ : ℂ) / Z (σ : ℂ)‖ ≤ M)
    {c : ℝ} (hc : 1 < c) (hc3 : c ≤ 3) :
    ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ ≤
      M + 1 / (c - 1) := by
  have hLf := Lf_eq_LSeries (s := (c : ℂ)) (by simpa using hc)
  have hLS : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) =
      ((∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    unfold LSeries
    exact tsum_congr (fun n => term_real c n)
  have hR0 : 0 ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ :=
    tsum_nonneg (fun n => norm_nonneg _)
  have h1 : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ)‖ =
      ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
    rw [hLS, Complex.norm_of_nonneg hR0]
  rw [← h1, ← hLf]
  unfold Lf
  have hc1 : 0 < c - 1 := by linarith
  have e : (1 : ℂ) / ((c : ℂ) - 1) = ((1 / (c - 1) : ℝ) : ℂ) := by push_cast; ring
  calc ‖-deriv Z (c : ℂ) / Z (c : ℂ) + 1 / ((c : ℂ) - 1)‖
      ≤ ‖-deriv Z (c : ℂ) / Z (c : ℂ)‖ + ‖1 / ((c : ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ M + 1 / (c - 1) := by
      apply add_le_add
      · rw [neg_div, norm_neg]
        exact hM c hc.le hc3
      · rw [e, Complex.norm_of_nonneg (by positivity)]

theorem X3_pow (x δ : ℝ) (hx : 2 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10) :
    (x * (1 + δ) ^ 4) ^ (1 + 1 / Real.log x) ≤ 18 * x := by
  have hx0 : 0 < x := by linarith
  have hX : 0 < x * (1 + δ) ^ 4 := by positivity
  have h4 : (1 + δ) ^ 4 ≤ 2 := by
    have : (1 + δ) ^ 4 ≤ (1 + 1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    linarith [show (1 + 1 / 10 : ℝ) ^ 4 ≤ 2 by norm_num]
  have hb : x * (1 + δ) ^ 4 ≤ 2 * x := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx : 0 < Real.log x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hl2
  have hlog : Real.log (x * (1 + δ) ^ 4) ≤ 2 * Real.log x := by
    calc Real.log (x * (1 + δ) ^ 4) ≤ Real.log (2 * x) := Real.log_le_log hX hb
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ 2 * Real.log x := by linarith
  rw [Real.rpow_add hX, Real.rpow_one, Real.rpow_def_of_pos hX]
  have he : Real.exp (Real.log (x * (1 + δ) ^ 4) * (1 / Real.log x)) ≤ 9 := by
    have h2 : Real.log (x * (1 + δ) ^ 4) * (1 / Real.log x) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hlx]
      linarith
    calc Real.exp (Real.log (x * (1 + δ) ^ 4) * (1 / Real.log x)) ≤ Real.exp 2 :=
          Real.exp_le_exp.mpr h2
      _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 9 := by
          have := Real.exp_one_lt_d9
          nlinarith [Real.exp_pos 1]
  calc x * (1 + δ) ^ 4 * Real.exp (Real.log (x * (1 + δ) ^ 4) * (1 / Real.log x))
      ≤ (2 * x) * 9 := mul_le_mul hb he (Real.exp_pos _).le (by positivity)
    _ = 18 * x := by ring

end EM

namespace EM

theorem LS_cont {c : ℝ} (hc : 1 < c) :
    Continuous (fun t : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((c : ℂ) + t * I)) := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤
      ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
  refine (LSeries_differentiableOn _).continuousOn.comp_continuous (by fun_prop) (fun t => ?_)
  have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  show LSeries.abscissaOfAbsConv _ < (((c : ℂ) + (t : ℂ) * I).re : EReal)
  rw [hre]
  exact habs.trans_lt (by exact_mod_cast hc)

theorem LS_bound {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)‖ ≤
      ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
  have hsumm : Summable (fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
  have heq : (fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n‖) =
      fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
    funext n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  unfold LSeries
  calc ‖∑' n, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((c : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm (by rw [heq]; exact hsumm)
    _ = _ := by rw [heq]

end EM

theorem perron_trunc : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ T : ℝ, 1 ≤ T →
    ‖((∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n : ℝ) : ℂ) -
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ in (-T)..T,
        Wk x δ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)‖ ≤ C * x * Real.log x / T := by
  obtain ⟨M, hM0, hM⟩ := EM.Mbound
  refine ⟨72 * (M / Real.log 2 + 1), ?_⟩
  intro x hx δ hδ hδ1 T hT
  have hx0 : 0 < x := by linarith
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlx : 0 < Real.log x := by linarith
  have hT0 : 0 < T := by linarith
  have hXc : (x * (1 + δ) ^ 4) ^ (1 + 1 / Real.log x) ≤ 18 * x := EM.X3_pow x δ hx hδ hδ1
  have hfull := EM.sum_identity x δ hx0 hδ hδ1 (1 + 1 / Real.log x)
    (by have : 0 < 1 / Real.log x := by positivity
        linarith)
  have hRb := EM.R_bound hM (c := 1 + 1 / Real.log x)
    (by have : 0 < 1 / Real.log x := by positivity
        linarith)
    (by have : 1 / Real.log x ≤ 2 := by rw [div_le_iff₀ hlx]; linarith
        linarith)
  have hcont := EM.LS_cont (c := 1 + 1 / Real.log x)
    (by have : 0 < 1 / Real.log x := by positivity
        linarith)
  have hLSb := EM.LS_bound (c := 1 + 1 / Real.log x)
    (by have : 0 < 1 / Real.log x := by positivity
        linarith)
  generalize hc : 1 + 1 / Real.log x = c at hXc hfull hRb hcont hLSb ⊢
  have hc1 : 1 < c := by
    rw [← hc]
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have hc0 : 0 < c := by linarith
  have e1 : 1 / (c - 1) = Real.log x := by rw [← hc, add_sub_cancel_left, one_div_one_div]
  rw [e1] at hRb
  generalize hR : ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (c : ℂ) n‖ = R at hRb hLSb
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hLSb 0)
  generalize hS : (∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1),
    (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n) = S at hfull ⊢
  generalize hX : x * (1 + δ) ^ 4 = X at hXc
  have hX0 : 0 < X := by rw [← hX]; positivity
  -- continuity and bounds of the integrand
  have hWc : Continuous (fun t : ℝ => Wk x δ ((c : ℂ) + t * I)) := by
    have : (fun t : ℝ => Wk x δ ((c : ℂ) + t * I)) = fun t => EM.K (x * (1 + δ) ^ 4) c t -
        EM.K (x * (1 + δ) ^ 3) c t - EM.K (x * (1 + δ)) c t + EM.K x c t :=
      funext (fun t => EM.Wk_K x δ c t)
    rw [this]
    exact (((EM.K_cont (by positivity) hc0).sub (EM.K_cont (by positivity) hc0)).sub
      (EM.K_cont (by positivity) hc0)).add (EM.K_cont hx0 hc0)
  have hGc : Continuous (fun t : ℝ => Wk x δ ((c : ℂ) + t * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)) :=
    hWc.mul hcont
  have hGb : ∀ t : ℝ, ‖Wk x δ ((c : ℂ) + t * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)‖ ≤
      4 * X ^ c * R * (c ^ 2 + t ^ 2)⁻¹ := by
    intro t
    rw [norm_mul]
    have h1 := EM.norm_Wk_le hx0 hδ hc0 t
    rw [hX] at h1
    calc ‖Wk x δ ((c : ℂ) + t * I)‖ *
          ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)‖
        ≤ 4 * X ^ c / (c ^ 2 + t ^ 2) * R :=
          mul_le_mul h1 (hLSb t) (norm_nonneg _) (by positivity)
      _ = 4 * X ^ c * R * (c ^ 2 + t ^ 2)⁻¹ := by ring
  have hGint : Integrable (fun t : ℝ => Wk x δ ((c : ℂ) + t * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)) :=
    Integrable.mono' ((EM.int_inv c hc0).1.const_mul (4 * X ^ c * R)) hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall hGb)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hsplit := integral_add_compl (measurableSet_Ioc (a := -T) (b := T)) hGint
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : ((S : ℝ) : ℂ) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ in Set.Ioc (-T) T, Wk x δ ((c : ℂ) + t * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ in (Set.Ioc (-T) T)ᶜ, Wk x δ ((c : ℂ) + t * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I) := by
    rw [← hsplit] at hfull
    have hS' : ((S : ℝ) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ in Set.Ioc (-T) T, Wk x δ ((c : ℂ) + t * I) *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)) +
        ∫ t : ℝ in (Set.Ioc (-T) T)ᶜ, Wk x δ ((c : ℂ) + t * I) *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)) := by
      rw [hfull]
      push_cast
      field_simp
    rw [hS']
    ring
  rw [key, norm_mul, Complex.norm_of_nonneg (by positivity)]
  have hBint := (EM.int_inv T hT0).1.const_mul (8 * X ^ c * R)
  have hB : ‖∫ t : ℝ in (Set.Ioc (-T) T)ᶜ, Wk x δ ((c : ℂ) + t * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)‖ ≤
      8 * X ^ c * R * (Real.pi / T) := by
    calc _ ≤ ∫ t : ℝ in (Set.Ioc (-T) T)ᶜ, ‖Wk x δ ((c : ℂ) + t * I) *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in (Set.Ioc (-T) T)ᶜ, 8 * X ^ c * R * (T ^ 2 + t ^ 2)⁻¹ := by
          refine setIntegral_mono_on hGint.norm.integrableOn hBint.integrableOn
            measurableSet_Ioc.compl (fun t ht => ?_)
          have ht2 : T ^ 2 ≤ t ^ 2 := by
            simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
            rcases ht with h | h <;> nlinarith
          have hi : (c ^ 2 + t ^ 2)⁻¹ ≤ 2 * (T ^ 2 + t ^ 2)⁻¹ := by
            have := inv_anti₀ (by positivity : 0 < (T ^ 2 + t ^ 2) / 2)
              (by nlinarith : (T ^ 2 + t ^ 2) / 2 ≤ c ^ 2 + t ^ 2)
            rwa [inv_div, div_eq_mul_inv] at this
          have hA : 0 ≤ 4 * X ^ c * R := by positivity
          calc _ ≤ 4 * X ^ c * R * (c ^ 2 + t ^ 2)⁻¹ := hGb t
            _ ≤ 4 * X ^ c * R * (2 * (T ^ 2 + t ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hi hA
            _ = 8 * X ^ c * R * (T ^ 2 + t ^ 2)⁻¹ := by ring
      _ ≤ ∫ t : ℝ, 8 * X ^ c * R * (T ^ 2 + t ^ 2)⁻¹ :=
          setIntegral_le_integral hBint (Filter.Eventually.of_forall fun t => by positivity)
      _ = 8 * X ^ c * R * (Real.pi / T) := by
          rw [integral_const_mul, (EM.int_inv T hT0).2]
  have hR' : R ≤ (M / Real.log 2 + 1) * Real.log x := by
    have : M ≤ M / Real.log 2 * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hl2 hM0
    linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ in (Set.Ioc (-T) T)ᶜ, Wk x δ ((c : ℂ) + t * I) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((c : ℂ) + t * I)‖
      ≤ 1 / (2 * Real.pi) * (8 * X ^ c * R * (Real.pi / T)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = 4 * X ^ c * R / T := by
        field_simp
        ring
    _ ≤ 4 * (18 * x) * ((M / Real.log 2 + 1) * Real.log x) / T := by
        gcongr
    _ = 72 * (M / Real.log 2 + 1) * x * Real.log x / T := by ring


-- ===== from ER.lean =====


namespace ER

theorem bdry_mem {z : ℂ} {x0 x1 y0 y1 : ℝ} (hz : OnBdry z x0 x1 y0 y1) :
    z ∈ [[x0, x1]] ×ℂ [[y0, y1]] := by
  rw [mem_reProdIm]
  rcases hz with ⟨h1, h | h⟩ | ⟨h1, h | h⟩ <;> simp_all [left_mem_uIcc, right_mem_uIcc]

theorem RI_sum {ι : Type*} (F : Finset ι) (f : ι → ℂ → ℂ) {x0 x1 y0 y1 : ℝ}
    (h : ∀ i ∈ F, RIable (f i) x0 x1 y0 y1) :
    RI (fun z => ∑ i ∈ F, f i z) x0 x1 y0 y1 = ∑ i ∈ F, RI (f i) x0 x1 y0 y1 := by
  unfold RI
  rw [intervalIntegral.integral_finsetSum (fun i hi => (h i hi).1),
    intervalIntegral.integral_finsetSum (fun i hi => (h i hi).2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (h i hi).2.2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (h i hi).2.2.2),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]

theorem RIable_add' {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hf : RIable f x0 x1 y0 y1)
    (hg : RIable g x0 x1 y0 y1) : RIable (fun z => f z + g z) x0 x1 y0 y1 :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

theorem contAt_sum {ι : Type*} (F : Finset ι) (f : ι → ℂ → ℂ) {z : ℂ}
    (h : ∀ i ∈ F, ContinuousAt (f i) z) : ContinuousAt (fun w => ∑ i ∈ F, f i w) z :=
  tendsto_finsetSum F h

/-- Zeros in `zbox` lie strictly inside the rectangle. -/
theorem zbox_inside {σ1 c T' : ℝ} (hc : 1 < c)
    (hbd : ∀ z, OnBdry z σ1 c (-T') T' → Z z ≠ 0) {u : ℂ} (hu : u ∈ zbox σ1 T') :
    σ1 < u.re ∧ u.re < c ∧ -T' < u.im ∧ u.im < T' := by
  obtain ⟨hZ, hre, him⟩ := mem_zbox.1 hu
  have hlt := Z_re_lt_one hZ
  have hT : -T' ≤ u.im ∧ u.im ≤ T' := abs_le.1 him
  refine ⟨?_, by linarith, ?_, ?_⟩
  · rcases hre.lt_or_eq with h | h
    · exact h
    · exact absurd hZ (hbd u (Or.inr ⟨mem_uIcc.2 (Or.inl hT), Or.inl h.symm⟩))
  · rcases hT.1.lt_or_eq with h | h
    · exact h
    · exact absurd hZ (hbd u (Or.inl ⟨mem_uIcc.2 (Or.inl ⟨hre, by linarith⟩), Or.inl h.symm⟩))
  · rcases hT.2.lt_or_eq with h | h
    · exact h
    · exact absurd hZ (hbd u (Or.inl ⟨mem_uIcc.2 (Or.inl ⟨hre, by linarith⟩), Or.inr h⟩))

end ER

theorem rect_residue : ∀ (H : ℂ → ℂ) (V : Set ℂ), IsOpen V → ∀ σ1 c T' : ℝ, σ1 < 1 → 1 < c →
    0 < T' → [[σ1, c]] ×ℂ [[-T', T']] ⊆ V → DifferentiableOn ℂ H V →
    (∀ z, OnBdry z σ1 c (-T') T' → Z z ≠ 0) →
    RI (fun s => H s * Lf s) σ1 c (-T') T' =
      2 * Real.pi * I * (H 1 - ∑ ρ ∈ zbox σ1 T', (mult ρ : ℂ) * H ρ) := by
  intro H V hV σ1 c T' hσ1 hc hT hRV hH hbd
  set F := zbox σ1 T' with hF
  obtain ⟨g, hg, hgF, hfac⟩ := factor F Z Z_diff (fun u _ => Z_order_ne_top u)
  have hZ : (fun z => (∏ u ∈ F, (z - u) ^ mult u) * g z) = Z := funext fun s => (hfac s).symm
  -- g ≠ 0 on the closed rectangle
  have hgR : ∀ s ∈ [[σ1, c]] ×ℂ [[-T', T']], g s ≠ 0 := by
    intro s hs hgs
    rw [mem_reProdIm, uIcc_of_le (by linarith : σ1 ≤ c), uIcc_of_le (by linarith : -T' ≤ T')]
      at hs
    have hZs : Z s = 0 := by rw [hfac s, hgs, mul_zero]
    have hsF : s ∈ F := mem_zbox.2 ⟨hZs, hs.1.1, abs_le.2 hs.2⟩
    exact hgF s hsF hgs
  have hdg : Differentiable ℂ (deriv g) := fun z => ((hg.analyticAt z).deriv).differentiableAt
  have hHat : ∀ z ∈ [[σ1, c]] ×ℂ [[-T', T']], DifferentiableAt ℂ H z :=
    fun z hz => hH.differentiableAt (hV.mem_nhds (hRV hz))
  -- boundary facts
  have hneu : ∀ z, OnBdry z σ1 c (-T') T' → ∀ u ∈ F, z ≠ u := by
    intro z hz u hu hzu
    exact hbd z hz (hzu ▸ (mem_zbox.1 hu).1)
  have hne1 : ∀ z, OnBdry z σ1 c (-T') T' → z ≠ 1 := by
    intro z hz hz1
    subst hz1
    rcases hz with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> simp at h <;> linarith
  -- pointwise identity on the boundary
  set G : ℂ → ℂ := fun z => H z / (z - 1) -
    ((∑ u ∈ F, (mult u : ℂ) * (H z / (z - u))) + H z * (deriv g z / g z)) with hG
  have hpt : ∀ z, OnBdry z σ1 c (-T') T' → H z * Lf z = G z := by
    intro z hz
    have hl := logDeriv_factor hg F mult (hneu z hz) (hgR z (ER.bdry_mem hz))
    rw [hZ, logDeriv_apply] at hl
    have hs : ∑ u ∈ F, (mult u : ℂ) * (H z / (z - u)) = H z * ∑ u ∈ F, (mult u : ℂ) / (z - u) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    simp only [hG, Lf]
    rw [hs, neg_div, hl]
    ring
  -- integrability
  have hHc : ∀ z, OnBdry z σ1 c (-T') T' → ContinuousAt H z :=
    fun z hz => (hHat z (ER.bdry_mem hz)).continuousAt
  have hpole : ∀ u : ℂ, (∀ z, OnBdry z σ1 c (-T') T' → z ≠ u) →
      RIable (fun z => H z / (z - u)) σ1 c (-T') T' := fun u hu =>
    RIable_of_bdry fun z hz =>
      (hHc z hz).div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 (hu z hz))
  have hRu : ∀ u ∈ F, RIable (fun z => (mult u : ℂ) * (H z / (z - u))) σ1 c (-T') T' :=
    fun u hu => RIable_of_bdry fun z hz =>
      continuousAt_const.mul ((hHc z hz).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 (hneu z hz u hu)))
  have hRsum : RIable (fun z => ∑ u ∈ F, (mult u : ℂ) * (H z / (z - u))) σ1 c (-T') T' :=
    RIable_of_bdry fun z hz => ER.contAt_sum F _ fun u hu =>
      continuousAt_const.mul ((hHc z hz).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 (hneu z hz u hu)))
  have hRg : RIable (fun z => H z * (deriv g z / g z)) σ1 c (-T') T' :=
    RIable_of_bdry fun z hz => (hHc z hz).mul ((hdg z).continuousAt.div
      (hg z).continuousAt (hgR z (ER.bdry_mem hz)))
  -- holomorphic part integrates to zero
  have hzero : RI (fun z => H z * (deriv g z / g z)) σ1 c (-T') T' = 0 := by
    apply RI_eq_zero
    intro z hz
    exact ((hHat z hz).mul ((hdg z).div (hg z) (hgR z hz))).differentiableWithinAt
  -- residues
  have h1 : RI (fun z => H z / (z - 1)) σ1 c (-T') T' = 2 * Real.pi * I * H 1 :=
    RI_pole_gen (by simpa using hσ1) (by simpa using hc) (by simpa using hT)
      (by simpa using hT) hV hRV hH
  have hu : ∀ u ∈ F, RI (fun z => (mult u : ℂ) * (H z / (z - u))) σ1 c (-T') T' =
      (mult u : ℂ) * (2 * Real.pi * I * H u) := by
    intro u huF
    obtain ⟨a1, a2, a3, a4⟩ := ER.zbox_inside hc hbd huF
    rw [RI_const_mul, RI_pole_gen a1 a2 a3 a4 hV hRV hH]
  rw [RI_congr_bdry hpt, hG, RI_sub (hpole 1 hne1) (ER.RIable_add' hRsum hRg), RI_add hRsum hRg,
    ER.RI_sum F _ hRu, Finset.sum_congr rfl hu, h1, hzero, add_zero, mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun u _ => by ring



-- ===== from HD1.lean =====


namespace HD1

open ArithmeticFunction

/-- Real Dirichlet terms `Λ(n) n^{-σ}`. -/
def D (σ : ℝ) (n : ℕ) : ℝ := (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)

/-- `∑ Λ(n) n^{-σ}`. -/
def Ssum (σ : ℝ) : ℝ := ∑' n, D σ n

lemma D_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ D σ n :=
  mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma D_zero (σ : ℝ) : D σ 0 = 0 := by simp [D]

lemma norm_term_eq_D (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) s n‖ = D s.re n := by
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [D]
  · rw [if_neg hn.ne', D, Real.rpow_neg (Nat.cast_nonneg _), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, div_eq_mul_inv]

lemma term_eq_D (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => (vonMangoldt n : ℂ)) (σ : ℂ) n = ((D σ n : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [D]
  · rw [LSeries.term_of_ne_zero hn.ne']
    have : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← ofReal_natCast, ofReal_cpow (Nat.cast_nonneg _)]
    rw [this, D, Real.rpow_neg (Nat.cast_nonneg _)]
    push_cast
    rw [div_eq_mul_inv]

lemma D_summable {σ : ℝ} (hσ : 1 < σ) : Summable (D σ) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have h2 : Summable (fun n => ((D σ n : ℝ) : ℂ)) := h.congr (term_eq_D σ)
  exact Complex.summable_ofReal.mp h2

lemma LS_real {σ : ℝ} (_hσ : 1 < σ) :
    LSeries (fun n => (vonMangoldt n : ℂ)) (σ : ℂ) = ((Ssum σ : ℝ) : ℂ) := by
  rw [LSeries, Ssum, Complex.ofReal_tsum]
  simp_rw [term_eq_D]

lemma norm_LS_le {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n => (vonMangoldt n : ℂ)) s‖ ≤ Ssum s.re := by
  rw [LSeries, Ssum]
  have hsum : Summable (fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) s n‖) := by
    simp_rw [norm_term_eq_D]; exact D_summable hs
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  simp_rw [norm_term_eq_D]

lemma Ssum_nonneg (σ : ℝ) : 0 ≤ Ssum σ := tsum_nonneg (D_nonneg σ)

lemma Ssum_le_small {C : ℝ}
    (hland : ∀ t : ℝ, ∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → Z s ≠ 0 →
      ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤ C * Real.log (|t| + 3))
    {σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 11 / 10) :
    Ssum σ ≤ C * Real.log 3 + 1 / (σ - 1) := by
  have h := Lf_upper hland (t := 0) hσ hσ'
  have e : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = (σ : ℂ) := by simp
  rw [e] at h
  have hsum : 0 ≤ (∑ u ∈ zball (ctr 0), (mult u : ℂ) / ((σ : ℂ) - u)).re := by
    rw [re_sum]
    refine Finset.sum_nonneg fun u hu => re_div_nonneg (Nat.cast_nonneg _) ?_
    have := Z_re_lt_one (mem_zball.1 hu).1
    simp; linarith
  have hpole : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    have : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, one_div, ← ofReal_inv, ofReal_re, one_div]
  have hL : (Lf (σ : ℂ)).re = Ssum σ := by
    rw [Lf_eq_LSeries (by simpa using hσ), LS_real hσ, ofReal_re]
  simp only [abs_zero, zero_add] at h
  linarith

lemma Ssum_mono {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) : Ssum τ ≤ Ssum σ := by
  refine Summable.tsum_le_tsum (fun n => ?_) (D_summable (by linarith)) (D_summable hσ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [D_zero]
  · unfold D
    apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

lemma Ssum_bound : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ σ : ℝ, 1 < σ → Ssum σ ≤ C' + 1 / (σ - 1) := by
  obtain ⟨C, hC, hland⟩ := landau
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl := fun t s hs hz => (hland t).2 s hs hz
  refine ⟨C * Real.log 3 + 10, by positivity, fun σ hσ => ?_⟩
  by_cases h : σ ≤ 11 / 10
  · have := Ssum_le_small hl hσ h
    linarith
  · push Not at h
    have h1 := Ssum_mono (by norm_num : (1 : ℝ) < 11 / 10) h.le
    have h2 := Ssum_le_small hl (by norm_num : (1 : ℝ) < 11 / 10) le_rfl
    have h3 : 0 ≤ 1 / (σ - 1) := by
      have : 0 < σ - 1 := by linarith
      positivity
    norm_num at h2
    linarith

lemma re_m_div (m : ℝ) (z : ℂ) : ((m : ℂ) / z).re = m * z.re / ‖z‖ ^ 2 := by
  rw [Complex.div_re, Complex.sq_norm]
  simp

end HD1

theorem local_sum : ∃ C2 : ℝ, 0 < C2 ∧ ∀ γ η : ℝ, 0 < η → η ≤ 1 / 10 →
    ∑ u ∈ zball (ctr γ), (mult u : ℝ) / ‖((1 + η : ℝ) : ℂ) + γ * I - u‖ ^ 2 ≤
      C2 * (Real.log (|γ| + 3) + 1 / η) / η := by
  obtain ⟨C, hC, hland⟩ := landau
  have hl := fun t s hs hz => (hland t).2 s hs hz
  refine ⟨2 * C + 2, by positivity, fun γ η hη hη' => ?_⟩
  have hσ : 1 < 1 + η := by linarith
  have hσ' : 1 + η ≤ 11 / 10 := by linarith
  set s0 : ℂ := ((1 + η : ℝ) : ℂ) + γ * I with hs0
  have h := Lf_upper hl (t := γ) hσ hσ'
  have hs0re : s0.re = 1 + η := by simp [hs0]
  -- the Lf term
  have hLf : -(Lf s0).re ≤ C * Real.log 3 + 1 / η := by
    rw [Lf_eq_LSeries (by rw [hs0re]; exact hσ)]
    have h1 := HD1.norm_LS_le (s := s0) (by rw [hs0re]; exact hσ)
    have h2 := HD1.Ssum_le_small hl (σ := s0.re) (by rw [hs0re]; exact hσ) (by rw [hs0re]; exact hσ')
    rw [hs0re, add_sub_cancel_left] at h2
    rw [hs0re] at h1
    have h3 := neg_le_abs (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s0).re
    have h4 := Complex.abs_re_le_norm (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s0)
    linarith
  -- the pole term
  have hpole : (1 / (s0 - 1)).re ≤ 1 / η := by
    have hz : (s0 - 1).re = η := by simp [hs0]
    have := HD1.re_m_div 1 (s0 - 1)
    push_cast at this
    rw [this, hz, one_mul]
    have hn : η ≤ ‖s0 - 1‖ := by
      have := Complex.abs_re_le_norm (s0 - 1)
      rw [hz, abs_of_pos hη] at this; exact this
    rw [div_le_div_iff₀ (by nlinarith) hη]
    nlinarith
  -- the zero sum
  have hsum : η * ∑ u ∈ zball (ctr γ), (mult u : ℝ) / ‖s0 - u‖ ^ 2 ≤
      (∑ u ∈ zball (ctr γ), (mult u : ℂ) / (s0 - u)).re := by
    rw [re_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    have hu1 := Z_re_lt_one (mem_zball.1 hu).1
    have hre : (s0 - u).re = 1 + η - u.re := by simp [hs0]
    have := HD1.re_m_div (mult u : ℝ) (s0 - u)
    push_cast at this
    rw [this, hre]
    have hpos : 0 < ‖s0 - u‖ := by
      apply norm_pos_iff.2; intro h0
      have := congrArg Complex.re h0; rw [hre] at this; simp at this; linarith
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    have hm : (0 : ℝ) ≤ mult u := Nat.cast_nonneg _
    nlinarith
  have hlog : Real.log 3 ≤ Real.log (|γ| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ])
  have hl3 : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hfin : η * ∑ u ∈ zball (ctr γ), (mult u : ℝ) / ‖s0 - u‖ ^ 2 ≤
      (2 * C + 2) * (Real.log (|γ| + 3) + 1 / η) := by
    have : C * Real.log 3 ≤ C * Real.log (|γ| + 3) := mul_le_mul_of_nonneg_left hlog hC.le
    have hi : 0 ≤ 1 / η := by positivity
    have hlg : 0 ≤ Real.log (|γ| + 3) := hl3.trans hlog
    nlinarith
  rw [le_div_iff₀ hη]
  linarith

namespace HD1

open ArithmeticFunction

lemma logMul_iter (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show Complex.log n * (LSeries.logMul^[k] f) n = _
    rw [ih]; ring

lemma iD_inv (u s : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => (z - u)⁻¹) s = (-1) ^ k * k.factorial * ((s - u) ^ (k + 1))⁻¹ := by
  rw [iteratedDeriv_eq_iterate]
  have := iter_deriv_inv_linear_sub k (1 : ℂ) u
  simp only [one_mul, one_pow, mul_one] at this
  rw [this]
  dsimp only
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

lemma s0_sub_ctr (γ η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 20) :
    ‖((1 + η : ℝ) : ℂ) + γ * I - ctr γ‖ = 1 / 5 - η := by
  have : ((1 + η : ℝ) : ℂ) + γ * I - ctr γ = ((η - 1 / 5 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ctr] <;> ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  ring

lemma abscissa_lt (s : ℂ) (hs : 1 < s.re) :
    LSeries.abscissaOfAbsConv (fun n => (vonMangoldt n : ℂ)) < s.re := by
  have h : LSeries.abscissaOfAbsConv (fun n => (vonMangoldt n : ℂ)) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)
  exact h.trans_lt (by exact_mod_cast hs)

/-- The detector identity (k-th derivative of Landau's expansion). -/
lemma ident {γ η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 20) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball (ctr γ) (11 / 20)))
    (hrep : ∀ s ∈ ball (ctr γ) (11 / 20), Z s ≠ 0 →
      deriv Z s / Z s = ∑ u ∈ zball (ctr γ), (mult u : ℂ) / (s - u) + G s)
    (k : ℕ) {s0 : ℂ} (hs0 : s0 = ((1 + η : ℝ) : ℂ) + γ * I) :
    (-1) ^ k * LSeries (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0 =
      (-1) ^ k * k.factorial * ((s0 - 1) ^ (k + 1))⁻¹ -
        ∑ u ∈ zball (ctr γ), (mult u : ℂ) * ((-1) ^ k * k.factorial * ((s0 - u) ^ (k + 1))⁻¹) -
        iteratedDeriv k G s0 := by
  have hs0re : s0.re = 1 + η := by simp [hs0]
  have hs0b : s0 ∈ ball (ctr γ) (11 / 20) := by
    rw [mem_ball, dist_eq_norm, hs0, s0_sub_ctr γ η hη hη']; linarith
  have hU : IsOpen (ball (ctr γ) (11 / 20) ∩ {s : ℂ | 1 < s.re}) :=
    isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hev : LSeries (fun n => (vonMangoldt n : ℂ)) =ᶠ[𝓝 s0]
      (fun s => (s - 1)⁻¹ - ∑ u ∈ zball (ctr γ), (mult u : ℂ) * (s - u)⁻¹ - G s) := by
    filter_upwards [hU.mem_nhds ⟨hs0b, by simp only [Set.mem_ofPred_eq, hs0re]; linarith⟩] with s hs
    have hs2 : 1 < s.re := hs.2
    have hZ : Z s ≠ 0 := fun h => by have := Z_re_lt_one h; linarith
    rw [← Lf_eq_LSeries hs2, Lf, neg_div, hrep s hs.1 hZ]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have hne : ∀ u : ℂ, u.re < 1 → s0 - u ≠ 0 := fun u hu h => by
    have := congrArg Complex.re h; simp at this; linarith
  have c1 : ContDiffAt ℂ k (fun s : ℂ => (s - 1)⁻¹) s0 :=
    (contDiffAt_id.sub contDiffAt_const).inv (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)
  have c2 : ∀ u ∈ zball (ctr γ), ContDiffAt ℂ k (fun s : ℂ => (mult u : ℂ) * (s - u)⁻¹) s0 :=
    fun u hu => contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv
      (by simpa using hne u (Z_re_lt_one (mem_zball.1 hu).1)))
  have c3 : ContDiffAt ℂ k G s0 := (hG.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hs0b)
  have c12 : ContDiffAt ℂ k (fun s : ℂ => ∑ u ∈ zball (ctr γ), (mult u : ℂ) * (s - u)⁻¹) s0 :=
    ContDiffAt.sum c2
  have h1 := hev.iteratedDeriv_eq k
  rw [LSeries_iteratedDeriv k (abscissa_lt s0 (by rw [hs0re]; linarith))] at h1
  rw [h1, iteratedDeriv_fun_sub (c1.sub c12) c3, iteratedDeriv_fun_sub c1 c12,
    iteratedDeriv_fun_sum c2]
  simp only [iteratedDeriv_const_mul_field, iD_inv]

lemma cauchyG {γ η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 20) {G : ℂ → ℂ} {M : ℝ}
    (hG : DifferentiableOn ℂ G (ball (ctr γ) (11 / 20)))
    (hGb : ∀ s : ℂ, ‖s - ctr γ‖ ≤ 1 / 2 → ‖G s‖ ≤ M)
    (k : ℕ) {s0 : ℂ} (hs0 : s0 = ((1 + η : ℝ) : ℂ) + γ * I) :
    ‖iteratedDeriv k G s0‖ ≤ k.factorial * M / (3 / 10) ^ k := by
  have hd : ‖s0 - ctr γ‖ = 1 / 5 - η := by rw [hs0, s0_sub_ctr γ η hη hη']
  have key : ∀ z, ‖z - s0‖ ≤ 3 / 10 → ‖z - ctr γ‖ ≤ 1 / 2 := by
    intro z hz
    have := norm_add_le (z - s0) (s0 - ctr γ)
    rw [sub_add_sub_cancel] at this
    linarith
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num)
    (hG.diffContOnCl_ball ?_) (fun z hz => hGb z (key z (le_of_eq ?_)))
  · intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    linarith [key z hz]
  · rw [mem_sphere, dist_eq_norm] at hz; exact hz

end HD1

namespace HD1

open ArithmeticFunction

/-- Real version of `wt`. -/
def wtr (η : ℝ) (k n : ℕ) : ℝ :=
  (vonMangoldt n : ℝ) / n * (η * Real.log n) ^ k * Real.exp (-(η * Real.log n)) /
    (k.factorial : ℝ)

lemma wt_eq (η : ℝ) (k n : ℕ) : wt η k n = ((wtr η k n : ℝ) : ℂ) := rfl

lemma wtr_nonneg {η : ℝ} (hη : 0 ≤ η) (k n : ℕ) : 0 ≤ wtr η k n := by
  unfold wtr
  have hl := Real.log_natCast_nonneg n
  exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
    (pow_nonneg (mul_nonneg hη hl) _)) (Real.exp_pos _).le) (Nat.cast_nonneg _)

lemma wtr_zero (η : ℝ) (k : ℕ) : wtr η k 0 = 0 := by simp [wtr]

lemma norm_wt_phase {η : ℝ} (hη : 0 ≤ η) (γ : ℝ) (k n : ℕ) :
    ‖wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))‖ = wtr η k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wt_eq, wtr_zero]
  · rw [norm_mul, norm_natCast_cpow_of_pos hn, wt_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (wtr_nonneg hη k n)]
    simp

lemma term_wt {η : ℝ} (_hη : 0 < η) (γ : ℝ) (k n : ℕ) {s0 : ℂ}
    (hs0 : s0 = ((1 + η : ℝ) : ℂ) + γ * I) :
    ((η ^ (k + 1) / k.factorial : ℝ) : ℂ) *
        LSeries.term (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0 n =
      (η : ℂ) * (wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wt_eq, wtr_zero]
  have hn' : n ≠ 0 := hn.ne'
  rw [LSeries.term_of_ne_zero hn', logMul_iter, wt_eq, wtr]
  have hlog : Complex.log n = ((Real.log n : ℝ) : ℂ) := Complex.natCast_log.symm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℂ) ^ (((1 + η : ℝ)) : ℂ) = (((n : ℝ) * Real.exp (η * Real.log n) : ℝ) : ℂ) := by
    have : ((n : ℝ) ^ (1 + η) : ℝ) = (n : ℝ) * Real.exp (η * Real.log n) := by
      rw [Real.rpow_add hnR, Real.rpow_one, Real.rpow_def_of_pos hnR, mul_comm (Real.log _)]
    rw [← this, ofReal_cpow hnR.le]
    simp
  have hcp : (n : ℂ) ^ s0 = (((n : ℝ) * Real.exp (η * Real.log n) : ℝ) : ℂ) *
      (n : ℂ) ^ ((γ : ℂ) * I) := by
    rw [hs0, cpow_add _ _ (Nat.cast_ne_zero.2 hn'), h1]
  have hneg : (n : ℂ) ^ (-((γ : ℂ) * I)) = ((n : ℂ) ^ ((γ : ℂ) * I))⁻¹ := cpow_neg _ _
  have hne : (n : ℂ) ^ ((γ : ℂ) * I) ≠ 0 := by
    intro h
    have := norm_natCast_cpow_of_pos hn ((γ : ℂ) * I)
    rw [h] at this; simp at this
  have hex : Real.exp (η * Real.log n) ≠ 0 := (Real.exp_pos _).ne'
  rw [hlog, hcp, hneg, Real.exp_neg]
  push_cast
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn'
  have hexC : Complex.exp ((η : ℂ) * (Real.log n : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

lemma LS_wt {η : ℝ} (hη : 0 < η) (γ : ℝ) (k : ℕ) {s0 : ℂ}
    (hs0 : s0 = ((1 + η : ℝ) : ℂ) + γ * I) :
    Summable (fun n : ℕ => wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))) ∧
    ((η ^ (k + 1) / k.factorial : ℝ) : ℂ) *
        LSeries (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0 =
      (η : ℂ) * ∑' n : ℕ, wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I)) := by
  have hs0re : s0.re = 1 + η := by simp [hs0]
  have hsum : LSeriesSummable (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      rw [LSeries.absicssaOfAbsConv_logPowMul]; exact abscissa_lt s0 (by rw [hs0re]; linarith))
  set c : ℂ := ((η ^ (k + 1) / k.factorial : ℝ) : ℂ)
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have h2 : ∀ n : ℕ, wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I)) =
      (η : ℂ)⁻¹ * (c * LSeries.term (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0 n) := by
    intro n
    rw [term_wt hη γ k n hs0, ← mul_assoc, inv_mul_cancel₀ hηC, one_mul]
  refine ⟨((hsum.mul_left c).mul_left (η : ℂ)⁻¹).congr (fun n => (h2 n).symm), ?_⟩
  rw [LSeries, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [term_wt hη γ k n hs0]

/-- Splitting a convergent series into head, middle block and tail. -/
lemma split_bound (f : ℕ → ℂ) (hf : Summable f) {N0 N1 : ℕ} (h01 : N0 ≤ N1) :
    ‖∑' n, f n‖ ≤ ∑ n ∈ Finset.range (N0 + 1), ‖f n‖ + ‖∑ n ∈ Finset.Ioc N0 N1, f n‖ +
      ‖∑' m : ℕ, f (m + (N1 + 1))‖ := by
  rw [← hf.sum_add_tsum_nat_add (N1 + 1)]
  have hU : Finset.range (N1 + 1) = Finset.range (N0 + 1) ∪ Finset.Ioc N0 N1 := by
    ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]; omega
  have hD : Disjoint (Finset.range (N0 + 1)) (Finset.Ioc N0 N1) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_range, Finset.mem_Ioc] at h1 h2; omega
  rw [hU, Finset.sum_union hD]
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact norm_sum_le _ _

/-- `y^k e^{-y/2}` is decreasing for `y ≥ 2k`. -/
lemma mono_aux (k : ℕ) {Y y : ℝ} (h0 : 2 * k ≤ Y) (hY : Y ≤ y) :
    y ^ k * Real.exp (-(y / 2)) ≤ Y ^ k * Real.exp (-(Y / 2)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul]
    exact Real.exp_le_exp.2 (by linarith)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hYp : 0 < Y := by linarith
  have h1 : y / Y ≤ Real.exp (y / Y - 1) := by
    have := Real.add_one_le_exp (y / Y - 1); linarith
  have h2 : (y / Y) ^ k ≤ Real.exp ((y - Y) / 2) := by
    calc (y / Y) ^ k ≤ Real.exp (y / Y - 1) ^ k :=
          pow_le_pow_left₀ (div_nonneg (by linarith) hYp.le) h1 k
      _ = Real.exp (k * (y / Y - 1)) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((y - Y) / 2) := by
          apply Real.exp_le_exp.2
          have : y / Y - 1 = (y - Y) / Y := by field_simp
          rw [this, mul_div_assoc']
          rw [div_le_div_iff₀ hYp (by norm_num)]
          nlinarith
  have h3 : y ^ k = Y ^ k * (y / Y) ^ k := by
    rw [div_pow, mul_div_assoc', mul_div_cancel_left₀ _ (pow_pos hYp k).ne']
  rw [h3]
  calc Y ^ k * (y / Y) ^ k * Real.exp (-(y / 2)) ≤
        Y ^ k * Real.exp ((y - Y) / 2) * Real.exp (-(y / 2)) := by
        gcongr
    _ = Y ^ k * Real.exp (-(Y / 2)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Pointwise head bound. -/
lemma wtr_head {η A : ℝ} (hη : 0 < η) (hA : 0 < A) (k n : ℕ) (hn : η * Real.log n ≤ A) :
    wtr η k n ≤ Real.exp 1 * A ^ k / k.factorial * D (1 + η / A) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [wtr_zero, D_zero]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hl := Real.log_natCast_nonneg n
  have hΛ := (vonMangoldt_nonneg : (0 : ℝ) ≤ vonMangoldt n)
  have hpow : (η * Real.log n) ^ k ≤ A ^ k := pow_le_pow_left₀ (by positivity) hn k
  have hex : Real.exp (-(η * Real.log n)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := mul_nonneg hη.le hl; linarith)
  have hinv : 1 / (n : ℝ) ≤ Real.exp 1 * (n : ℝ) ^ (-(1 + η / A)) := by
    rw [Real.rpow_neg hnR.le, Real.rpow_add hnR, Real.rpow_one, Real.rpow_def_of_pos hnR]
    rw [div_le_iff₀ hnR]
    have : Real.exp (Real.log n * (η / A)) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.2
      rw [mul_div_assoc', div_le_one hA]; linarith [mul_comm η (Real.log n)]
    have hp : 0 < (n : ℝ) * Real.exp (Real.log n * (η / A)) := by positivity
    rw [mul_inv, ← mul_assoc, mul_assoc (Real.exp 1)]
    rw [show (Real.exp 1 * (((n : ℝ))⁻¹ * (Real.exp (Real.log n * (η / A)))⁻¹) * n) =
      Real.exp 1 / Real.exp (Real.log n * (η / A)) by field_simp]
    rw [le_div_iff₀ (Real.exp_pos _)]; linarith
  unfold wtr D
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hfact]
  calc (vonMangoldt n : ℝ) / n * (η * Real.log n) ^ k * Real.exp (-(η * Real.log n))
      ≤ (vonMangoldt n : ℝ) * (1 / n) * A ^ k * 1 := by
        rw [div_eq_mul_one_div]
        gcongr
    _ ≤ (vonMangoldt n : ℝ) * (Real.exp 1 * (n : ℝ) ^ (-(1 + η / A))) * A ^ k * 1 := by
        gcongr
    _ = Real.exp 1 * A ^ k / k.factorial *
          ((vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + η / A))) * k.factorial := by
        field_simp

/-- Pointwise tail bound. -/
lemma wtr_tail {η Y : ℝ} (_hη : 0 < η) (k n : ℕ) (hY : 2 * k ≤ Y) (hn : Y ≤ η * Real.log n) :
    wtr η k n ≤ Y ^ k * Real.exp (-(Y / 2)) / k.factorial * D (1 + η / 2) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [wtr_zero, D_zero]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hl := Real.log_natCast_nonneg n
  have hΛ := (vonMangoldt_nonneg : (0 : ℝ) ≤ vonMangoldt n)
  set y := η * Real.log n with hy
  have hm := mono_aux k hY hn
  have hsplit : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hD : (n : ℝ) ^ (-(1 + η / 2)) = 1 / n * Real.exp (-(y / 2)) := by
    rw [Real.rpow_neg hnR.le, Real.rpow_add hnR, Real.rpow_one, Real.rpow_def_of_pos hnR,
      Real.exp_neg, hy]
    rw [show Real.log n * (η / 2) = η * Real.log n / 2 by ring]
    field_simp
  unfold wtr D
  rw [hD, hsplit]
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hfact]
  have e1 : (vonMangoldt n : ℝ) / n * y ^ k * (Real.exp (-(y / 2)) * Real.exp (-(y / 2))) =
      ((vonMangoldt n : ℝ) / n * Real.exp (-(y / 2))) * (y ^ k * Real.exp (-(y / 2))) := by ring
  have e2 : Y ^ k * Real.exp (-(Y / 2)) / k.factorial *
      ((vonMangoldt n : ℝ) * (1 / n * Real.exp (-(y / 2)))) * k.factorial =
      ((vonMangoldt n : ℝ) / n * Real.exp (-(y / 2))) * (Y ^ k * Real.exp (-(Y / 2))) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

end HD1

namespace HD1

open ArithmeticFunction

lemma geomV {A q x : ℝ} (hA : 0 ≤ A) (hq : 0 < q) (hx : 0 ≤ x) (hxq : x ≤ q / (2 * (A + 1)))
    {N : ℕ} (hN : 1 ≤ N) : A * N * x ^ N ≤ q ^ N := by
  have h1 : x ^ N ≤ (q / (2 * (A + 1))) ^ N := pow_le_pow_left₀ hx hxq N
  have h2 : (q / (2 * (A + 1))) ^ N = q ^ N * ((1 / 2) ^ N * (1 / (A + 1)) ^ N) := by
    rw [← mul_pow, ← mul_pow]; congr 1; field_simp
  have h3 : (1 / (A + 1)) ^ N ≤ 1 / (A + 1) :=
    pow_le_of_le_one (by positivity) (by rw [div_le_one (by linarith)]; linarith) (by omega)
  have h4 : (N : ℝ) * (1 / 2) ^ N ≤ 1 := by
    have : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
    rw [one_div_pow, mul_one_div, div_le_one (by positivity)]; exact this.le
  have h5 : A * (1 / (A + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]; linarith
  calc A * N * x ^ N ≤ A * N * (q ^ N * ((1 / 2) ^ N * (1 / (A + 1)) ^ N)) := by
        rw [← h2]; gcongr
    _ ≤ A * N * (q ^ N * ((1 / 2) ^ N * (1 / (A + 1)))) := by gcongr
    _ = q ^ N * (((N : ℝ) * (1 / 2) ^ N) * (A * (1 / (A + 1)))) := by ring
    _ ≤ q ^ N * (1 * 1) := by
        gcongr
    _ = q ^ N := by ring

lemma far_le {x A : ℝ} (hA : 0 < A) (hx : A < x) (ν : ℕ) (hν : 2 ≤ ν) :
    1 / x ^ ν ≤ 1 / A ^ (ν - 2) * (1 / x ^ 2) := by
  have hx0 : 0 < x := hA.trans hx
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (by positivity)
  calc A ^ (ν - 2) * x ^ 2 ≤ x ^ (ν - 2) * x ^ 2 := by gcongr
    _ = x ^ ν := by rw [← pow_add, Nat.sub_add_cancel hν]

lemma turan_near {c : ℝ}
    (hT : ∀ (S : Finset ℂ) (b : ℂ → ℝ) (N : ℕ), S.card ≤ N →
      (∀ z ∈ S, ‖z‖ ≤ 1) → (∀ z ∈ S, 1 ≤ b z) → (∃ z ∈ S, ‖z‖ = 1) →
      ∃ ν : ℕ, N + 1 ≤ ν ∧ ν ≤ 2 * N ∧ c ^ N ≤ ‖∑ z ∈ S, (b z : ℂ) * z ^ ν‖)
    (F : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ u ∈ F, 1 ≤ m u) (s0 u1 : ℂ) (hu1 : u1 ∈ F)
    (hmin : ∀ u ∈ F, ‖s0 - u1‖ ≤ ‖s0 - u‖) (hpos : 0 < ‖s0 - u1‖) (N : ℕ)
    (hN : ∑ u ∈ F, m u ≤ N) :
    ∃ ν : ℕ, N + 1 ≤ ν ∧ ν ≤ 2 * N ∧
      c ^ N ≤ ‖s0 - u1‖ ^ ν * ‖∑ u ∈ F, (m u : ℂ) * ((s0 - u) ^ ν)⁻¹‖ := by
  classical
  set zf : ℂ → ℂ := fun u => (s0 - u1) / (s0 - u) with hzf
  set P := F.image zf
  set b : ℂ → ℝ := fun z => ∑ u ∈ F with zf u = z, m u with hb
  have hcard : P.card ≤ N := by
    have h1 : P.card ≤ F.card := Finset.card_image_le
    have h2 : (F.card : ℝ) ≤ ∑ u ∈ F, m u := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]; push_cast
      exact Finset.sum_le_sum hm
    have : (F.card : ℝ) ≤ N := h2.trans hN
    have : F.card ≤ N := by exact_mod_cast this
    omega
  have hnorm : ∀ u ∈ F, ‖zf u‖ ≤ 1 := by
    intro u hu
    simp only [hzf]
    rw [norm_div, div_le_one (hpos.trans_le (hmin u hu))]
    exact hmin u hu
  have hne : s0 - u1 ≠ 0 := norm_pos_iff.1 hpos
  obtain ⟨ν, h1, h2, h3⟩ := hT P b N hcard
    (by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
      exact hnorm u hu)
    (by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
      have := Finset.single_le_sum (f := m)
        (fun x hx => le_trans zero_le_one (hm x (Finset.mem_filter.1 hx).1))
        (Finset.mem_filter.2 ⟨hu, rfl⟩ : u ∈ F.filter (fun x => zf x = zf u))
      exact (hm u hu).trans this)
    ⟨zf u1, Finset.mem_image_of_mem _ hu1, by simp [hzf, div_self hne]⟩
  refine ⟨ν, h1, h2, ?_⟩
  have hsum : ∑ z ∈ P, (b z : ℂ) * z ^ ν = ∑ u ∈ F, (m u : ℂ) * (zf u) ^ ν := by
    apply Finset.sum_image'
    intro u hu
    simp only [hb]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  have hsum2 : ∑ u ∈ F, (m u : ℂ) * (zf u) ^ ν =
      (s0 - u1) ^ ν * ∑ u ∈ F, (m u : ℂ) * ((s0 - u) ^ ν)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [hzf]
    rw [div_pow, div_eq_mul_inv]
    ring
  rw [hsum, hsum2, norm_mul, norm_pow] at h3
  exact h3

lemma head_sum {η A : ℝ} (hη : 0 < η) (hA : 0 < A) (k N0 : ℕ)
    (hN0 : (N0 : ℝ) ≤ Real.exp (A / η)) :
    ∑ n ∈ Finset.range (N0 + 1), wtr η k n ≤
      Real.exp 1 * A ^ k / k.factorial * Ssum (1 + η / A) := by
  have hσ : 1 < 1 + η / A := lt_add_of_pos_right 1 (by positivity)
  have hpt : ∀ n ∈ Finset.range (N0 + 1), wtr η k n ≤
      Real.exp 1 * A ^ k / k.factorial * D (1 + η / A) n := by
    intro n hn
    apply wtr_head hη hA
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp; exact hA.le
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnN : (n : ℝ) ≤ N0 := by
      have := Finset.mem_range.1 hn; exact_mod_cast (by omega : n ≤ N0)
    have : Real.log n ≤ A / η := by
      rw [Real.log_le_iff_le_exp hnR]; linarith
    rw [le_div_iff₀ hη] at this; linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  exact Summable.sum_le_tsum _ (fun n _ => D_nonneg _ n) (D_summable hσ)

lemma tail_sum {η Y : ℝ} (hη : 0 < η) (k N1 : ℕ) (hY : 2 * k ≤ Y)
    (hN1 : Real.exp (Y / η) < N1 + 1) :
    Summable (fun m : ℕ => wtr η k (m + (N1 + 1))) ∧
      ∑' m : ℕ, wtr η k (m + (N1 + 1)) ≤
        Y ^ k * Real.exp (-(Y / 2)) / k.factorial * Ssum (1 + η / 2) := by
  have hσ : 1 < 1 + η / 2 := by linarith
  set K := Y ^ k * Real.exp (-(Y / 2)) / k.factorial
  have hK : 0 ≤ K := by
    have : 0 ≤ Y := le_trans (by positivity) hY
    positivity
  have hpt : ∀ m : ℕ, wtr η k (m + (N1 + 1)) ≤ K * D (1 + η / 2) (m + (N1 + 1)) := by
    intro m
    apply wtr_tail hη k _ hY
    have hnR : (0 : ℝ) < (m + (N1 + 1) : ℕ) := by positivity
    have hlt : Real.exp (Y / η) < ((m + (N1 + 1) : ℕ) : ℝ) := by push_cast; linarith
    have : Y / η < Real.log ((m + (N1 + 1) : ℕ) : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hnR]; exact hlt
    rw [div_lt_iff₀ hη] at this; linarith
  have hDs : Summable (fun m : ℕ => D (1 + η / 2) (m + (N1 + 1))) :=
    (summable_nat_add_iff (N1 + 1)).2 (D_summable hσ)
  have hs : Summable (fun m : ℕ => wtr η k (m + (N1 + 1))) :=
    Summable.of_nonneg_of_le (fun m => wtr_nonneg hη.le k _) hpt (hDs.mul_left K)
  refine ⟨hs, ?_⟩
  calc ∑' m : ℕ, wtr η k (m + (N1 + 1)) ≤ ∑' m : ℕ, K * D (1 + η / 2) (m + (N1 + 1)) :=
        Summable.tsum_le_tsum hpt hs (hDs.mul_left K)
    _ = K * ∑' m : ℕ, D (1 + η / 2) (m + (N1 + 1)) := tsum_mul_left
    _ ≤ K * Ssum (1 + η / 2) := by
        gcongr
        exact tsum_comp_le_tsum_of_inj (f := D (1 + η / 2)) (D_summable hσ) (D_nonneg _)
          (i := fun m => m + (N1 + 1)) (fun x y h => by simpa using h)

lemma kpow_fact (k : ℕ) : (k : ℝ) ^ k / k.factorial ≤ Real.exp 1 ^ k := by
  have := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  rw [← Real.exp_nat_mul, mul_one]; exact this

end HD1

namespace HD1

open ArithmeticFunction

lemma exp_pow_split (b : ℝ) (k : ℕ) :
    b ^ k * Real.exp 1 ^ k * Real.exp (-(b * k / 2)) = (b * Real.exp (1 - b / 2)) ^ k := by
  rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- Truncation of the Dirichlet series to the block `(N0, N1]`. -/
lemma trunc {η a b C' q : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (ha : 0 < a) (hae : a * Real.exp 1 ≤ 1)
    (hb : 2 ≤ b) (hbe : b * Real.exp (1 - b / 2) ≤ 1)
    (hC' : 0 ≤ C') (hS : ∀ σ : ℝ, 1 < σ → Ssum σ ≤ C' + 1 / (σ - 1))
    (hHa : ∀ N : ℕ, 1 ≤ N → 8 * (Real.exp 1 * (C' + 2)) * N * (a * Real.exp 1) ^ N ≤ q ^ N)
    (hHb : ∀ N : ℕ, 1 ≤ N → 8 * (C' + 2) * N * (b * Real.exp (1 - b / 2)) ^ N ≤ q ^ N)
    (γ : ℝ) (k N : ℕ) (hN : 1 ≤ N) (hNk : N ≤ k) (hk2 : k ≤ 2 * N)
    (hf : Summable (fun n : ℕ => wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))))
    (hmain : (5 / 8) * q ^ N ≤ η * ‖∑' n : ℕ, wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))‖) :
    (3 / 8) * q ^ N ≤ η * ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k / η)⌋₊ ⌊Real.exp (b * k / η)⌋₊,
      wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))‖ := by
  have hkpos : 0 < k := lt_of_lt_of_le hN hNk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNkR : (N : ℝ) ≤ k := by exact_mod_cast hNk
  have hk2R : (k : ℝ) ≤ 2 * N := by exact_mod_cast hk2
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num); linarith
  have ha1 : a ≤ 1 := by nlinarith
  have hab : a < b := by linarith
  set f : ℕ → ℂ := fun n => wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I)) with hfdef
  have h01 : ⌊Real.exp (a * k / η)⌋₊ ≤ ⌊Real.exp (b * k / η)⌋₊ := by
    apply Nat.floor_le_floor
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hη.le
    exact mul_le_mul_of_nonneg_right hab.le (by positivity)
  have hsplit := split_bound f hf h01
  -- head
  have hakp : 0 < a * k := by positivity
  have hhead0 : ∑ n ∈ Finset.range (⌊Real.exp (a * k / η)⌋₊ + 1), ‖f n‖ ≤
      Real.exp 1 * (a * k) ^ k / k.factorial * Ssum (1 + η / (a * k)) := by
    simp only [hfdef, norm_wt_phase hη.le]
    exact head_sum hη hakp k _ (Nat.floor_le (Real.exp_pos _).le)
  have hSh : η * Ssum (1 + η / (a * k)) ≤ C' + a * k := by
    have := hS (1 + η / (a * k)) (lt_add_of_pos_right 1 (by positivity))
    rw [add_sub_cancel_left, one_div_div] at this
    calc η * Ssum (1 + η / (a * k)) ≤ η * (C' + a * k / η) := by gcongr
      _ = η * C' + a * k := by field_simp
      _ ≤ C' + a * k := by nlinarith
  have hP := kpow_fact k
  have hP0 : 0 ≤ (k : ℝ) ^ k / k.factorial := by positivity
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hhead : η * ∑ n ∈ Finset.range (⌊Real.exp (a * k / η)⌋₊ + 1), ‖f n‖ ≤
      Real.exp 1 * (a * Real.exp 1) ^ N * ((C' + 2) * N) := by
    have hS0 : 0 ≤ Ssum (1 + η / (a * k)) := Ssum_nonneg _
    calc η * ∑ n ∈ Finset.range (⌊Real.exp (a * k / η)⌋₊ + 1), ‖f n‖
        ≤ η * (Real.exp 1 * (a * k) ^ k / k.factorial * Ssum (1 + η / (a * k))) := by gcongr
      _ = Real.exp 1 * (a ^ k * ((k : ℝ) ^ k / k.factorial)) * (η * Ssum (1 + η / (a * k))) := by
          rw [mul_pow]; ring
      _ ≤ Real.exp 1 * (a ^ k * Real.exp 1 ^ k) * (C' + a * k) := by gcongr
      _ = Real.exp 1 * (a * Real.exp 1) ^ k * (C' + a * k) := by rw [mul_pow]
      _ ≤ Real.exp 1 * (a * Real.exp 1) ^ N * ((C' + 2) * N) := by
          have h1 : (a * Real.exp 1) ^ k ≤ (a * Real.exp 1) ^ N :=
            pow_le_pow_of_le_one (by positivity) hae hNk
          have h2 : C' + a * k ≤ (C' + 2) * N := by nlinarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity)
            (by positivity)
  -- tail
  obtain ⟨hts, htl⟩ := tail_sum hη k ⌊Real.exp (b * k / η)⌋₊ (Y := b * k)
    (by nlinarith) (Nat.lt_floor_add_one _)
  have htail0 : ‖∑' m : ℕ, f (m + (⌊Real.exp (b * k / η)⌋₊ + 1))‖ ≤
      (b * k) ^ k * Real.exp (-(b * k / 2)) / k.factorial * Ssum (1 + η / 2) := by
    have hs' : Summable (fun m : ℕ => ‖f (m + (⌊Real.exp (b * k / η)⌋₊ + 1))‖) := by
      simp only [hfdef, norm_wt_phase hη.le]; exact hts
    refine (norm_tsum_le_tsum_norm hs').trans ?_
    simp only [hfdef, norm_wt_phase hη.le]
    exact htl
  have hSt : η * Ssum (1 + η / 2) ≤ C' + 2 := by
    have := hS (1 + η / 2) (by linarith)
    rw [add_sub_cancel_left, one_div_div] at this
    calc η * Ssum (1 + η / 2) ≤ η * (C' + 2 / η) := by gcongr
      _ = η * C' + 2 := by field_simp
      _ ≤ C' + 2 := by nlinarith
  have htail : η * ‖∑' m : ℕ, f (m + (⌊Real.exp (b * k / η)⌋₊ + 1))‖ ≤
      (b * Real.exp (1 - b / 2)) ^ N * ((C' + 2) * N) := by
    have hS0 : 0 ≤ Ssum (1 + η / 2) := Ssum_nonneg _
    have hbe0 : 0 ≤ b * Real.exp (1 - b / 2) := by positivity
    calc η * ‖∑' m : ℕ, f (m + (⌊Real.exp (b * k / η)⌋₊ + 1))‖
        ≤ η * ((b * k) ^ k * Real.exp (-(b * k / 2)) / k.factorial * Ssum (1 + η / 2)) := by
          gcongr
      _ = b ^ k * ((k : ℝ) ^ k / k.factorial) * Real.exp (-(b * k / 2)) *
            (η * Ssum (1 + η / 2)) := by rw [mul_pow]; ring
      _ ≤ b ^ k * Real.exp 1 ^ k * Real.exp (-(b * k / 2)) * (C' + 2) := by gcongr
      _ = (b * Real.exp (1 - b / 2)) ^ k * (C' + 2) := by rw [exp_pow_split]
      _ ≤ (b * Real.exp (1 - b / 2)) ^ N * ((C' + 2) * N) := by
          have h1 : (b * Real.exp (1 - b / 2)) ^ k ≤ (b * Real.exp (1 - b / 2)) ^ N :=
            pow_le_pow_of_le_one hbe0 hbe hNk
          have h2 : C' + 2 ≤ (C' + 2) * N := by nlinarith
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hA := hHa N hN
  have hB := hHb N hN
  have e1 : Real.exp 1 * (a * Real.exp 1) ^ N * ((C' + 2) * N) =
      (8 * (Real.exp 1 * (C' + 2)) * N * (a * Real.exp 1) ^ N) / 8 := by ring
  have e2 : (b * Real.exp (1 - b / 2)) ^ N * ((C' + 2) * N) =
      (8 * (C' + 2) * N * (b * Real.exp (1 - b / 2)) ^ N) / 8 := by ring
  have hs2 := mul_le_mul_of_nonneg_left hsplit hη.le
  rw [mul_add, mul_add] at hs2
  linarith

end HD1

namespace HD1

open ArithmeticFunction

/-- Norm form of the detector identity. -/
lemma ident_norm {γ η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 20) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball (ctr γ) (11 / 20)))
    (hrep : ∀ s ∈ ball (ctr γ) (11 / 20), Z s ≠ 0 →
      deriv Z s / Z s = ∑ u ∈ zball (ctr γ), (mult u : ℂ) / (s - u) + G s)
    (k : ℕ) {s0 : ℂ} (hs0 : s0 = ((1 + η : ℝ) : ℂ) + γ * I) :
    (k.factorial : ℝ) * ‖∑ u ∈ zball (ctr γ), (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹‖ ≤
      k.factorial * ‖((s0 - 1) ^ (k + 1))⁻¹‖ +
        ‖LSeries (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0‖ +
        ‖iteratedDeriv k G s0‖ := by
  have hid := ident hη hη' hG hrep k hs0
  set E : ℂ := (-1) ^ k * (k.factorial : ℂ)
  have hsum : ∑ u ∈ zball (ctr γ), (mult u : ℂ) * ((-1) ^ k * k.factorial * ((s0 - u) ^ (k + 1))⁻¹)
      = E * ∑ u ∈ zball (ctr γ), (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
  have heq : E * ∑ u ∈ zball (ctr γ), (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹ =
      E * ((s0 - 1) ^ (k + 1))⁻¹ -
        (-1) ^ k * LSeries (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0 -
        iteratedDeriv k G s0 := by
    linear_combination hid - hsum
  have hE : ‖E‖ = k.factorial := by simp [E]
  have := congrArg norm heq
  rw [norm_mul, hE] at this
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hE, norm_mul]
  simp

set_option maxHeartbeats 1000000 in
lemma lower_LS {C C2 c q R K0 κ1 : ℝ} (hC : 0 < C) (hC2 : 0 < C2) (hq : 0 < q) (hqc : 4 * q ≤ c)
    (hT : ∀ (S : Finset ℂ) (b : ℂ → ℝ) (N : ℕ), S.card ≤ N →
      (∀ z ∈ S, ‖z‖ ≤ 1) → (∀ z ∈ S, 1 ≤ b z) → (∃ z ∈ S, ‖z‖ = 1) →
      ∃ ν : ℕ, N + 1 ≤ ν ∧ ν ≤ 2 * N ∧ c ^ N ≤ ‖∑ z ∈ S, (b z : ℂ) * z ^ ν‖)
    (hloc : ∀ γ η : ℝ, 0 < η → η ≤ 1 / 10 →
      ∑ u ∈ zball (ctr γ), (mult u : ℝ) / ‖((1 + η : ℝ) : ℂ) + γ * I - u‖ ^ 2 ≤
        C2 * (Real.log (|γ| + 3) + 1 / η) / η)
    (hR2 : 2 ≤ R) (hRg : ∀ M : ℕ, 1 ≤ M → (32 * C2 / q) * M * (1 / R) ^ M ≤ q ^ M)
    (hK0 : 2 * C2 * R ^ 2 ≤ K0) (hK02 : 2 ≤ K0)
    (hκ : κ1 ≤ 1 / 20) (hκA : ∀ N : ℕ, 1 ≤ N → 8 * N * κ1 ^ N ≤ q ^ N)
    (hκG : ∀ N : ℕ, 1 ≤ N → 8 * C * N * (10 * κ1 / 3) ^ N ≤ q ^ N) (hκ3 : 10 * κ1 / 3 ≤ 1)
    {γ η lam : ℝ} (hη : 0 < η) (hηκ : η ≤ κ1) (hlam : 1 ≤ lam) (hγ : 1 < |γ|)
    (hL : Real.log (|γ| + 3) ≤ lam / η)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball (ctr γ) (11 / 20)))
    (hGb : ∀ s : ℂ, ‖s - ctr γ‖ ≤ 1 / 2 → ‖G s‖ ≤ C * Real.log (|γ| + 3))
    (hrep : ∀ s ∈ ball (ctr γ) (11 / 20), Z s ≠ 0 →
      deriv Z s / Z s = ∑ u ∈ zball (ctr γ), (mult u : ℂ) / (s - u) + G s)
    {ρ : ℂ} (hρ : Z ρ = 0) (hρim : ρ.im = γ) (hρre : 1 - η ≤ ρ.re) :
    ∃ k : ℕ, ⌈K0 * lam⌉₊ ≤ k ∧ k + 1 ≤ 2 * ⌈K0 * lam⌉₊ ∧
      (5 / 8) * q ^ ⌈K0 * lam⌉₊ ≤ η ^ (k + 1) / k.factorial *
        ‖LSeries (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ)))
          (((1 + η : ℝ) : ℂ) + γ * I)‖ := by
  classical
  set N := ⌈K0 * lam⌉₊ with hNdef
  have hNge : K0 * lam ≤ N := Nat.le_ceil _
  have hN2R : (2 : ℝ) ≤ N := by nlinarith
  have hN2 : 2 ≤ N := by exact_mod_cast hN2R
  have hlamN : lam ≤ N := by nlinarith
  have hη20 : η ≤ 1 / 20 := hηκ.trans hκ
  have hκ0 : 0 < κ1 := hη.trans_le hηκ
  set s0 : ℂ := ((1 + η : ℝ) : ℂ) + γ * I with hs0
  set F := zball (ctr γ) with hF
  have hs0re : s0.re = 1 + η := by simp [hs0]
  have hs0im : s0.im = γ := by simp [hs0]
  -- the weighted zero sum
  have hW : ∑ u ∈ F, (mult u : ℝ) / ‖s0 - u‖ ^ 2 ≤ 2 * C2 * lam / η ^ 2 := by
    refine (hloc γ η hη (by linarith)).trans ?_
    have h1 : 1 / η ≤ lam / η := div_le_div_of_nonneg_right hlam hη.le
    calc C2 * (Real.log (|γ| + 3) + 1 / η) / η ≤ C2 * (lam / η + lam / η) / η := by gcongr
      _ = 2 * C2 * lam / η ^ 2 := by field_simp; ring
  have hre_lt : ∀ u ∈ F, u.re < 1 := fun u hu => Z_re_lt_one (mem_zball.1 hu).1
  have hpos_u : ∀ u ∈ F, η < ‖s0 - u‖ := by
    intro u hu
    have h1 := Complex.abs_re_le_norm (s0 - u)
    have h2 : (s0 - u).re = 1 + η - u.re := by simp [hs0re]
    rw [h2] at h1
    have := hre_lt u hu
    rw [abs_of_pos (by linarith)] at h1
    linarith
  -- the zero ρ
  have hρ1 : ρ.re < 1 := Z_re_lt_one hρ
  have hρF : ρ ∈ F := by
    rw [hF, mem_zball]
    refine ⟨hρ, ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    have : ρ - ctr γ = ((ρ.re - 6 / 5 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [ctr, hρim]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hs0ρ : ‖s0 - ρ‖ ≤ 2 * η := by
    have : s0 - ρ = ((1 + η - ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hs0, hρim]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨u1, hu1F, hmin⟩ := Finset.exists_min_image F (fun u => ‖s0 - u‖) ⟨ρ, hρF⟩
  have hd2 : ‖s0 - u1‖ ≤ 2 * η := (hmin ρ hρF).trans hs0ρ
  have hdpos : 0 < ‖s0 - u1‖ := hη.trans (hpos_u u1 hu1F)
  -- near set
  set S0 := F.filter (fun u => ‖s0 - u‖ ≤ R * η) with hS0
  have hRη : 0 < R * η := by positivity
  have hu1S : u1 ∈ S0 := Finset.mem_filter.2 ⟨hu1F, by nlinarith⟩
  have hcard : ∑ u ∈ S0, (mult u : ℝ) ≤ N := by
    have h1 : ∑ u ∈ S0, (mult u : ℝ) ≤ ∑ u ∈ S0, (R * η) ^ 2 * ((mult u : ℝ) / ‖s0 - u‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨huF, hun⟩ := Finset.mem_filter.1 hu
      have hp := hpos_u u huF
      have hm : (0 : ℝ) ≤ mult u := Nat.cast_nonneg _
      have hsq : ‖s0 - u‖ ^ 2 ≤ (R * η) ^ 2 := pow_le_pow_left₀ (by linarith) hun 2
      rw [mul_div_assoc', le_div_iff₀ (pow_pos (hη.trans hp) 2)]
      nlinarith
    have h2 : ∑ u ∈ S0, (mult u : ℝ) / ‖s0 - u‖ ^ 2 ≤ ∑ u ∈ F, (mult u : ℝ) / ‖s0 - u‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u _ _ => by positivity)
    rw [← Finset.mul_sum] at h1
    calc ∑ u ∈ S0, (mult u : ℝ) ≤ (R * η) ^ 2 * (2 * C2 * lam / η ^ 2) := by
          refine h1.trans ?_
          gcongr
          exact h2.trans hW
      _ = 2 * C2 * R ^ 2 * lam := by field_simp
      _ ≤ K0 * lam := by gcongr
      _ ≤ N := hNge
  have hmS : ∀ u ∈ S0, (1 : ℝ) ≤ mult u := by
    intro u hu
    have := mult_pos (mem_zball.1 (Finset.mem_filter.1 hu).1).1
    exact_mod_cast this
  obtain ⟨ν, hν1, hν2, hνc⟩ := turan_near hT S0 (fun u => (mult u : ℝ)) hmS s0 u1 hu1S
    (fun u hu => hmin u (Finset.mem_filter.1 hu).1) hdpos N hcard
  obtain ⟨k, rfl⟩ : ∃ k, ν = k + 1 := ⟨ν - 1, by omega⟩
  refine ⟨k, by omega, hν2, ?_⟩
  simp only [Complex.ofReal_natCast] at hνc
  set X := ‖∑ u ∈ S0, (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹‖ with hX
  -- (i) main term
  have hmain : q ^ N ≤ η ^ (k + 1) * X := by
    have h1 : (4 * q) ^ N ≤ c ^ N := pow_le_pow_left₀ (by positivity) hqc N
    have h2 : ‖s0 - u1‖ ^ (k + 1) ≤ (2 * η) ^ (k + 1) := pow_le_pow_left₀ hdpos.le hd2 _
    have h3 : (2 : ℝ) ^ (k + 1) ≤ 4 ^ N := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hX0 : 0 ≤ X := norm_nonneg _
    have h4 : (4 * q) ^ N ≤ 2 ^ (k + 1) * (η ^ (k + 1) * X) := by
      calc (4 * q) ^ N ≤ ‖s0 - u1‖ ^ (k + 1) * X := h1.trans hνc
        _ ≤ (2 * η) ^ (k + 1) * X := by gcongr
        _ = 2 ^ (k + 1) * (η ^ (k + 1) * X) := by rw [mul_pow]; ring
    rw [mul_pow] at h4
    have h5 : (2 : ℝ) ^ (k + 1) * q ^ N ≤ 2 ^ (k + 1) * (η ^ (k + 1) * X) := by
      calc (2 : ℝ) ^ (k + 1) * q ^ N ≤ 4 ^ N * q ^ N := by gcongr
        _ ≤ _ := h4
    exact le_of_mul_le_mul_left h5 (by positivity)
  -- (ii) identity, split near/far
  set Fr := ∑ u ∈ F.filter (fun u => ¬ ‖s0 - u‖ ≤ R * η), (mult u : ℝ) * (1 / ‖s0 - u‖ ^ (k + 1))
    with hFr
  set Lv := ‖LSeries (LSeries.logMul^[k] (fun n => (vonMangoldt n : ℂ))) s0‖
  set Dv := ‖iteratedDeriv k G s0‖
  set Av := ‖((s0 - 1) ^ (k + 1))⁻¹‖
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hii : X ≤ Av + Lv / k.factorial + Dv / k.factorial + Fr := by
    have hI := ident_norm hη hη20 hG hrep k hs0
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun u => ‖s0 - u‖ ≤ R * η)
      (fun u => (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹)
    have hfar : ‖∑ u ∈ F.filter (fun u => ¬ ‖s0 - u‖ ≤ R * η),
        (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹‖ ≤ Fr := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro u _
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, one_div]
    have hY : X ≤ ‖∑ u ∈ F, (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹‖ + Fr := by
      rw [hX, eq_sub_of_add_eq hsplit]
      exact (norm_sub_le _ _).trans (by linarith [hfar])
    have hI' : ‖∑ u ∈ F, (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹‖ ≤
        Av + Lv / k.factorial + Dv / k.factorial := by
      rw [← mul_le_mul_iff_of_pos_left hfact]
      calc (k.factorial : ℝ) * ‖∑ u ∈ F, (mult u : ℂ) * ((s0 - u) ^ (k + 1))⁻¹‖ ≤
          k.factorial * Av + Lv + Dv := hI
        _ = k.factorial * (Av + Lv / k.factorial + Dv / k.factorial) := by field_simp
    linarith
  -- (iii) pole term
  have hηk : η ^ (k + 1) ≤ κ1 ^ N := by
    calc η ^ (k + 1) ≤ κ1 ^ (k + 1) := pow_le_pow_left₀ hη.le hηκ _
      _ ≤ κ1 ^ N := pow_le_pow_of_le_one hκ0.le (by linarith) (by omega)
  have hiii : η ^ (k + 1) * Av ≤ q ^ N / 8 := by
    have hA1 : Av ≤ 1 := by
      have h1 : 1 ≤ ‖s0 - 1‖ := by
        have := Complex.abs_im_le_norm (s0 - 1)
        have h2 : (s0 - 1).im = γ := by simp [hs0im]
        rw [h2] at this; linarith
      simp only [Av, norm_inv, norm_pow]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    have := hκA N (by omega)
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have h8 : 8 * κ1 ^ N ≤ 8 * N * κ1 ^ N := by
      have : 0 ≤ κ1 ^ N := by positivity
      nlinarith
    calc η ^ (k + 1) * Av ≤ κ1 ^ N * 1 := by
          gcongr
      _ ≤ q ^ N / 8 := by linarith
  -- (iv) holomorphic remainder
  have hiv : η ^ (k + 1) * (Dv / k.factorial) ≤ q ^ N / 8 := by
    have hc := cauchyG hη hη20 hG hGb k hs0
    have hlog0 : 0 ≤ Real.log (|γ| + 3) := Real.log_nonneg (by linarith [abs_nonneg γ])
    have h1 : Dv / k.factorial ≤ C * (lam / η) * (10 / 3) ^ k := by
      rw [div_le_iff₀ hfact]
      refine hc.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : C * Real.log (|γ| + 3) ≤ C * (lam / η) := mul_le_mul_of_nonneg_left hL hC.le
      have e : (10 / 3 : ℝ) ^ k * (3 / 10) ^ k = 1 := by rw [← mul_pow]; norm_num
      calc (k.factorial : ℝ) * (C * Real.log (|γ| + 3)) ≤ k.factorial * (C * (lam / η)) := by
            gcongr
        _ = C * (lam / η) * (10 / 3) ^ k * k.factorial * (3 / 10) ^ k := by
            rw [show C * (lam / η) * (10 / 3) ^ k * k.factorial * (3 / 10) ^ k =
              C * (lam / η) * k.factorial * ((10 / 3) ^ k * (3 / 10) ^ k) by ring, e]; ring
    have h2 : η ^ (k + 1) * (C * (lam / η) * (10 / 3) ^ k) = C * lam * (10 * η / 3) ^ k := by
      have e3 : (10 * η / 3) ^ k = η ^ k * (10 / 3) ^ k := by rw [← mul_pow]; ring_nf
      have e4 : η / η = 1 := div_self hη.ne'
      rw [e3, pow_succ]
      calc η ^ k * η * (C * (lam / η) * (10 / 3) ^ k) =
          C * lam * (η / η) * (η ^ k * (10 / 3) ^ k) := by ring
        _ = _ := by rw [e4, mul_one]
    have h3 : (10 * η / 3) ^ k ≤ (10 * κ1 / 3) ^ N := by
      calc (10 * η / 3) ^ k ≤ (10 * κ1 / 3) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (10 * κ1 / 3) ^ N := pow_le_pow_of_le_one (by positivity) hκ3 (by omega)
    have := hκG N (by omega)
    calc η ^ (k + 1) * (Dv / k.factorial) ≤ η ^ (k + 1) * (C * (lam / η) * (10 / 3) ^ k) := by
          gcongr
      _ = C * lam * (10 * η / 3) ^ k := h2
      _ ≤ C * N * (10 * κ1 / 3) ^ N := by gcongr
      _ ≤ q ^ N / 8 := by linarith
  -- (v) far zeros
  have hv : η ^ (k + 1) * Fr ≤ q ^ N / 8 := by
    have hk1 : 2 ≤ k + 1 := by omega
    have h1 : Fr ≤ 1 / (R * η) ^ (k + 1 - 2) * (2 * C2 * lam / η ^ 2) := by
      calc Fr ≤ ∑ u ∈ F.filter (fun u => ¬ ‖s0 - u‖ ≤ R * η),
            (mult u : ℝ) * (1 / (R * η) ^ (k + 1 - 2) * (1 / ‖s0 - u‖ ^ 2)) := by
            apply Finset.sum_le_sum
            intro u hu
            have hfu := (Finset.mem_filter.1 hu).2
            push Not at hfu
            exact mul_le_mul_of_nonneg_left (far_le hRη hfu (k + 1) hk1) (Nat.cast_nonneg _)
        _ = 1 / (R * η) ^ (k + 1 - 2) *
              ∑ u ∈ F.filter (fun u => ¬ ‖s0 - u‖ ≤ R * η), (mult u : ℝ) / ‖s0 - u‖ ^ 2 := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
        _ ≤ 1 / (R * η) ^ (k + 1 - 2) * ∑ u ∈ F, (mult u : ℝ) / ‖s0 - u‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun u _ _ => by positivity)
        _ ≤ 1 / (R * η) ^ (k + 1 - 2) * (2 * C2 * lam / η ^ 2) :=
            mul_le_mul_of_nonneg_left hW (by positivity)
    have hk' : k + 1 - 2 + 2 = k + 1 := by omega
    have h2 : η ^ (k + 1) * (1 / (R * η) ^ (k + 1 - 2) * (2 * C2 * lam / η ^ 2)) =
        2 * C2 * lam * (1 / R) ^ (k + 1 - 2) := by
      have hpw : η ^ (k + 1) = η ^ (k + 1 - 2) * η ^ 2 := by
        rw [← pow_add, hk']
      rw [hpw, mul_pow, one_div_pow]
      field_simp
    have hR1 : 1 / R ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h3 : (1 / R) ^ (k + 1 - 2) ≤ (1 / R) ^ (N - 1) :=
      pow_le_pow_of_le_one (by positivity) hR1 (by omega)
    have hM := hRg (N - 1) (by omega)
    have hNM : (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hqN : q ^ N = q * q ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hM1 : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N - 1)
    set M : ℝ := ((N - 1 : ℕ) : ℝ)
    set P := (1 / R) ^ (N - 1)
    have hP0 : 0 ≤ P := by positivity
    have hM' : 32 * C2 * M * P ≤ q * q ^ (N - 1) := by
      have := mul_le_mul_of_nonneg_left hM hq.le
      calc 32 * C2 * M * P = q * (32 * C2 / q * M * P) := by field_simp
        _ ≤ q * q ^ (N - 1) := this
    calc η ^ (k + 1) * Fr ≤ η ^ (k + 1) * (1 / (R * η) ^ (k + 1 - 2) * (2 * C2 * lam / η ^ 2)) := by
          gcongr
      _ = 2 * C2 * lam * (1 / R) ^ (k + 1 - 2) := h2
      _ ≤ 2 * C2 * N * P := by gcongr
      _ ≤ q ^ N / 8 := by
          rw [hNM, hqN]
          have hx : 0 ≤ 2 * C2 * P * (M - 1) :=
            mul_nonneg (mul_nonneg (by positivity) hP0) (by linarith)
          nlinarith
  -- combine
  have hcomb : η ^ (k + 1) * X ≤ η ^ (k + 1) * Av + η ^ (k + 1) * (Lv / k.factorial) +
      η ^ (k + 1) * (Dv / k.factorial) + η ^ (k + 1) * Fr := by
    have := mul_le_mul_of_nonneg_left hii (by positivity : (0 : ℝ) ≤ η ^ (k + 1))
    linarith [this]
  have e : η ^ (k + 1) / k.factorial * Lv = η ^ (k + 1) * (Lv / k.factorial) := by ring
  rw [e]
  linarith

end HD1

namespace HD1

lemma b_choice {x : ℝ} (hx : 0 < x) : ∃ b : ℝ, 2 ≤ b ∧ b * Real.exp (1 - b / 2) ≤ x := by
  have h0 : 0 ≤ 8 * Real.exp 1 / x := by positivity
  refine ⟨2 + 8 * Real.exp 1 / x, by linarith, ?_⟩
  set b := 2 + 8 * Real.exp 1 / x
  have hb : 0 < b := by positivity
  have hbx : 8 * Real.exp 1 / x ≤ b := by simp only [b]; linarith
  have h1 : (b / 2) ^ 2 / 2 ≤ Real.exp (b / 2) := by
    have := Real.pow_div_factorial_le_exp (b / 2) (by positivity) 2
    simpa using this
  have h2 : Real.exp (1 - b / 2) = Real.exp 1 / Real.exp (b / 2) := by
    rw [Real.exp_sub]
  rw [h2, mul_div_assoc', div_le_iff₀ (Real.exp_pos _)]
  have h3 : 8 * Real.exp 1 ≤ x * b := by
    rw [div_le_iff₀ hx] at hbx; linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

end HD1

set_option maxHeartbeats 4000000 in
theorem detector : ∃ K0 A1 κ1 a b : ℝ, 0 < K0 ∧ 0 < κ1 ∧ 0 < a ∧ a < b ∧
    ∀ T : ℝ, 3 ≤ T → ∀ lam : ℝ, 1 ≤ lam → lam ≤ κ1 * Real.log (T + 3) →
    ∀ ρ : ℂ, Z ρ = 0 → 1 - lam / Real.log (T + 3) ≤ ρ.re → 1 < |ρ.im| → |ρ.im| ≤ T →
    ∃ k : ℕ, k ≤ 2 * ⌈K0 * lam⌉₊ ∧
      (T + 3) ^ 10 ≤ (⌊Real.exp (a * k * Real.log (T + 3) / lam)⌋₊ : ℝ) ∧
      Real.exp (-(A1 * lam)) * Real.log (T + 3) ≤ lam *
        ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k * Real.log (T + 3) / lam)⌋₊
            ⌊Real.exp (b * k * Real.log (T + 3) / lam)⌋₊,
          wt (lam / Real.log (T + 3)) k n * (n : ℂ) ^ (-((ρ.im : ℂ) * I))‖ := by
  obtain ⟨C, hC, hlandG⟩ := landauG
  obtain ⟨C2, hC2, hloc⟩ := local_sum
  obtain ⟨c, hc, hT⟩ := turan
  obtain ⟨C', hC', hS⟩ := HD1.Ssum_bound
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num); linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  -- q
  set q := min c (1 / 2) / 4 with hqdef
  have hq : 0 < q := by positivity
  have hqc : 4 * q ≤ c := by simp only [hqdef]; linarith [min_le_left c (1 / 2)]
  have hq8 : q ≤ 1 / 8 := by simp only [hqdef]; linarith [min_le_right c (1 / 2)]
  -- R
  set AR := 32 * C2 / q with hAR
  have hAR0 : 0 ≤ AR := by positivity
  set R := 2 * (AR + 1) / q + 2 with hRdef
  have hR0 : 0 ≤ 2 * (AR + 1) / q := by positivity
  have hR2 : 2 ≤ R := by linarith
  have hRg : ∀ M : ℕ, 1 ≤ M → (32 * C2 / q) * M * (1 / R) ^ M ≤ q ^ M := by
    intro M hM
    apply HD1.geomV hAR0 hq (by positivity) _ hM
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have : 2 * (AR + 1) ≤ q * R := by
      have h := (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2) :
        2 * (AR + 1) / q ≤ 2 * (AR + 1) / q + 2)
      rw [div_le_iff₀ hq] at h; linarith
    linarith
  -- a
  set Aa := 8 * (Real.exp 1 * (C' + 2)) with hAa
  have hAa0 : 0 ≤ Aa := by positivity
  set a := q / (2 * (Aa + 1)) / Real.exp 1 with hadef
  have ha : 0 < a := by positivity
  have hae_eq : a * Real.exp 1 = q / (2 * (Aa + 1)) := by
    simp only [hadef]; field_simp
  have hae : a * Real.exp 1 ≤ 1 := by
    rw [hae_eq, div_le_one (by positivity)]; nlinarith
  have hHa : ∀ N : ℕ, 1 ≤ N → 8 * (Real.exp 1 * (C' + 2)) * N * (a * Real.exp 1) ^ N ≤ q ^ N :=
    fun N hN => HD1.geomV hAa0 hq (by positivity) hae_eq.le hN
  -- b
  set Ab := 8 * (C' + 2) with hAb
  have hAb0 : 0 ≤ Ab := by positivity
  obtain ⟨b, hb2, hbx⟩ := HD1.b_choice (x := q / (2 * (Ab + 1))) (by positivity)
  have hbe : b * Real.exp (1 - b / 2) ≤ 1 := by
    refine hbx.trans ?_
    rw [div_le_one (by positivity)]; nlinarith
  have hHb : ∀ N : ℕ, 1 ≤ N → 8 * (C' + 2) * N * (b * Real.exp (1 - b / 2)) ^ N ≤ q ^ N :=
    fun N hN => HD1.geomV hAb0 hq (by positivity) hbx hN
  have ha1 : a ≤ 1 := by nlinarith
  have hab : a < b := by linarith
  -- K0
  set K0 := max (max (2 * C2 * R ^ 2) 2) (11 / a) with hK0def
  have hK0a : 2 * C2 * R ^ 2 ≤ K0 := (le_max_left _ _).trans (le_max_left _ _)
  have hK02 : 2 ≤ K0 := (le_max_right _ _).trans (le_max_left _ _)
  have hK0b : 11 / a ≤ K0 := le_max_right _ _
  have haK : 11 ≤ a * K0 := by rw [div_le_iff₀ ha] at hK0b; linarith
  -- κ1
  set κ1 := min (1 / 20) (min (q / 18) (3 * q / (20 * (8 * C + 1)))) with hκdef
  have hκ0 : 0 < κ1 := by positivity
  have hκ20 : κ1 ≤ 1 / 20 := min_le_left _ _
  have hκq : κ1 ≤ q / 18 := (min_le_right _ _).trans (min_le_left _ _)
  have hκC : κ1 ≤ 3 * q / (20 * (8 * C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hκA : ∀ N : ℕ, 1 ≤ N → 8 * N * κ1 ^ N ≤ q ^ N := by
    intro N hN
    exact HD1.geomV (A := 8) (by norm_num) hq hκ0.le (by linarith) hN
  have hκG : ∀ N : ℕ, 1 ≤ N → 8 * C * N * (10 * κ1 / 3) ^ N ≤ q ^ N := by
    intro N hN
    apply HD1.geomV (by positivity) hq (by positivity) _ hN
    have : 3 * q / (20 * (8 * C + 1)) * 10 / 3 = q / (2 * (8 * C + 1)) := by field_simp; ring
    linarith
  have hκ3 : 10 * κ1 / 3 ≤ 1 := by linarith
  -- A1
  set A1 := (K0 + 1) * (-Real.log q) + 1 with hA1
  refine ⟨K0, A1, κ1, a, b, by linarith, hκ0, ha, hab, ?_⟩
  intro T hT3 lam hlam hlamκ ρ hρ hρre hγ1 hγT
  set L := Real.log (T + 3) with hLdef
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set η := lam / L with hηdef
  have hη : 0 < η := by positivity
  have hηκ : η ≤ κ1 := by rw [hηdef, div_le_iff₀ hL0]; linarith
  have hlamη : lam / η = L := by rw [hηdef]; field_simp
  set γ := ρ.im with hγdef
  have hLγ : Real.log (|γ| + 3) ≤ lam / η := by
    rw [hlamη]; exact Real.log_le_log (by positivity) (by linarith)
  obtain ⟨-, G, hG, hGb, hrep⟩ := hlandG γ
  obtain ⟨k, hNk, hk2, hlow⟩ := HD1.lower_LS hC hC2 hq hqc hT hloc hR2 hRg hK0a hK02 hκ20 hκA hκG
    hκ3 hη hηκ hlam hγ1 hLγ hG hGb hrep hρ rfl hρre
  set N := ⌈K0 * lam⌉₊ with hNdef
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := le_trans (by nlinarith) (Nat.le_ceil (K0 * lam))
    exact_mod_cast this
  obtain ⟨hf, hLS⟩ := HD1.LS_wt hη γ k (s0 := ((1 + η : ℝ) : ℂ) + γ * I) rfl
  have hmain : (5 / 8) * q ^ N ≤ η * ‖∑' n : ℕ, wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))‖ := by
    have := congrArg norm hLS
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hη, abs_of_nonneg (by positivity)] at this
    rw [← this]; exact hlow
  have htr := HD1.trunc hη (by linarith) ha hae hb2 hbe hC' hS hHa hHb γ k N hN1 hNk (by omega) hf
    hmain
  have e1 : a * k * L / lam = a * k / η := by rw [hηdef]; field_simp
  have e2 : b * k * L / lam = b * k / η := by rw [hηdef]; field_simp
  refine ⟨k, by omega, ?_, ?_⟩
  · rw [e1]
    have hNge : K0 * lam ≤ N := Nat.le_ceil _
    have hkN : (N : ℝ) ≤ k := by exact_mod_cast hNk
    have h1 : 11 * L ≤ a * k / η := by
      rw [le_div_iff₀ hη, hηdef]
      have : 11 * lam ≤ a * k := by
        have i1 : 11 * lam ≤ a * K0 * lam := mul_le_mul_of_nonneg_right haK (by linarith)
        have i2 : a * (K0 * lam) ≤ a * N := mul_le_mul_of_nonneg_left hNge ha.le
        have i3 : a * N ≤ a * k := mul_le_mul_of_nonneg_left hkN ha.le
        linarith [mul_assoc a K0 lam]
      calc 11 * L * (lam / L) = 11 * lam := by field_simp
        _ ≤ a * k := this
    have h2 : (T + 3) ^ 11 ≤ Real.exp (a * k / η) := by
      calc (T + 3) ^ 11 = Real.exp (11 * L) := by
            rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, hLdef,
              Real.exp_log (by linarith)]
        _ ≤ Real.exp (a * k / η) := Real.exp_le_exp.2 h1
    have h3 := Nat.sub_one_lt_floor (Real.exp (a * k / η))
    have h4 : (T + 3) ^ 10 + 1 ≤ (T + 3) ^ 11 := by
      have h6 : (1 : ℝ) ≤ (T + 3) ^ 10 := one_le_pow₀ (by linarith)
      have h5 : (T + 3) ^ 10 * 1 ≤ (T + 3) ^ 10 * (T + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h7 : (T + 3) ^ 11 = (T + 3) ^ 10 * (T + 2) + (T + 3) ^ 10 := by ring
      linarith
    linarith
  · rw [e1, e2]
    -- exp(-(A1 lam)) ≤ (3/8) q^N
    have hlogq : Real.log q < 0 := Real.log_neg hq (by linarith)
    have hNle : (N : ℝ) ≤ (K0 + 1) * lam := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ K0 * lam)
      nlinarith
    have hqN : q ^ N = Real.exp (N * Real.log q) := by
      rw [Real.exp_nat_mul, Real.exp_log hq]
    have hex : Real.exp (-(A1 * lam)) ≤ (3 / 8) * q ^ N := by
      rw [hqN]
      have h1 : -(A1 * lam) ≤ N * Real.log q + (-1) := by
        rw [hA1]
        have : (K0 + 1) * lam * Real.log q ≤ N * Real.log q := by nlinarith
        nlinarith
      have h2 : Real.exp (-1) ≤ 3 / 8 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.exp_one_gt_d9; linarith
      calc Real.exp (-(A1 * lam)) ≤ Real.exp (N * Real.log q + (-1)) := Real.exp_le_exp.2 h1
        _ = Real.exp (N * Real.log q) * Real.exp (-1) := Real.exp_add _ _
        _ ≤ Real.exp (N * Real.log q) * (3 / 8) := by gcongr
        _ = 3 / 8 * Real.exp (N * Real.log q) := by ring
    have hlamL : lam = L * η := by rw [hηdef]; field_simp
    rw [hlamL]
    calc Real.exp (-(A1 * (L * η))) * L = Real.exp (-(A1 * lam)) * L := by rw [← hlamL]
      _ ≤ (3 / 8) * q ^ N * L := by gcongr
      _ ≤ (η * ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k / η)⌋₊ ⌊Real.exp (b * k / η)⌋₊,
            wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))‖) * L := by gcongr
      _ = L * η * ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k / η)⌋₊ ⌊Real.exp (b * k / η)⌋₊,
            wt η k n * (n : ℂ) ^ (-((γ : ℂ) * I))‖ := by ring



-- ===== from HD2.lean =====


namespace HD2

theorem Ncount_nonneg (σ T : ℝ) : 0 ≤ Ncount σ T := by
  unfold Ncount
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem Ncount_mono {σ σ' T T' : ℝ} (hσ : σ' ≤ σ) (hT : T ≤ T') :
    Ncount σ T ≤ Ncount σ' T' := by
  unfold Ncount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [mem_zbox] at hρ ⊢
    obtain ⟨h1, h2, h3⟩ := hρ
    exact ⟨h1, by linarith, by linarith⟩
  · intros; positivity

theorem Ncount_eq_zero {σ T : ℝ} (hσ : 1 < σ) : Ncount σ T = 0 := by
  unfold Ncount
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [mem_zbox] at hρ
  have := Z_re_lt_one hρ.1
  linarith [hρ.2.1]

theorem log_T3_ge {T : ℝ} (hT : 3 ≤ T) : 1 ≤ Real.log (T + 3) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) : Real.log (⌊Real.exp x⌋₊ : ℝ) ≤ x := by
  rcases Nat.eq_zero_or_pos ⌊Real.exp x⌋₊ with h | h
  · rw [h]; simpa using hx
  · calc Real.log (⌊Real.exp x⌋₊ : ℝ) ≤ Real.log (Real.exp x) :=
          Real.log_le_log (by exact_mod_cast h) (Nat.floor_le (Real.exp_pos x).le)
      _ = x := Real.log_exp x

theorem wt_norm_le {η : ℝ} (hη : 0 ≤ η) (k n : ℕ) :
    ‖wt η k n‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  unfold wt
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hy : 0 ≤ η * Real.log n := mul_nonneg hη (Real.log_natCast_nonneg n)
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have e : (ArithmeticFunction.vonMangoldt n : ℝ) / n * (η * Real.log n) ^ k *
      Real.exp (-(η * Real.log n)) / (k.factorial : ℝ) =
      (ArithmeticFunction.vonMangoldt n : ℝ) / n *
        ((η * Real.log n) ^ k / (k.factorial : ℝ) * Real.exp (-(η * Real.log n))) := by ring
  have h1 : (η * Real.log n) ^ k / (k.factorial : ℝ) * Real.exp (-(η * Real.log n)) ≤ 1 := by
    calc (η * Real.log n) ^ k / (k.factorial : ℝ) * Real.exp (-(η * Real.log n))
        ≤ Real.exp (η * Real.log n) * Real.exp (-(η * Real.log n)) := by
          gcongr
          exact Real.pow_div_factorial_le_exp _ hy k
      _ = 1 := by rw [← Real.exp_add]; simp
  have h0 : 0 ≤ (η * Real.log n) ^ k / (k.factorial : ℝ) * Real.exp (-(η * Real.log n)) := by
    positivity
  rw [e, abs_of_nonneg (mul_nonneg hΛ h0)]
  exact mul_le_of_le_one_right hΛ h1

/-- Window bound (c). -/
theorem window : ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ T : ℝ, 3 ≤ T → ∀ σ lam : ℝ, 1 ≤ lam →
    lam / Real.log (T + 3) ≤ 1 / 10 → 1 - lam / Real.log (T + 3) ≤ σ → ∀ j : ℤ,
    ∑ ρ ∈ (zbox σ T).filter (fun ρ => ⌊ρ.im * Real.log (T + 3)⌋ = j), (mult ρ : ℝ) ≤
      C3 * (2 * lam + 1) := by
  obtain ⟨C2, hC2, hloc⟩ := local_sum
  refine ⟨9 * C2, by positivity, ?_⟩
  intro T hT σ lam hlam hη10 hσ j
  set L := Real.log (T + 3) with hLdef
  have hL1 : 1 ≤ L := log_T3_ge hT
  have hL0 : 0 < L := by linarith
  set η := lam / L with hηdef
  have hη0 : 0 < η := div_pos (by linarith) hL0
  have hLη : 1 / L ≤ η := div_le_div_of_nonneg_right hlam hL0.le
  set γ : ℝ := (j : ℝ) / L with hγ
  set F := (zbox σ T).filter (fun ρ => ⌊ρ.im * L⌋ = j) with hF
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · rw [hFe, Finset.sum_empty]; positivity
  -- facts about elements of F
  have hfact : ∀ ρ ∈ F, Z ρ = 0 ∧ 1 - η ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧
      γ ≤ ρ.im ∧ ρ.im < γ + 1 / L := by
    intro ρ hρ
    rw [hF, Finset.mem_filter, mem_zbox] at hρ
    obtain ⟨⟨hZ, hre, him⟩, hj⟩ := hρ
    have f1 := Int.floor_le (ρ.im * L)
    have f2 := Int.lt_floor_add_one (ρ.im * L)
    rw [hj] at f1 f2
    refine ⟨hZ, by linarith, Z_re_lt_one hZ, him, ?_, ?_⟩
    · rw [hγ, div_le_iff₀ hL0]; exact f1
    · rw [hγ, ← add_div, lt_div_iff₀ hL0]; exact f2
  obtain ⟨ρ0, hρ0⟩ := hFne
  obtain ⟨-, -, -, h0T, h0a, h0b⟩ := hfact ρ0 hρ0
  have hγT : |γ| ≤ T + 1 := by
    rw [abs_le] at h0T ⊢
    constructor <;> nlinarith [hLη, hη0]
  have hlogγ : Real.log (|γ| + 3) ≤ 2 * L := by
    rw [hLdef, ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by positivity)
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [abs_nonneg γ]
  have hloc' := hloc γ η hη0 hη10
  -- per-zero estimate
  have hper : ∀ ρ ∈ F, (mult ρ : ℝ) ≤
      9 * η ^ 2 * ((mult ρ : ℝ) / ‖((1 + η : ℝ) : ℂ) + γ * I - ρ‖ ^ 2) := by
    intro ρ hρ
    obtain ⟨-, h1, h2, -, h4, h5⟩ := hfact ρ hρ
    set z := ((1 + η : ℝ) : ℂ) + γ * I - ρ with hz
    have hzre : z.re = 1 + η - ρ.re := by simp [hz]
    have hzim : z.im = γ - ρ.im := by simp [hz]
    have hpos : 0 < ‖z‖ := by
      have := Complex.abs_re_le_norm z
      rw [hzre, abs_of_pos (by linarith)] at this
      linarith
    have hle : ‖z‖ ≤ 3 * η := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [hzre, hzim, abs_of_pos (by linarith), abs_of_nonpos (by linarith)] at this
      linarith
    have hsq : ‖z‖ ^ 2 ≤ 9 * η ^ 2 := by nlinarith
    have hm : (0 : ℝ) ≤ mult ρ := by positivity
    calc (mult ρ : ℝ) = (mult ρ : ℝ) / ‖z‖ ^ 2 * ‖z‖ ^ 2 := by field_simp
      _ ≤ (mult ρ : ℝ) / ‖z‖ ^ 2 * (9 * η ^ 2) := by gcongr
      _ = 9 * η ^ 2 * ((mult ρ : ℝ) / ‖z‖ ^ 2) := by ring
  have hsub : F ⊆ zball (ctr γ) := by
    intro ρ hρ
    obtain ⟨hZ, h1, h2, -, h4, h5⟩ := hfact ρ hρ
    rw [mem_zball, Metric.mem_closedBall, Complex.dist_eq]
    refine ⟨hZ, ?_⟩
    have := Complex.norm_le_abs_re_add_abs_im (ρ - ctr γ)
    have hre : (ρ - ctr γ).re = ρ.re - 6 / 5 := by rw [Complex.sub_re, ctr_re]
    have him : (ρ - ctr γ).im = ρ.im - γ := by rw [Complex.sub_im, ctr_im]
    rw [hre, him, abs_of_neg (by linarith), abs_of_nonneg (by linarith)] at this
    have : η ≤ 1 / 10 := hη10
    linarith
  calc ∑ ρ ∈ F, (mult ρ : ℝ)
      ≤ ∑ ρ ∈ F, 9 * η ^ 2 * ((mult ρ : ℝ) / ‖((1 + η : ℝ) : ℂ) + γ * I - ρ‖ ^ 2) :=
        Finset.sum_le_sum hper
    _ = 9 * η ^ 2 * ∑ ρ ∈ F, (mult ρ : ℝ) / ‖((1 + η : ℝ) : ℂ) + γ * I - ρ‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 9 * η ^ 2 * ∑ u ∈ zball (ctr γ), (mult u : ℝ) / ‖((1 + η : ℝ) : ℂ) + γ * I - u‖ ^ 2 := by
        gcongr
    _ ≤ 9 * η ^ 2 * (C2 * (Real.log (|γ| + 3) + 1 / η) / η) := by gcongr
    _ = 9 * C2 * (η * Real.log (|γ| + 3) + 1) := by field_simp
    _ ≤ 9 * C2 * (2 * lam + 1) := by
        have h : η * Real.log (|γ| + 3) ≤ 2 * lam := by
          calc η * Real.log (|γ| + 3) ≤ η * (2 * L) := by gcongr
            _ = 2 * lam := by rw [hηdef]; field_simp
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Counting a well-spaced set of zero ordinates (e). -/
theorem count_P : ∃ κ1 : ℝ, 0 < κ1 ∧ ∃ c0 A0 : ℝ, 0 ≤ c0 ∧ ∀ T : ℝ, 3 ≤ T → ∀ lam : ℝ,
    1 ≤ lam → lam ≤ κ1 * Real.log (T + 3) → ∀ P : Finset ℝ,
    (∀ t ∈ P, ∃ ρ : ℂ, Z ρ = 0 ∧ 1 - lam / Real.log (T + 3) ≤ ρ.re ∧ ρ.im = t ∧
      1 < |t| ∧ |t| ≤ T) →
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → 1 / Real.log (T + 3) ≤ |t - t'|) →
    (P.card : ℝ) ≤ c0 * Real.exp (A0 * lam) := by
  obtain ⟨K0, A1, κ1, a, b, hK0, hκ1, ha, hab, hdet⟩ := detector
  obtain ⟨CM, hCM, hmv⟩ := mean_value
  have hb : 0 < b := by linarith
  refine ⟨κ1, hκ1, (2 * K0 + 3) * (2 * K0 + 2) ^ 2 * CM * b ^ 2, 3 + 2 * A1,
    by positivity, ?_⟩
  intro T hT lam hlam hlamκ P hP hsp
  set L := Real.log (T + 3) with hLdef
  have hL1 : 1 ≤ L := log_T3_ge hT
  have hL0 : 0 < L := by linarith
  have hlam0 : 0 < lam := by linarith
  set η := lam / L with hηdef
  have hη0 : 0 ≤ η := by positivity
  set m := ⌈K0 * lam⌉₊ with hm
  have hk : ∀ t ∈ P, ∃ k : ℕ, k ≤ 2 * m ∧
      (T + 3) ^ 10 ≤ (⌊Real.exp (a * k * L / lam)⌋₊ : ℝ) ∧
      Real.exp (-(A1 * lam)) * L ≤ lam *
        ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k * L / lam)⌋₊ ⌊Real.exp (b * k * L / lam)⌋₊,
          wt η k n * (n : ℂ) ^ (-((t : ℂ) * I))‖ := by
    intro t ht
    obtain ⟨ρ, hZ, hre, rfl, h1, h2⟩ := hP t ht
    exact hdet T hT lam hlam hlamκ ρ hZ hre h1 h2
  choose! kf hkf using hk
  -- fiber bound
  have hfib : ∀ k ∈ Finset.range (2 * m + 1),
      (((P.filter (fun t => kf t = k)).card : ℕ) : ℝ) ≤
        CM * (b * (2 * (m : ℝ))) ^ 2 * Real.exp (2 * A1 * lam) := by
    intro k hkr
    have hkm : (k : ℝ) ≤ 2 * (m : ℝ) := by
      have := Finset.mem_range.1 hkr
      exact_mod_cast (by omega : k ≤ 2 * m)
    set Q := P.filter (fun t => kf t = k) with hQ
    rcases Q.eq_empty_or_nonempty with hQe | ⟨t0, ht0⟩
    · rw [hQe, Finset.card_empty, Nat.cast_zero]; positivity
    have ht0' := Finset.mem_filter.1 ht0
    have h10 := (hkf t0 ht0'.1).2.1
    rw [ht0'.2] at h10
    have hQP : Q ⊆ P := Finset.filter_subset _ _
    have hmv' := hmv T hT _ ⌊Real.exp (b * k * L / lam)⌋₊ h10 (wt η k) (wt_norm_le hη0 k) Q
      (fun t ht => by
        obtain ⟨ρ, -, -, rfl, -, h2⟩ := hP t (hQP ht); exact h2)
      (fun t ht t' ht' hne => hsp t (hQP ht) t' (hQP ht') hne)
    set u := L / lam with hu
    have hu0 : 0 < u := div_pos hL0 hlam0
    set E := Real.exp (-(A1 * lam)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hlow : ∀ t ∈ Q, (E * u) ^ 2 ≤
        ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k * L / lam)⌋₊ ⌊Real.exp (b * k * L / lam)⌋₊,
          wt η k n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 := by
      intro t ht
      have ht' := Finset.mem_filter.1 ht
      have h3 := (hkf t ht'.1).2.2
      rw [ht'.2] at h3
      have : E * u ≤ ‖∑ n ∈ Finset.Ioc ⌊Real.exp (a * k * L / lam)⌋₊
          ⌊Real.exp (b * k * L / lam)⌋₊, wt η k n * (n : ℂ) ^ (-((t : ℂ) * I))‖ := by
        rw [hu, ← mul_div_assoc, div_le_iff₀ hlam0]; linarith
      gcongr
    have hsum := Finset.card_nsmul_le_sum Q _ _ hlow
    rw [nsmul_eq_mul] at hsum
    have hx0 : 0 ≤ b * k * L / lam := by positivity
    have hlogN := log_floor_exp_le hx0
    have hlogN0 := Real.log_natCast_nonneg ⌊Real.exp (b * k * L / lam)⌋₊
    have hbk : b * k * L / lam = b * k * u := by rw [hu]; ring
    have hlogN' : Real.log (⌊Real.exp (b * k * L / lam)⌋₊ : ℝ) ≤ b * k * u := by
      rw [← hbk]; exact hlogN
    have hlog2 : Real.log (⌊Real.exp (b * k * L / lam)⌋₊ : ℝ) ^ 2 ≤ (b * k * u) ^ 2 :=
      pow_le_pow_left₀ hlogN0 hlogN' 2
    have hmain : (Q.card : ℝ) * (E * u) ^ 2 ≤ CM * (b * k * u) ^ 2 := by
      calc (Q.card : ℝ) * (E * u) ^ 2 ≤ _ := hsum
        _ ≤ _ := hmv'
        _ ≤ CM * (b * k * u) ^ 2 := by gcongr
    have hmain2 : (Q.card : ℝ) * E ^ 2 ≤ CM * (b * k) ^ 2 := by
      have hu2 : 0 < u ^ 2 := by positivity
      have : (Q.card : ℝ) * E ^ 2 * u ^ 2 ≤ CM * (b * k) ^ 2 * u ^ 2 := by
        calc (Q.card : ℝ) * E ^ 2 * u ^ 2 = (Q.card : ℝ) * (E * u) ^ 2 := by ring
          _ ≤ CM * (b * k * u) ^ 2 := hmain
          _ = CM * (b * k) ^ 2 * u ^ 2 := by ring
      exact le_of_mul_le_mul_right this hu2
    have hEE : E ^ 2 * Real.exp (2 * A1 * lam) = 1 := by
      rw [hE, sq, ← Real.exp_add, ← Real.exp_add]; simp; ring_nf
    calc (Q.card : ℝ) = (Q.card : ℝ) * E ^ 2 * Real.exp (2 * A1 * lam) := by
          rw [mul_assoc, hEE, mul_one]
      _ ≤ CM * (b * k) ^ 2 * Real.exp (2 * A1 * lam) := by gcongr
      _ ≤ CM * (b * (2 * (m : ℝ))) ^ 2 * Real.exp (2 * A1 * lam) := by gcongr
  have hcard : (P.card : ℝ) = ∑ k ∈ Finset.range (2 * m + 1),
      (((P.filter (fun t => kf t = k)).card : ℕ) : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := kf) (t := Finset.range (2 * m + 1))]
    · push_cast; rfl
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio]
      have := (hkf t ht).1
      omega
  have hmle : (m : ℝ) ≤ K0 * lam + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hexp := Real.add_one_le_exp lam
  have he0 : 0 < Real.exp lam := Real.exp_pos _
  have hA : Real.exp ((3 + 2 * A1) * lam) =
      Real.exp lam * Real.exp lam * Real.exp lam * Real.exp (2 * A1 * lam) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hc1 : 2 * (m : ℝ) + 1 ≤ (2 * K0 + 3) * Real.exp lam := by nlinarith
  have hc2 : 2 * (m : ℝ) ≤ (2 * K0 + 2) * Real.exp lam := by nlinarith
  rw [hcard]
  calc ∑ k ∈ Finset.range (2 * m + 1), (((P.filter (fun t => kf t = k)).card : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.range (2 * m + 1),
          CM * (b * (2 * (m : ℝ))) ^ 2 * Real.exp (2 * A1 * lam) := Finset.sum_le_sum hfib
    _ = (2 * (m : ℝ) + 1) * (CM * (b * (2 * (m : ℝ))) ^ 2 * Real.exp (2 * A1 * lam)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((2 * K0 + 3) * Real.exp lam) *
          (CM * (b * ((2 * K0 + 2) * Real.exp lam)) ^ 2 * Real.exp (2 * A1 * lam)) := by
        gcongr
    _ = (2 * K0 + 3) * (2 * K0 + 2) ^ 2 * CM * b ^ 2 * Real.exp ((3 + 2 * A1) * lam) := by
        rw [hA]; ring

/-- Number of occupied windows (d)+(e). -/
theorem card_J : ∃ κ1 : ℝ, 0 < κ1 ∧ ∃ c0 A0 : ℝ, 0 ≤ c0 ∧ ∀ T : ℝ, 3 ≤ T → ∀ lam : ℝ,
    1 ≤ lam → lam ≤ κ1 * Real.log (T + 3) → ∀ σ : ℝ, 1 - lam / Real.log (T + 3) ≤ σ →
    (∀ ρ ∈ zbox σ T, 1 < |ρ.im|) →
    ((((zbox σ T).image (fun ρ => ⌊ρ.im * Real.log (T + 3)⌋)).card : ℕ) : ℝ) ≤
      2 * c0 * Real.exp (A0 * lam) := by
  obtain ⟨κ1, hκ1, c0, A0, hc0, hcount⟩ := count_P
  refine ⟨κ1, hκ1, c0, A0, hc0, ?_⟩
  intro T hT lam hlam hlamκ σ hσ him1
  set L := Real.log (T + 3) with hLdef
  have hL1 : 1 ≤ L := log_T3_ge hT
  have hL0 : 0 < L := by linarith
  set J := (zbox σ T).image (fun ρ => ⌊ρ.im * L⌋) with hJ
  have hex : ∀ j ∈ J, ∃ ρ ∈ zbox σ T, ⌊ρ.im * L⌋ = j := fun j hj => Finset.mem_image.1 hj
  choose! r hr using hex
  have key : ∀ p : ℤ → Prop, ∀ _ : DecidablePred p,
      (∀ j j' : ℤ, p j → p j' → j ≠ j' → 2 ≤ |j - j'|) →
      (((J.filter p).card : ℕ) : ℝ) ≤ c0 * Real.exp (A0 * lam) := by
    intro p _ hp
    have hinj : Set.InjOn (fun j => (r j).im) (J.filter p : Set ℤ) := by
      intro j hj j' hj' he
      have h1 := (hr j (Finset.mem_filter.1 hj).1).2
      have h2 := (hr j' (Finset.mem_filter.1 hj').1).2
      simp only at he
      rw [← h1, ← h2, he]
    rw [← Finset.card_image_of_injOn hinj]
    apply hcount T hT lam hlam hlamκ
    · intro t ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
      have hρ := (hr j (Finset.mem_filter.1 hj).1).1
      have hρ' := hρ
      rw [mem_zbox] at hρ'
      exact ⟨r j, hρ'.1, by linarith [hρ'.2.1], rfl, him1 _ hρ, hρ'.2.2⟩
    · intro t ht t' ht' hne
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 ht'
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      have h2 := hp j j' (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hj').2 hjj
      have e1 := (hr j (Finset.mem_filter.1 hj).1).2
      have e2 := (hr j' (Finset.mem_filter.1 hj').1).2
      have f1 := Int.floor_le ((r j).im * L)
      have f2 := Int.lt_floor_add_one ((r j).im * L)
      have f3 := Int.floor_le ((r j').im * L)
      have f4 := Int.lt_floor_add_one ((r j').im * L)
      rw [e1] at f1 f2
      rw [e2] at f3 f4
      have h2' : (2 : ℝ) ≤ |(j : ℝ) - j'| := by exact_mod_cast h2
      have h1 : 1 ≤ |(r j).im * L - (r j').im * L| := by
        rcases le_abs'.1 h2' with h | h
        · rw [abs_sub_comm]; exact le_abs.2 (Or.inl (by linarith))
        · exact le_abs.2 (Or.inl (by linarith))
      rw [div_le_iff₀ hL0]
      calc (1 : ℝ) ≤ |(r j).im * L - (r j').im * L| := h1
        _ = |(r j).im - (r j').im| * L := by rw [← sub_mul, abs_mul, abs_of_pos hL0]
  have hsep : ∀ q : Prop, ∀ j j' : ℤ, (Even j ↔ q) → (Even j' ↔ q) → j ≠ j' → 2 ≤ |j - j'| := by
    intro q j j' h1 h2 hne
    have hev : Even (j - j') := Int.even_sub.2 (by rw [h1, h2])
    obtain ⟨s, hs⟩ := hev
    rcases le_or_gt 0 (j - j') with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_neg h]; omega
  have k1 := key (fun j => Even j) inferInstance
    (fun j j' h1 h2 hne => hsep True j j' (iff_true_intro h1) (iff_true_intro h2) hne)
  have k2 := key (fun j => ¬ Even j) inferInstance
    (fun j j' h1 h2 hne => hsep False j j' (iff_false_intro h1) (iff_false_intro h2) hne)
  have hsplit := Finset.card_filter_add_card_filter_not (s := J) (fun j => Even j)
  rw [← hsplit]
  push_cast
  linarith

end HD2


theorem density : ∃ A C κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ T : ℝ, 3 ≤ T → ∀ σ : ℝ, 1 - κ ≤ σ →
    Ncount σ T ≤ C * T ^ (A * (1 - σ)) := by
  obtain ⟨κ1, hκ1, c0, A0, hc0, hJ⟩ := HD2.card_J
  obtain ⟨C3, hC3, hwin⟩ := HD2.window
  obtain ⟨η0, hη0, hzf⟩ := zero_free_low
  obtain ⟨C0, hC0⟩ := count_total'
  set κ := min (min κ1 (1 / 10)) (η0 / 2) with hκdef
  have hκ0 : 0 < κ := lt_min (lt_min hκ1 (by norm_num)) (by linarith)
  have hκ1' : κ ≤ κ1 := (min_le_left _ _).trans (min_le_left _ _)
  have hκ10 : κ ≤ 1 / 10 := (min_le_left _ _).trans (min_le_right _ _)
  have hκη : κ ≤ η0 / 2 := min_le_right _ _
  set L0 := max 2 (1 / κ) with hL0def
  set A2 := |A0| + 1 with hA2
  have hA2pos : 0 < A2 := by positivity
  set Cs := C0 * Real.exp L0 ^ 2 with hCs
  have hexpL0 : 3 ≤ Real.exp L0 := by
    have := Real.add_one_le_exp L0
    have : 2 ≤ L0 := le_max_left _ _
    linarith
  have hCs0 : 0 ≤ Cs := (HD2.Ncount_nonneg _ _).trans (hC0 _ hexpL0)
  set Cb := 6 * c0 * C3 * Real.exp A2 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨2 * A2, Cs + Cb, κ, by positivity, hκ0, ?_⟩
  intro T hT σ hσ
  have hT1 : 1 ≤ T := by linarith
  -- case σ > 1
  rcases lt_or_ge 1 σ with hσ1 | hσ1
  · rw [HD2.Ncount_eq_zero hσ1]
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ T) (2 * A2 * (1 - σ))
    positivity
  have hexp0 : 0 ≤ 2 * A2 * (1 - σ) := by
    have : 0 ≤ 1 - σ := by linarith
    positivity
  have hTpow : 1 ≤ T ^ (2 * A2 * (1 - σ)) := Real.one_le_rpow hT1 hexp0
  set L := Real.log (T + 3) with hLdef
  have hL1 : 1 ≤ L := HD2.log_T3_ge hT
  have hL0 : 0 < L := by linarith
  rcases lt_or_ge L L0 with hsmall | hbig
  · -- small T
    have hT3 : T + 3 < Real.exp L0 := by
      rw [← Real.log_lt_iff_lt_exp (by linarith)]; exact hsmall
    have h1 : Ncount σ T ≤ Ncount (7 / 10) (Real.exp L0) :=
      HD2.Ncount_mono (by linarith) (by linarith)
    have h2 := hC0 _ hexpL0
    calc Ncount σ T ≤ Cs := h1.trans h2
      _ ≤ Cs * T ^ (2 * A2 * (1 - σ)) := le_mul_of_one_le_right hCs0 hTpow
      _ ≤ (Cs + Cb) * T ^ (2 * A2 * (1 - σ)) := by gcongr; linarith
  -- large T
  have hLκ : 1 ≤ κ * L := by
    have : 1 / κ ≤ L := (le_max_right _ _).trans hbig
    rw [div_le_iff₀ hκ0] at this; linarith
  set lam := max 1 ((1 - σ) * L) with hlamdef
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlamκ : lam ≤ κ * L := max_le hLκ (by
    have : 1 - σ ≤ κ := by linarith
    nlinarith)
  have hlamκ1 : lam ≤ κ1 * L := hlamκ.trans (by nlinarith)
  have hη : lam / L ≤ κ := by rw [div_le_iff₀ hL0]; linarith
  have hη10 : lam / L ≤ 1 / 10 := hη.trans hκ10
  have hσ' : 1 - lam / L ≤ σ := by
    have : (1 - σ) * L ≤ lam := le_max_right _ _
    have : 1 - σ ≤ lam / L := by rw [le_div_iff₀ hL0]; exact this
    linarith
  have him1 : ∀ ρ ∈ zbox σ T, 1 < |ρ.im| := by
    intro ρ hρ
    rw [mem_zbox] at hρ
    by_contra h
    push Not at h
    have := hzf ρ hρ.1 h
    linarith [hρ.2.1]
  -- Ncount ≤ #J * HD2.window bound
  have hmaps : ∀ ρ ∈ zbox σ T, (fun ρ : ℂ => ⌊ρ.im * L⌋) ρ ∈
      (zbox σ T).image (fun ρ => ⌊ρ.im * L⌋) := fun ρ hρ => Finset.mem_image_of_mem _ hρ
  have hN : Ncount σ T ≤ ((((zbox σ T).image (fun ρ => ⌊ρ.im * L⌋)).card : ℕ) : ℝ) *
      (C3 * (2 * lam + 1)) := by
    unfold Ncount
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ j ∈ (zbox σ T).image (fun ρ => ⌊ρ.im * L⌋),
          ∑ ρ ∈ (zbox σ T).filter (fun ρ => ⌊ρ.im * L⌋ = j), (mult ρ : ℝ)
        ≤ ∑ j ∈ (zbox σ T).image (fun ρ => ⌊ρ.im * L⌋), C3 * (2 * lam + 1) :=
          Finset.sum_le_sum (fun j _ => hwin T hT σ lam hlam1 hη10 hσ' j)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hJb := hJ T hT lam hlam1 hlamκ1 σ hσ' him1
  have hexplam := Real.add_one_le_exp lam
  have hel : Real.exp (A0 * lam) * Real.exp lam ≤ Real.exp (A2 * lam) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have := le_abs_self A0
    nlinarith
  have hlamle : lam ≤ 1 + (1 - σ) * L := by
    apply max_le (by nlinarith) (by linarith)
  have hpow : Real.exp ((1 - σ) * L) ≤ T ^ (2 * (1 - σ)) := by
    rw [hLdef, mul_comm, ← Real.rpow_def_of_pos (by linarith)]
    have hT2 : T + 3 ≤ T ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc (T + 3) ^ (1 - σ) ≤ (T ^ (2 : ℝ)) ^ (1 - σ) :=
          Real.rpow_le_rpow (by linarith) hT2 (by linarith)
      _ = T ^ (2 * (1 - σ)) := by rw [← Real.rpow_mul (by linarith)]
  have hfin : Real.exp (A2 * lam) ≤ Real.exp A2 * T ^ (2 * A2 * (1 - σ)) := by
    calc Real.exp (A2 * lam) ≤ Real.exp (A2 * (1 + (1 - σ) * L)) :=
          Real.exp_le_exp.2 (by gcongr)
      _ = Real.exp A2 * Real.exp ((1 - σ) * L) ^ A2 := by
          rw [← Real.exp_mul, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp A2 * (T ^ (2 * (1 - σ))) ^ A2 := by gcongr
      _ = Real.exp A2 * T ^ (2 * A2 * (1 - σ)) := by
          rw [← Real.rpow_mul (by linarith)]; congr 2; ring
  have hTp0 : 0 ≤ T ^ (2 * A2 * (1 - σ)) := by positivity
  calc Ncount σ T ≤ _ := hN
    _ ≤ (2 * c0 * Real.exp (A0 * lam)) * (C3 * (2 * lam + 1)) := by
        gcongr
    _ ≤ (2 * c0 * Real.exp (A0 * lam)) * (C3 * (3 * Real.exp lam)) := by
        gcongr; linarith
    _ = 6 * c0 * C3 * (Real.exp (A0 * lam) * Real.exp lam) := by ring
    _ ≤ 6 * c0 * C3 * Real.exp (A2 * lam) := by gcongr
    _ ≤ 6 * c0 * C3 * (Real.exp A2 * T ^ (2 * A2 * (1 - σ))) := by gcongr
    _ = Cb * T ^ (2 * A2 * (1 - σ)) := by rw [hCb]; ring
    _ ≤ (Cs + Cb) * T ^ (2 * A2 * (1 - σ)) := by gcongr; linarith



-- ===== from EB.lean =====


namespace EB

/-! ### Avoidance (pigeonhole) -/

theorem avoid (S : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ y, a ≤ y ∧ y ≤ b ∧ ∀ s ∈ S, (b - a) / (2 * ((S.card : ℝ) + 1)) ≤ |y - s| := by
  set n := S.card with hn
  set d := (b - a) / (2 * ((n : ℝ) + 1)) with hd
  have hn0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hd0 : 0 < d := div_pos (by linarith) hn0
  have hdn : 2 * ((n : ℝ) + 1) * d = b - a := by rw [hd]; field_simp
  let y : ℕ → ℝ := fun j => a + (2 * (j : ℝ) + 1) * d
  set B := (Finset.range (n + 1)).filter (fun j => ∃ s ∈ S, |y j - s| < d) with hB
  have hBsub : B ⊆ S.biUnion (fun s => (Finset.range (n + 1)).filter (fun j => |y j - s| < d)) := by
    intro j hj
    rw [hB, Finset.mem_filter] at hj
    obtain ⟨hj, s, hs, hjs⟩ := hj
    exact Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_filter.2 ⟨hj, hjs⟩⟩
  have hcard1 : ∀ s ∈ S,
      ((Finset.range (n + 1)).filter (fun j => |y j - s| < d)).card ≤ 1 := by
    intro s _
    apply Finset.card_le_one.2
    intro i hi j hj
    rw [Finset.mem_filter] at hi hj
    have h1 := hi.2
    have h2 := hj.2
    have h3 : |y i - y j| < 2 * d := by
      calc |y i - y j| = |(y i - s) - (y j - s)| := by ring_nf
        _ ≤ |y i - s| + |y j - s| := abs_sub _ _
        _ < 2 * d := by linarith
    have hyij : y i - y j = 2 * d * ((i : ℝ) - j) := by simp only [y]; ring
    rw [hyij, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * d)] at h3
    by_contra hne
    have hz : ((i : ℤ) - j) ≠ 0 := by omega
    have h4 : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      have := Int.one_le_abs hz
      exact_mod_cast this
    nlinarith
  have hBcard : B.card ≤ n := by
    calc B.card ≤ (S.biUnion (fun s => (Finset.range (n + 1)).filter
          (fun j => |y j - s| < d))).card := Finset.card_le_card hBsub
      _ ≤ ∑ s ∈ S, ((Finset.range (n + 1)).filter (fun j => |y j - s| < d)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S, 1 := Finset.sum_le_sum hcard1
      _ = n := by simp [hn]
  have hlt : B.card < (Finset.range (n + 1)).card := by rw [Finset.card_range]; omega
  obtain ⟨j, hj, hjB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hjn : (j : ℝ) ≤ n := by
    have := Finset.mem_range.1 hj
    exact_mod_cast Nat.lt_succ_iff.1 this
  refine ⟨y j, ?_, ?_, ?_⟩
  · simp only [y]; have : (0 : ℝ) ≤ (2 * (j : ℝ) + 1) * d := by positivity
    linarith
  · simp only [y]
    have : (2 * (j : ℝ) + 1) * d ≤ 2 * ((n : ℝ) + 1) * d := by
      apply mul_le_mul_of_nonneg_right _ hd0.le; linarith
    linarith
  · intro s hs
    by_contra hlt'
    push Not at hlt'
    exact hjB (Finset.mem_filter.2 ⟨hj, s, hs, hlt'⟩)

/-! ### Counting -/

theorem card_le_sum_mult (F : Finset ℂ) (hF : ∀ u ∈ F, Z u = 0) :
    (F.card : ℝ) ≤ ∑ u ∈ F, (mult u : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro u hu
  have := mult_pos (hF u hu)
  simp only [Nat.cast_one]
  exact_mod_cast this

theorem cover {u : ℂ} (hu : Z u = 0) (hre : 7 / 10 ≤ u.re) (t0 : ℝ) (h1 : t0 ≤ u.im)
    (h2 : u.im ≤ t0 + 3) : ∃ k ∈ Finset.range 16, u ∈ zball (ctr (t0 + k / 5)) := by
  have hlt := Z_re_lt_one hu
  set k := ⌊5 * (u.im - t0) + 1 / 2⌋₊ with hk
  have hk0 : 0 ≤ 5 * (u.im - t0) + 1 / 2 := by linarith
  have hk1 := Nat.floor_le hk0
  have hk2 := Nat.lt_floor_add_one (5 * (u.im - t0) + 1 / 2)
  rw [← hk] at hk1 hk2
  refine ⟨k, ?_, mem_zball.2 ⟨hu, ?_⟩⟩
  · rw [Finset.mem_range]
    have : (k : ℝ) < 16 := by linarith
    exact_mod_cast this
  · rw [mem_closedBall, dist_eq_norm]
    have e : ‖u - ctr (t0 + k / 5)‖ ^ 2 = (u.re - 6 / 5) ^ 2 + (u.im - (t0 + k / 5)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [ctr]; ring
    have h3 : ‖u - ctr (t0 + k / 5)‖ ^ 2 ≤ (11 / 20) ^ 2 := by
      rw [e]; nlinarith
    nlinarith [norm_nonneg (u - ctr (t0 + k / 5))]

/-- Zeros with `Re ≥ 7/10` and `T - 1 ≤ |Im| ≤ T + 2`. -/
def G (T : ℝ) : Finset ℂ := (zbox (7 / 10) (T + 2)).filter (fun u => T - 1 ≤ |u.im|)

theorem card_zball_le {CL : ℝ}
    (hL : ∀ t : ℝ, ∑ u ∈ zball (ctr t), (mult u : ℝ) ≤ CL * Real.log (|t| + 3)) (hCL : 0 < CL)
    {t T : ℝ} (ht : |t| ≤ T + 2) : ((zball (ctr t)).card : ℝ) ≤ CL * Real.log (T + 5) := by
  calc ((zball (ctr t)).card : ℝ) ≤ ∑ u ∈ zball (ctr t), (mult u : ℝ) :=
        card_le_sum_mult _ (fun u hu => (mem_zball.1 hu).1)
    _ ≤ CL * Real.log (|t| + 3) := hL t
    _ ≤ CL * Real.log (T + 5) := by
        apply mul_le_mul_of_nonneg_left _ hCL.le
        apply Real.log_le_log (by positivity) (by linarith)

theorem card_G {CL : ℝ}
    (hL : ∀ t : ℝ, ∑ u ∈ zball (ctr t), (mult u : ℝ) ≤ CL * Real.log (|t| + 3)) (hCL : 0 < CL)
    {T : ℝ} (hT : 3 ≤ T) : ((G T).card : ℝ) ≤ 32 * CL * Real.log (T + 5) := by
  classical
  have hsub : G T ⊆ (Finset.range 16).biUnion
      (fun k : ℕ => zball (ctr (T - 1 + k / 5)) ∪ zball (ctr (-(T + 2) + k / 5))) := by
    intro u hu
    rw [G, Finset.mem_filter, mem_zbox] at hu
    obtain ⟨⟨hZ, hre, him⟩, him'⟩ := hu
    rw [Finset.mem_biUnion]
    rcases le_or_gt 0 u.im with h0 | h0
    · rw [abs_of_nonneg h0] at him him'
      obtain ⟨k, hk, hk'⟩ := cover hZ hre (T - 1) him' (by linarith)
      exact ⟨k, hk, Finset.mem_union_left _ hk'⟩
    · rw [abs_of_neg h0] at him him'
      obtain ⟨k, hk, hk'⟩ := cover hZ hre (-(T + 2)) (by linarith) (by linarith)
      exact ⟨k, hk, Finset.mem_union_right _ hk'⟩
  have hk : ∀ k ∈ Finset.range 16, (((zball (ctr (T - 1 + k / 5)) ∪
      zball (ctr (-(T + 2) + k / 5))).card : ℕ) : ℝ) ≤ 2 * (CL * Real.log (T + 5)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ 15 := by
      have := Finset.mem_range.1 hk
      exact_mod_cast Nat.lt_succ_iff.1 this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have a1 := card_zball_le hL hCL (t := T - 1 + k / 5) (T := T)
      (by rw [abs_le]; constructor <;> linarith)
    have a2 := card_zball_le hL hCL (t := -(T + 2) + k / 5) (T := T)
      (by rw [abs_le]; constructor <;> linarith)
    have := Finset.card_union_le (zball (ctr (T - 1 + k / 5))) (zball (ctr (-(T + 2) + k / 5)))
    have : (((zball (ctr (T - 1 + k / 5)) ∪ zball (ctr (-(T + 2) + k / 5))).card : ℕ) : ℝ) ≤
        ((zball (ctr (T - 1 + k / 5))).card : ℝ) + ((zball (ctr (-(T + 2) + k / 5))).card : ℝ) := by
      exact_mod_cast this
    linarith
  calc ((G T).card : ℝ) ≤ (((Finset.range 16).biUnion
      (fun k : ℕ => zball (ctr (T - 1 + k / 5)) ∪ zball (ctr (-(T + 2) + k / 5)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ k ∈ Finset.range 16, ((zball (ctr (T - 1 + k / 5)) ∪
          zball (ctr (-(T + 2) + k / 5))).card) : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range 16, (((zball (ctr (T - 1 + k / 5)) ∪
          zball (ctr (-(T + 2) + k / 5))).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ k ∈ Finset.range 16, 2 * (CL * Real.log (T + 5)) := Finset.sum_le_sum hk
    _ = 32 * CL * Real.log (T + 5) := by simp; ring

/-! ### Pointwise bounds for `Z'/Z` and `Lf` -/

theorem dlog_bound {CL : ℝ} (hland : ∀ t : ℝ,
    (∑ u ∈ zball (ctr t), (mult u : ℝ)) ≤ CL * Real.log (|t| + 3) ∧
    ∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → Z s ≠ 0 →
      ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤
        CL * Real.log (|t| + 3))
    {t : ℝ} {s : ℂ} (hs : ‖s - ctr t‖ ≤ 1 / 2) (hZ : Z s ≠ 0) {e : ℝ} (he : 0 < e)
    (hdist : ∀ u ∈ zball (ctr t), e ≤ ‖s - u‖) :
    ‖deriv Z s / Z s‖ ≤ CL * Real.log (|t| + 3) * (1 / e + 1) := by
  have h1 := (hland t).2 s hs hZ
  have h2 := (hland t).1
  have h3 : ‖∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤ CL * Real.log (|t| + 3) / e := by
    calc ‖∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖
        ≤ ∑ u ∈ zball (ctr t), ‖(mult u : ℂ) / (s - u)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ zball (ctr t), (mult u : ℝ) / e := by
          apply Finset.sum_le_sum
          intro u hu
          rw [norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) he (hdist u hu)
      _ = (∑ u ∈ zball (ctr t), (mult u : ℝ)) / e := by rw [Finset.sum_div]
      _ ≤ CL * Real.log (|t| + 3) / e := div_le_div_of_nonneg_right h2 he.le
  calc ‖deriv Z s / Z s‖
      = ‖(deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)) +
          ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ := by rw [sub_add_cancel]
    _ ≤ ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ +
          ‖∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ := norm_add_le _ _
    _ ≤ CL * Real.log (|t| + 3) + CL * Real.log (|t| + 3) / e := add_le_add h1 h3
    _ = CL * Real.log (|t| + 3) * (1 / e + 1) := by ring

theorem Lf_norm_le (s : ℂ) : ‖Lf s‖ ≤ ‖deriv Z s / Z s‖ + 1 / ‖s - 1‖ := by
  unfold Lf
  calc ‖-deriv Z s / Z s + 1 / (s - 1)‖ ≤ ‖-deriv Z s / Z s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
    _ = ‖deriv Z s / Z s‖ + 1 / ‖s - 1‖ := by rw [neg_div, norm_neg, one_div, one_div, norm_inv]

theorem min_pos' {d : ℝ} (hd : 0 < d) : 0 < min d (1 / 50) := lt_min hd (by norm_num)

theorem inv_min_le {d : ℝ} (hd : 0 < d) : 1 / min d (1 / 50) ≤ 1 / d + 50 := by
  rcases min_choice d (1 / 50) with h | h <;> rw [h]
  · have : 0 < 1 / d := by positivity
    linarith
  · have : 0 < 1 / d := by positivity
    norm_num; linarith

theorem Lf_left {CL : ℝ} (hland : ∀ t : ℝ,
    (∑ u ∈ zball (ctr t), (mult u : ℝ)) ≤ CL * Real.log (|t| + 3) ∧
    ∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → Z s ≠ 0 →
      ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤
        CL * Real.log (|t| + 3)) (hCL : 0 < CL)
    {T σ1 d1 : ℝ} (hT : 3 ≤ T) (hσ1 : 18 / 25 ≤ σ1) (hσ1' : σ1 ≤ 3 / 4) (hd1 : 0 < d1)
    (hav : ∀ u ∈ zbox (7 / 10) (T + 2), d1 ≤ |σ1 - u.re|) {t : ℝ} (ht : |t| ≤ T + 1) :
    ‖Lf (σ1 + t * I)‖ ≤ CL * Real.log (T + 4) * (1 / min d1 (1 / 50) + 1) + 4 := by
  set s : ℂ := σ1 + t * I with hs
  have sre : s.re = σ1 := by simp [hs]
  have sim : s.im = t := by simp [hs]
  have hZ : Z s ≠ 0 := by
    intro h
    have := hav s (mem_zbox.2 ⟨h, by rw [sre]; linarith, by rw [sim]; linarith⟩)
    rw [sre, sub_self, abs_zero] at this
    linarith
  have hctr : ‖s - ctr t‖ ≤ 1 / 2 := by
    have : s - ctr t = ((σ1 - 6 / 5 : ℝ) : ℂ) := by simp [hs, ctr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hdist : ∀ u ∈ zball (ctr t), min d1 (1 / 50) ≤ ‖s - u‖ := by
    intro u hu
    obtain ⟨hZu, hu⟩ := mem_zball.1 hu
    rw [mem_closedBall, dist_eq_norm] at hu
    have hre1 := Complex.abs_re_le_norm (s - u)
    rw [Complex.sub_re, sre] at hre1
    by_cases h7 : 7 / 10 ≤ u.re
    · have him := Complex.abs_im_le_norm (u - ctr t)
      rw [Complex.sub_im, ctr_im] at him
      have him2 : |u.im| ≤ T + 2 := by
        rw [abs_le] at ht him ⊢; constructor <;> linarith
      have := hav u (mem_zbox.2 ⟨hZu, h7, him2⟩)
      exact (min_le_left _ _).trans (this.trans hre1)
    · push Not at h7
      have : (1 / 50 : ℝ) ≤ |σ1 - u.re| := by
        rw [abs_of_pos (by linarith)]; linarith
      exact (min_le_right _ _).trans (this.trans hre1)
  have h1 := dlog_bound hland hctr hZ (min_pos' hd1) hdist
  have hlog : Real.log (|t| + 3) ≤ Real.log (T + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpos : 0 ≤ 1 / min d1 (1 / 50) + 1 := by have := min_pos' hd1; positivity
  have h2 : CL * Real.log (|t| + 3) * (1 / min d1 (1 / 50) + 1) ≤
      CL * Real.log (T + 4) * (1 / min d1 (1 / 50) + 1) := by
    apply mul_le_mul_of_nonneg_right _ hpos
    exact mul_le_mul_of_nonneg_left hlog hCL.le
  have h3 : 1 / ‖s - 1‖ ≤ 4 := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, sre, Complex.one_re, abs_of_neg (by linarith)] at this
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith [Lf_norm_le s]

theorem Lf_horiz {CL : ℝ} (hland : ∀ t : ℝ,
    (∑ u ∈ zball (ctr t), (mult u : ℝ)) ≤ CL * Real.log (|t| + 3) ∧
    ∀ s : ℂ, ‖s - ctr t‖ ≤ 1 / 2 → Z s ≠ 0 →
      ‖deriv Z s / Z s - ∑ u ∈ zball (ctr t), (mult u : ℂ) / (s - u)‖ ≤
        CL * Real.log (|t| + 3)) (hCL : 0 < CL)
    {T T' σ1 d2 σ : ℝ} (hT : 3 ≤ T) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1) (hσ1 : 18 / 25 ≤ σ1)
    (hσ : σ1 ≤ σ) (hσ' : σ ≤ 11 / 10) (hd2 : 0 < d2)
    (hav : ∀ u ∈ G T, d2 ≤ |T' - u.im| ∧ d2 ≤ |T' + u.im|) {τ : ℝ} (hτ : τ = T' ∨ τ = -T') :
    ‖Lf (σ + τ * I)‖ ≤ CL * Real.log (T + 4) * (1 / min d2 (1 / 50) + 1) + 1 := by
  set s : ℂ := σ + τ * I with hs
  have sre : s.re = σ := by simp [hs]
  have sim : s.im = τ := by simp [hs]
  have habs : |τ| = T' := by
    rcases hτ with h | h <;> rw [h] <;> simp [abs_of_pos (by linarith : (0:ℝ) < T')]
  have hkey : ∀ u ∈ G T, d2 ≤ |τ - u.im| := by
    intro u hu
    rcases hτ with h | h
    · rw [h]; exact (hav u hu).1
    · rw [h, show -T' - u.im = -(T' + u.im) by ring, abs_neg]; exact (hav u hu).2
  have hZ : Z s ≠ 0 := by
    intro h
    have hG : s ∈ G T := by
      rw [G, Finset.mem_filter, mem_zbox, sim, habs]
      exact ⟨⟨h, by rw [sre]; linarith, by linarith⟩, by linarith⟩
    have := hkey s hG
    rw [sim, sub_self, abs_zero] at this
    linarith
  have hctr : ‖s - ctr τ‖ ≤ 1 / 2 := by
    have : s - ctr τ = ((σ - 6 / 5 : ℝ) : ℂ) := by simp [hs, ctr]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hdist : ∀ u ∈ zball (ctr τ), min d2 (1 / 50) ≤ ‖s - u‖ := by
    intro u hu
    obtain ⟨hZu, hu⟩ := mem_zball.1 hu
    rw [mem_closedBall, dist_eq_norm] at hu
    by_cases h7 : 7 / 10 ≤ u.re
    · have him := Complex.abs_im_le_norm (u - ctr τ)
      rw [Complex.sub_im, ctr_im] at him
      have him1 : |u.im| ≤ T + 2 := by
        have := abs_sub_abs_le_abs_sub u.im τ
        rw [habs] at this; linarith
      have him2 : T - 1 ≤ |u.im| := by
        have := abs_sub_abs_le_abs_sub τ u.im
        rw [habs, abs_sub_comm] at this; linarith
      have hG : u ∈ G T := by
        rw [G, Finset.mem_filter, mem_zbox]; exact ⟨⟨hZu, h7, him1⟩, him2⟩
      have him3 := Complex.abs_im_le_norm (s - u)
      rw [Complex.sub_im, sim] at him3
      exact (min_le_left _ _).trans ((hkey u hG).trans him3)
    · push Not at h7
      have hre1 := Complex.abs_re_le_norm (s - u)
      rw [Complex.sub_re, sre] at hre1
      have : (1 / 50 : ℝ) ≤ |σ - u.re| := by
        rw [abs_of_pos (by linarith)]; linarith
      exact (min_le_right _ _).trans (this.trans hre1)
  have h1 := dlog_bound hland hctr hZ (min_pos' hd2) hdist
  have hlog : Real.log (|τ| + 3) ≤ Real.log (T + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpos : 0 ≤ 1 / min d2 (1 / 50) + 1 := by have := min_pos' hd2; positivity
  have h2 : CL * Real.log (|τ| + 3) * (1 / min d2 (1 / 50) + 1) ≤
      CL * Real.log (T + 4) * (1 / min d2 (1 / 50) + 1) := by
    apply mul_le_mul_of_nonneg_right _ hpos
    exact mul_le_mul_of_nonneg_left hlog hCL.le
  have h3 : 1 / ‖s - 1‖ ≤ 1 := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, sim, Complex.one_im, sub_zero, habs] at this
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith [Lf_norm_le s]

/-! ### Bounds for the Mellin weight `Wk` -/

theorem norm4 (a b c d : ℂ) : ‖a - b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a - b - c) d
  have h2 := norm_sub_le (a - b) c
  have h3 := norm_sub_le a b
  linarith

theorem Wk_norm_le {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Wk x δ s‖ ≤ 4 * (x * (1 + δ) ^ 4) ^ s.re / ‖s‖ ^ 2 := by
  have h1 : (1 : ℝ) ≤ 1 + δ := by linarith
  have p4 : 1 ≤ (1 + δ) ^ 4 := one_le_pow₀ h1
  have e0 : x ≤ x * (1 + δ) ^ 4 := le_mul_of_one_le_right hx.le p4
  have e1 : x * (1 + δ) ≤ x * (1 + δ) ^ 4 := by
    apply mul_le_mul_of_nonneg_left _ hx.le
    calc 1 + δ = (1 + δ) ^ 1 := (pow_one _).symm
      _ ≤ (1 + δ) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  have e3 : x * (1 + δ) ^ 3 ≤ x * (1 + δ) ^ 4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by norm_num)) hx.le
  have key : ∀ r : ℝ, 0 < r → r ≤ x * (1 + δ) ^ 4 →
      ‖((r : ℝ) : ℂ) ^ s‖ ≤ (x * (1 + δ) ^ 4) ^ s.re := by
    intro r hr hle
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    exact Real.rpow_le_rpow hr.le hle hs
  have hpos1 : 0 < x * (1 + δ) := by positivity
  have hpos3 : 0 < x * (1 + δ) ^ 3 := by positivity
  have hpos4 : 0 < x * (1 + δ) ^ 4 := by positivity
  unfold Wk
  rw [norm_div, norm_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have k4 := key _ hpos4 le_rfl
  have k3 := key _ hpos3 e3
  have k1 := key _ hpos1 e1
  have k0 := key _ hx e0
  linarith [norm4 (((x * (1 + δ) ^ 4 : ℝ) : ℂ) ^ s) (((x * (1 + δ) ^ 3 : ℝ) : ℂ) ^ s)
    (((x * (1 + δ) : ℝ) : ℂ) ^ s) (((x : ℝ) : ℂ) ^ s)]

theorem x3_le {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10) :
    x * (1 + δ) ^ 4 ≤ 2 * x := by
  have h : (1 + δ) ^ 4 ≤ (11 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have := mul_le_mul_of_nonneg_left h hx
  nlinarith

theorem x3_rpow_left {x δ σ : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10) (hσ : 0 ≤ σ)
    (hσ' : σ ≤ 3 / 4) : (x * (1 + δ) ^ 4) ^ σ ≤ 2 * x ^ ((3 : ℝ) / 4) := by
  have hx0 : 0 ≤ x := by linarith
  have h3 := x3_le hx0 hδ hδ'
  calc (x * (1 + δ) ^ 4) ^ σ ≤ (2 * x) ^ σ := Real.rpow_le_rpow (by positivity) h3 hσ
    _ ≤ (2 * x) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ'
    _ = 2 ^ ((3 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) := Real.mul_rpow (by norm_num) hx0
    _ ≤ 2 * x ^ ((3 : ℝ) / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2

theorem log_ge_ten {x : ℝ} (hx : Real.exp 10 ≤ x) : 10 ≤ Real.log x := by
  have := Real.log_le_log (Real.exp_pos 10) hx
  rwa [Real.log_exp] at this

theorem two_le_of_exp {x : ℝ} (hx : Real.exp 10 ≤ x) : 2 ≤ x := by
  have := Real.add_one_le_exp 10
  linarith

theorem x3_rpow_horiz {x δ σ : ℝ} (hx : Real.exp 10 ≤ x) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1 + 1 / Real.log x) : (x * (1 + δ) ^ 4) ^ σ ≤ 16 * x := by
  have hx2 := two_le_of_exp hx
  have hx0 : 0 < x := by linarith
  have hlog := log_ge_ten hx
  have hlpos : 0 < Real.log x := by linarith
  have hlne : Real.log x ≠ 0 := hlpos.ne'
  have h3 := x3_le hx0.le hδ hδ'
  have h3' : 0 ≤ x * (1 + δ) ^ 4 := by positivity
  have hexp : Real.exp 2 ≤ 8 := by
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  have hpow : (x ^ 2) ^ (1 / Real.log x) = Real.exp 2 := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    push_cast
    field_simp
  calc (x * (1 + δ) ^ 4) ^ σ ≤ (2 * x) ^ σ := Real.rpow_le_rpow h3' h3 hσ
    _ ≤ (2 * x) ^ (1 + 1 / Real.log x) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ'
    _ = (2 * x) * (2 * x) ^ (1 / Real.log x) := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]
    _ ≤ (2 * x) * (x ^ 2) ^ (1 / Real.log x) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact Real.rpow_le_rpow (by linarith) (by nlinarith) (by positivity)
    _ = (2 * x) * Real.exp 2 := by rw [hpow]
    _ ≤ 16 * x := by nlinarith

/-! ### Edge integrals -/

theorem left_int {x δ σ1 T' L : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 10)
    (hσ1 : 18 / 25 ≤ σ1) (hσ1' : σ1 ≤ 3 / 4) (hT' : 0 ≤ T') (hL : 0 ≤ L)
    (hLf : ∀ y : ℝ, |y| ≤ T' → ‖Lf (σ1 + y * I)‖ ≤ L) :
    ‖∫ y : ℝ in (-T')..T', Wk x δ (σ1 + y * I) * Lf (σ1 + y * I)‖ ≤
      45 * x ^ ((3 : ℝ) / 4) * L := by
  have hσ0 : 0 < σ1 := by linarith
  have hx0 : 0 ≤ x := by linarith
  set K := 8 * x ^ ((3 : ℝ) / 4) * L with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ y : ℝ, |y| ≤ T' → ‖Wk x δ (σ1 + y * I) * Lf (σ1 + y * I)‖ ≤
      K / σ1 * (σ1 / (y ^ 2 + σ1 ^ 2)) := by
    intro y hy
    have hre : ((σ1 : ℂ) + y * I).re = σ1 := by simp
    have hn : ‖(σ1 : ℂ) + y * I‖ ^ 2 = y ^ 2 + σ1 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hW := Wk_norm_le (x := x) (δ := δ) (by linarith) hδ.le (s := σ1 + y * I)
      (by rw [hre]; linarith)
    rw [hre, hn] at hW
    have hx3 := x3_rpow_left hx hδ.le hδ' hσ0.le hσ1'
    have hpos : 0 < y ^ 2 + σ1 ^ 2 := by positivity
    rw [norm_mul]
    calc ‖Wk x δ (σ1 + y * I)‖ * ‖Lf (σ1 + y * I)‖
        ≤ (8 * x ^ ((3 : ℝ) / 4) / (y ^ 2 + σ1 ^ 2)) * L := by
          apply mul_le_mul _ (hLf y hy) (norm_nonneg _) (by positivity)
          calc _ ≤ 4 * (x * (1 + δ) ^ 4) ^ σ1 / (y ^ 2 + σ1 ^ 2) := hW
            _ ≤ 4 * (2 * x ^ ((3 : ℝ) / 4)) / (y ^ 2 + σ1 ^ 2) := by gcongr
            _ = _ := by ring
      _ = K / σ1 * (σ1 / (y ^ 2 + σ1 ^ 2)) := by rw [hK]; field_simp
  have hint : ∫ y : ℝ in (-T')..T', K / σ1 * (σ1 / (y ^ 2 + σ1 ^ 2)) =
      K / σ1 * (2 * Real.arctan (T' / σ1)) := by
    rw [intervalIntegral.integral_const_mul, integral_b_div_sq_add_sq hσ0]
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (g := fun y : ℝ => K / σ1 * (σ1 / (y ^ 2 + σ1 ^ 2))) (by linarith : -T' ≤ T')
    (Filter.Eventually.of_forall (fun y hy => hpt y (by rw [abs_le]; exact ⟨hy.1.le, hy.2⟩)))
    (by
      apply Continuous.intervalIntegrable
      apply Continuous.mul continuous_const
      apply Continuous.div continuous_const (by fun_prop)
      intro y; positivity)
  beta_reduce at hle
  rw [hint] at hle
  have harc := Real.arctan_lt_pi_div_two (T' / σ1)
  have hpi := Real.pi_le_four
  have hXL : 0 ≤ x ^ ((3 : ℝ) / 4) * L := by positivity
  calc _ ≤ K / σ1 * (2 * Real.arctan (T' / σ1)) := hle
    _ ≤ K / σ1 * 4 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ ≤ 45 * x ^ ((3 : ℝ) / 4) * L := by
        rw [hK, div_mul_eq_mul_div, div_le_iff₀ hσ0]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 45 * σ1 - 32) hXL]

theorem horiz_int {x δ σ1 τ T Lh : ℝ} (hx : Real.exp 10 ≤ x) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 10)
    (hσ1 : 18 / 25 ≤ σ1) (hσ1' : σ1 ≤ 3 / 4) (hT : 3 ≤ T) (hτ : T ≤ |τ|) (hL : 0 ≤ Lh)
    (hLf : ∀ σ : ℝ, σ1 ≤ σ → σ ≤ 1 + 1 / Real.log x → ‖Lf (σ + τ * I)‖ ≤ Lh) :
    ‖∫ σ : ℝ in σ1..(1 + 1 / Real.log x), Wk x δ (σ + τ * I) * Lf (σ + τ * I)‖ ≤
      64 * x * Lh / T ^ 2 := by
  have hlog := log_ge_ten hx
  have hx0 : 0 < x := by linarith [two_le_of_exp hx]
  have hinv : 0 < 1 / Real.log x := by positivity
  have hinv' : 1 / Real.log x ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hc1 : σ1 ≤ 1 + 1 / Real.log x := by linarith
  have hT0 : 0 < T := by linarith
  have hpt : ∀ σ ∈ Ι σ1 (1 + 1 / Real.log x),
      ‖Wk x δ (σ + τ * I) * Lf (σ + τ * I)‖ ≤ 64 * x * Lh / T ^ 2 := by
    intro σ hσ
    rw [Set.uIoc_of_le hc1] at hσ
    have hre : ((σ : ℂ) + τ * I).re = σ := by simp
    have him : ((σ : ℂ) + τ * I).im = τ := by simp
    have hn : T ^ 2 ≤ ‖(σ : ℂ) + τ * I‖ ^ 2 := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + τ * I)
      rw [him] at this
      exact pow_le_pow_left₀ hT0.le (hτ.trans this) 2
    have hW := Wk_norm_le hx0 hδ.le (s := σ + τ * I) (by rw [hre]; linarith [hσ.1])
    rw [hre] at hW
    have hx3 := x3_rpow_horiz hx hδ.le hδ' (σ := σ) (by linarith [hσ.1]) hσ.2
    have hx3' : 0 ≤ (x * (1 + δ) ^ 4) ^ σ := by positivity
    rw [norm_mul]
    calc ‖Wk x δ (σ + τ * I)‖ * ‖Lf (σ + τ * I)‖ ≤ (64 * x / T ^ 2) * Lh := by
          apply mul_le_mul _ (hLf σ hσ.1.le hσ.2) (norm_nonneg _) (by positivity)
          calc _ ≤ 4 * (x * (1 + δ) ^ 4) ^ σ / ‖(σ : ℂ) + τ * I‖ ^ 2 := hW
            _ ≤ 4 * (16 * x) / T ^ 2 := by gcongr
            _ = 64 * x / T ^ 2 := by ring
      _ = _ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have habs : |1 + 1 / Real.log x - σ1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc _ ≤ 64 * x * Lh / T ^ 2 * |1 + 1 / Real.log x - σ1| := this
    _ ≤ 64 * x * Lh / T ^ 2 * 1 := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := mul_one _

/-! ### Residue bookkeeping -/

theorem Wk_diffOn {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) :
    DifferentiableOn ℂ (Wk x δ) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hc : ∀ r : ℝ, 0 < r → DifferentiableAt ℂ (fun s : ℂ => ((r : ℝ) : ℂ) ^ s) s :=
    fun r hr => differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hr.ne'))
  apply DifferentiableAt.differentiableWithinAt
  have h1 : 0 < x * (1 + δ) := by positivity
  have h3 : 0 < x * (1 + δ) ^ 3 := by positivity
  have h4 : 0 < x * (1 + δ) ^ 4 := by positivity
  exact ((((hc _ h4).sub (hc _ h3)).sub (hc _ h1)).add (hc _ hx)).div
    (differentiableAt_id.pow 2) (pow_ne_zero 2 hs0)

theorem Wk_one (x δ : ℝ) : Wk x δ 1 = ((δ * x * ((1 + δ) ^ 3 - 1) : ℝ) : ℂ) := by
  unfold Wk
  simp only [Complex.cpow_one, one_pow, div_one]
  push_cast
  ring

theorem sum_W_le {x δ σ1 T' T : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hσ1 : 7 / 10 ≤ σ1)
    (hT' : T' ≤ T + 1) :
    ‖∑ ρ ∈ zbox σ1 T', (mult ρ : ℂ) * Wk x δ ρ‖ ≤
      ∑ ρ ∈ zbox (7 / 10) (T + 1),
        (mult ρ : ℝ) * (x ^ (ρ.re - 1) * (δ * x * ((1 + δ) ^ 3 - 1))) := by
  have hA : 0 ≤ δ * x * ((1 + δ) ^ 3 - 1) := by
    have h1 : 1 ≤ (1 + δ) ^ 3 := one_le_pow₀ (by linarith)
    have h2 := mul_pos hδ hx
    nlinarith
  calc _ ≤ ∑ ρ ∈ zbox σ1 T', ‖(mult ρ : ℂ) * Wk x δ ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ zbox σ1 T', (mult ρ : ℝ) * (x ^ (ρ.re - 1) * (δ * x * ((1 + δ) ^ 3 - 1))) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        obtain ⟨hZ, hre, _⟩ := mem_zbox.1 hρ
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (Wk_bound x δ hx hδ ρ (by linarith) (Z_re_lt_one hZ).le) (Nat.cast_nonneg _)
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ρ hρ
          obtain ⟨hZ, hre, him⟩ := mem_zbox.1 hρ
          exact mem_zbox.2 ⟨hZ, by linarith, by linarith⟩
        · intro ρ _ _
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.le _) hA)

theorem bdry_ok {T T' σ1 c d1 d2 : ℝ} (hT : 3 ≤ T) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1)
    (hσ1 : 7 / 10 ≤ σ1) (hσc : σ1 ≤ c) (hc : 1 < c) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hav1 : ∀ u ∈ zbox (7 / 10) (T + 2), d1 ≤ |σ1 - u.re|)
    (hav2 : ∀ u ∈ G T, d2 ≤ |T' - u.im| ∧ d2 ≤ |T' + u.im|) :
    ∀ z, OnBdry z σ1 c (-T') T' → Z z ≠ 0 := by
  intro z hz hZ
  have hre := Z_re_lt_one hZ
  rcases hz with ⟨hre', him | him⟩ | ⟨him', hre' | hre'⟩
  · rw [Set.uIcc_of_le hσc] at hre'
    have hG : z ∈ G T := by
      rw [G, Finset.mem_filter, mem_zbox, him, abs_neg, abs_of_pos (by linarith)]
      exact ⟨⟨hZ, by linarith [hre'.1], by linarith⟩, by linarith⟩
    have := (hav2 z hG).2
    rw [him, add_neg_cancel, abs_zero] at this
    linarith
  · rw [Set.uIcc_of_le hσc] at hre'
    have hG : z ∈ G T := by
      rw [G, Finset.mem_filter, mem_zbox, him, abs_of_pos (by linarith)]
      exact ⟨⟨hZ, by linarith [hre'.1], by linarith⟩, by linarith⟩
    have := (hav2 z hG).1
    rw [him, sub_self, abs_zero] at this
    linarith
  · rw [Set.uIcc_of_le (by linarith)] at him'
    have hz : z ∈ zbox (7 / 10) (T + 2) :=
      mem_zbox.2 ⟨hZ, by linarith, by rw [abs_le]; constructor <;> linarith [him'.1, him'.2]⟩
    have := hav1 z hz
    rw [hre', sub_self, abs_zero] at this
    linarith
  · linarith

end EB

set_option maxHeartbeats 1000000 in
open EB in
theorem explicit_ineq : ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 →
    ∀ T : ℝ, 3 ≤ T → T ≤ x →
    δ * x * ((1 + δ) ^ 3 - 1) *
        (1 - ∑ ρ ∈ zbox (7 / 10) (T + 1), (mult ρ : ℝ) * x ^ (ρ.re - 1))
      - C * x * Real.log x / T - C * x * Real.log T ^ 2 / T ^ 2 - C * T ^ 3 * x ^ ((3 : ℝ) / 4) ≤
    ∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n := by
  obtain ⟨CL, hCL, hland⟩ := landau
  obtain ⟨Cp, hperron⟩ := perron_trunc
  obtain ⟨Cc, hcount⟩ := count_total'
  set Cc' := max Cc 0 with hCc'
  have hCc'0 : 0 ≤ Cc' := le_max_right _ _
  set B1 := (200 / 3) * (3 * Cc' + 1) + 51 with hB1
  set B2 := 256 * CL + 53 with hB2
  set Al := 2 * CL * B1 + 1 with hAl
  set Ah := 2 * CL * B2 + 1 with hAh
  have hB1p : 0 ≤ B1 := by positivity
  have hB2p : 0 ≤ B2 := by positivity
  have hAlp : 0 ≤ Al := by positivity
  have hAhp : 0 ≤ Ah := by positivity
  refine ⟨|Cp| + 128 * Ah + 45 * Al, Real.exp 10, ?_⟩
  intro x hx δ hδ hδ' T hT hTx
  -- basic facts
  have hx2 := two_le_of_exp hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx := log_ge_ten hx
  have hlogT : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ T by linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at this
  have hlogT2 : Real.log (T ^ 2) = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hlogT4 : Real.log (T + 4) ≤ 2 * Real.log T := by
    rw [← hlogT2]; exact Real.log_le_log (by linarith) (by nlinarith)
  have hlogT5 : Real.log (T + 5) ≤ 2 * Real.log T := by
    rw [← hlogT2]; exact Real.log_le_log (by linarith) (by nlinarith)
  have hlogTT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  -- choice of σ1
  set S1 : Finset ℝ := (zbox (7 / 10) (T + 2)).image (fun u => u.re) with hS1
  obtain ⟨σ1, hσa, hσb, hσav⟩ := avoid S1 (show (18 / 25 : ℝ) < 3 / 4 by norm_num)
  set d1 := (3 / 4 - 18 / 25 : ℝ) / (2 * ((S1.card : ℝ) + 1)) with hd1
  have hd1pos : 0 < d1 := div_pos (by norm_num) (by positivity)
  have hav1 : ∀ u ∈ zbox (7 / 10) (T + 2), d1 ≤ |σ1 - u.re| :=
    fun u hu => hσav _ (Finset.mem_image_of_mem _ hu)
  have hinv1 : 1 / d1 = (200 / 3) * ((S1.card : ℝ) + 1) := by
    rw [hd1, one_div_div]; ring
  -- choice of T'
  set S2 : Finset ℝ := (G T).image (fun u => u.im) ∪ (G T).image (fun u => -u.im) with hS2
  obtain ⟨T', hT'a, hT'b, hT'av⟩ := avoid S2 (show T < T + 1 by linarith)
  set d2 := (T + 1 - T) / (2 * ((S2.card : ℝ) + 1)) with hd2
  have hd2' : d2 = 1 / (2 * ((S2.card : ℝ) + 1)) := by rw [hd2]; congr 1; ring
  have hd2pos : 0 < d2 := by rw [hd2']; positivity
  have hinv2 : 1 / d2 = 2 * ((S2.card : ℝ) + 1) := by rw [hd2', one_div_one_div]
  have hav2 : ∀ u ∈ G T, d2 ≤ |T' - u.im| ∧ d2 ≤ |T' + u.im| := by
    intro u hu
    refine ⟨hT'av _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)), ?_⟩
    have := hT'av _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun u : ℂ => -u.im) hu))
    simp only [sub_neg_eq_add] at this
    exact this
  -- counts
  have hcardS1 : (S1.card : ℝ) ≤ Cc' * (T + 2) ^ 2 := by
    have e1 : (S1.card : ℝ) ≤ ((zbox (7 / 10) (T + 2)).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have e2 := card_le_sum_mult (zbox (7 / 10) (T + 2)) (fun u hu => (mem_zbox.1 hu).1)
    have e3 := hcount (T + 2) (by linarith)
    have e4 : Cc * (T + 2) ^ 2 ≤ Cc' * (T + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    unfold Ncount at e3
    linarith
  have hcardS2 : (S2.card : ℝ) ≤ 64 * CL * Real.log (T + 5) := by
    have e1 : S2.card ≤ (G T).card + (G T).card :=
      (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    have e1' : (S2.card : ℝ) ≤ ((G T).card : ℝ) + ((G T).card : ℝ) := by exact_mod_cast e1
    have := card_G (fun t => (hland t).1) hCL hT
    linarith
  -- Lf bounds
  set L1 := CL * Real.log (T + 4) * (1 / min d1 (1 / 50) + 1) + 4 with hL1
  set L2 := CL * Real.log (T + 4) * (1 / min d2 (1 / 50) + 1) + 1 with hL2
  have hX1 : 1 / min d1 (1 / 50) + 1 ≤ B1 * T ^ 2 := by
    have := inv_min_le hd1pos
    rw [hinv1] at this
    have hT2 : (T + 2) ^ 2 ≤ 3 * T ^ 2 := by nlinarith
    have hCT : Cc' * (T + 2) ^ 2 ≤ Cc' * (3 * T ^ 2) := mul_le_mul_of_nonneg_left hT2 hCc'0
    have h1T : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    rw [hB1]
    linarith
  have hX2 : 1 / min d2 (1 / 50) + 1 ≤ B2 * Real.log T := by
    have := inv_min_le hd2pos
    rw [hinv2] at this
    have h5 : CL * Real.log (T + 5) ≤ CL * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlogT5 hCL.le
    rw [hB2]
    linarith
  have hX1p : 0 ≤ 1 / min d1 (1 / 50) + 1 := by have := min_pos' hd1pos; positivity
  have hX2p : 0 ≤ 1 / min d2 (1 / 50) + 1 := by have := min_pos' hd2pos; positivity
  have hL1b : L1 ≤ Al * T ^ 3 := by
    have h1 : CL * Real.log (T + 4) ≤ CL * (2 * T) :=
      mul_le_mul_of_nonneg_left (by linarith) hCL.le
    have h2 : CL * Real.log (T + 4) * (1 / min d1 (1 / 50) + 1) ≤ CL * (2 * T) * (B1 * T ^ 2) :=
      mul_le_mul h1 hX1 hX1p (by positivity)
    have h3 : (4 : ℝ) ≤ T ^ 3 := by nlinarith
    rw [hL1, hAl]
    linarith
  have hL2b : L2 ≤ Ah * Real.log T ^ 2 := by
    have h1 : CL * Real.log (T + 4) ≤ CL * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlogT4 hCL.le
    have h2 : CL * Real.log (T + 4) * (1 / min d2 (1 / 50) + 1) ≤
        CL * (2 * Real.log T) * (B2 * Real.log T) :=
      mul_le_mul h1 hX2 hX2p (by positivity)
    have h3 : (1 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
    rw [hL2, hAh]
    linarith
  -- the contour
  have hP := hperron x hx2 δ hδ hδ' T' (by linarith)
  set c := 1 + 1 / Real.log x with hc
  have hinv : 0 < 1 / Real.log x := by positivity
  have hinv' : 1 / Real.log x ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c ≤ 11 / 10 := by rw [hc]; linarith
  have hLleft : ∀ y : ℝ, |y| ≤ T' → ‖Lf (σ1 + y * I)‖ ≤ L1 := fun y hy =>
    Lf_left hland hCL hT hσa hσb hd1pos hav1 (by linarith)
  have hLtop : ∀ σ : ℝ, σ1 ≤ σ → σ ≤ c → ‖Lf (σ + T' * I)‖ ≤ L2 := fun σ h1 h2 =>
    Lf_horiz hland hCL hT hT'a hT'b hσa h1 (by linarith) hd2pos hav2 (Or.inl rfl)
  have hLbot : ∀ σ : ℝ, σ1 ≤ σ → σ ≤ c → ‖Lf (σ + ((-T' : ℝ) : ℂ) * I)‖ ≤ L2 := fun σ h1 h2 =>
    Lf_horiz hland hCL hT hT'a hT'b hσa h1 (by linarith) hd2pos hav2 (Or.inr rfl)
  have hL1p : 0 ≤ L1 := le_trans (norm_nonneg _) (hLleft 0 (by simp; linarith))
  have hL2p : 0 ≤ L2 := le_trans (norm_nonneg _) (hLtop σ1 le_rfl (by linarith))
  set Bt := ∫ σ : ℝ in σ1..c, Wk x δ (σ + ((-T' : ℝ) : ℂ) * I) * Lf (σ + ((-T' : ℝ) : ℂ) * I)
    with hBt
  set Tt := ∫ σ : ℝ in σ1..c, Wk x δ (σ + (T' : ℂ) * I) * Lf (σ + (T' : ℂ) * I) with hTt
  set Rt := ∫ y : ℝ in (-T')..T', Wk x δ (c + y * I) * Lf (c + y * I) with hRt
  set Lt := ∫ y : ℝ in (-T')..T', Wk x δ (σ1 + y * I) * Lf (σ1 + y * I) with hLt
  have hLtb : ‖Lt‖ ≤ 45 * x ^ ((3 : ℝ) / 4) * L1 :=
    left_int hx1 hδ hδ' hσa hσb (by linarith) hL1p hLleft
  have hTtb : ‖Tt‖ ≤ 64 * x * L2 / T ^ 2 :=
    horiz_int hx hδ hδ' hσa hσb hT (by rw [abs_of_pos (by linarith)]; linarith) hL2p hLtop
  have hBtb : ‖Bt‖ ≤ 64 * x * L2 / T ^ 2 :=
    horiz_int hx hδ hδ' hσa hσb hT (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      hL2p hLbot
  have hsub : [[σ1, c]] ×ℂ [[-T', T']] ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    rw [mem_reProdIm, Set.uIcc_of_le (by linarith)] at hz
    simp only [Set.mem_setOf_eq]
    linarith [hz.1.1]
  have hres := rect_residue (Wk x δ) {s : ℂ | 0 < s.re}
    (isOpen_lt continuous_const Complex.continuous_re) σ1 c T' (by linarith) hc1 (by linarith)
    hsub (Wk_diffOn hx0 hδ.le)
    (bdry_ok hT hT'a hT'b (by linarith) (by linarith) hc1 hd1pos hd2pos hav1 hav2)
  have hRI : RI (fun s => Wk x δ s * Lf s) σ1 c (-T') T' = Bt - Tt + I * Rt - I * Lt := rfl
  rw [hRI] at hres
  have hRP : Rt = ∫ t : ℝ in (-T')..T', Wk x δ (c + t * I) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [Lf_eq_LSeries (by simp; linarith)]
  rw [← hRP] at hP
  set Sc := ∑ ρ ∈ zbox σ1 T', (mult ρ : ℂ) * Wk x δ ρ with hSc
  set A := δ * x * ((1 + δ) ^ 3 - 1) with hA
  have hRt : Rt = 2 * Real.pi * (Wk x δ 1 - Sc) - I * (Tt - Bt) + Lt := by
    linear_combination (-I) * hres + (Rt - Lt - 2 * Real.pi * (Wk x δ 1 - Sc)) * I_mul_I
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set E := ((1 / (2 * Real.pi) : ℝ) : ℂ) * (-I * (Tt - Bt) + Lt) with hE
  have hQ : ((1 / (2 * Real.pi) : ℝ) : ℂ) * Rt = (A : ℂ) - Sc + E := by
    rw [hRt, hE, Wk_one, ← hA]
    have : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    push_cast at this ⊢
    field_simp
    ring
  have hEb : ‖E‖ ≤ ‖Tt‖ + ‖Bt‖ + ‖Lt‖ := by
    rw [hE, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖-I * (Tt - Bt) + Lt‖ ≤ ‖Tt‖ + ‖Bt‖ + ‖Lt‖ := by
      calc _ ≤ ‖-I * (Tt - Bt)‖ + ‖Lt‖ := norm_add_le _ _
        _ = ‖Tt - Bt‖ + ‖Lt‖ := by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
        _ ≤ _ := by linarith [norm_sub_le Tt Bt]
    have h2pi : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one hpi]; linarith [Real.pi_gt_three]
    calc 1 / (2 * Real.pi) * ‖-I * (Tt - Bt) + Lt‖ ≤ 1 * ‖-I * (Tt - Bt) + Lt‖ :=
          mul_le_mul_of_nonneg_right h2pi (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h1
  -- real parts
  set S := ∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n
    with hS
  have hreS : -(Cp * x * Real.log x / T') ≤ S - (((1 / (2 * Real.pi) : ℝ) : ℂ) * Rt).re := by
    have := (Complex.abs_re_le_norm (((S : ℝ) : ℂ) - ((1 / (2 * Real.pi) : ℝ) : ℂ) * Rt)).trans hP
    rw [Complex.sub_re, Complex.ofReal_re] at this
    exact (abs_le.1 this).1
  have hreQ : A - ‖Sc‖ - ‖E‖ ≤ (((1 / (2 * Real.pi) : ℝ) : ℂ) * Rt).re := by
    rw [hQ, Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    have e1 := Complex.re_le_norm Sc
    have e2 := Complex.abs_re_le_norm E
    have e3 := neg_abs_le E.re
    linarith
  have hScb : ‖Sc‖ ≤ ∑ ρ ∈ zbox (7 / 10) (T + 1), (mult ρ : ℝ) * (x ^ (ρ.re - 1) * A) :=
    sum_W_le (T := T) hx0 hδ (by linarith : 7 / 10 ≤ σ1) hT'b
  have hAsum : A * (1 - ∑ ρ ∈ zbox (7 / 10) (T + 1), (mult ρ : ℝ) * x ^ (ρ.re - 1)) =
      A - ∑ ρ ∈ zbox (7 / 10) (T + 1), (mult ρ : ℝ) * (x ^ (ρ.re - 1) * A) := by
    rw [mul_sub, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  -- error terms
  have hlx : 0 ≤ Real.log x := by linarith
  have hX1n : 0 ≤ x * Real.log x / T := by positivity
  have hX2n : 0 ≤ x * Real.log T ^ 2 / T ^ 2 := by positivity
  have hX3n : 0 ≤ T ^ 3 * x ^ ((3 : ℝ) / 4) := by positivity
  have hCp : Cp * x * Real.log x / T' ≤ |Cp| * (x * Real.log x / T) := by
    calc Cp * x * Real.log x / T' ≤ |Cp| * x * Real.log x / T' := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          apply mul_le_mul_of_nonneg_right _ hlx
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hx0.le
      _ ≤ |Cp| * x * Real.log x / T :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hT'a
      _ = _ := by ring
  have hTB : 64 * x * L2 / T ^ 2 ≤ 64 * Ah * (x * Real.log T ^ 2 / T ^ 2) := by
    calc 64 * x * L2 / T ^ 2 ≤ 64 * x * (Ah * Real.log T ^ 2) / T ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hL2b (by positivity)
      _ = _ := by ring
  have hLB : 45 * x ^ ((3 : ℝ) / 4) * L1 ≤ 45 * Al * (T ^ 3 * x ^ ((3 : ℝ) / 4)) := by
    calc 45 * x ^ ((3 : ℝ) / 4) * L1 ≤ 45 * x ^ ((3 : ℝ) / 4) * (Al * T ^ 3) :=
          mul_le_mul_of_nonneg_left hL1b (by positivity)
      _ = _ := by ring
  have r1 : (|Cp| + 128 * Ah + 45 * Al) * x * Real.log x / T =
      (|Cp| + 128 * Ah + 45 * Al) * (x * Real.log x / T) := by ring
  have r2 : (|Cp| + 128 * Ah + 45 * Al) * x * Real.log T ^ 2 / T ^ 2 =
      (|Cp| + 128 * Ah + 45 * Al) * (x * Real.log T ^ 2 / T ^ 2) := by ring
  have r3 : (|Cp| + 128 * Ah + 45 * Al) * T ^ 3 * x ^ ((3 : ℝ) / 4) =
      (|Cp| + 128 * Ah + 45 * Al) * (T ^ 3 * x ^ ((3 : ℝ) / 4)) := by ring
  have m1 : |Cp| * (x * Real.log x / T) ≤ (|Cp| + 128 * Ah + 45 * Al) * (x * Real.log x / T) :=
    mul_le_mul_of_nonneg_right (by linarith) hX1n
  have m2 : 128 * Ah * (x * Real.log T ^ 2 / T ^ 2) ≤
      (|Cp| + 128 * Ah + 45 * Al) * (x * Real.log T ^ 2 / T ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Cp]) hX2n
  have m3 : 45 * Al * (T ^ 3 * x ^ ((3 : ℝ) / 4)) ≤
      (|Cp| + 128 * Ah + 45 * Al) * (T ^ 3 * x ^ ((3 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Cp]) hX3n
  have g1 : (((1 / (2 * Real.pi) : ℝ) : ℂ) * Rt).re - Cp * x * Real.log x / T' ≤ S := by linarith [hreS]
  have g2 : A - ‖Sc‖ - ‖E‖ - Cp * x * Real.log x / T' ≤ S := by linarith [hreQ]
  have f1 : A - ‖Sc‖ - ‖E‖ - |Cp| * (x * Real.log x / T) ≤ S := by linarith [hCp]
  have f2 : ‖E‖ ≤ 128 * Ah * (x * Real.log T ^ 2 / T ^ 2) + 45 * Al * (T ^ 3 * x ^ ((3 : ℝ) / 4)) := by
    linarith
  rw [hAsum, r1, r2, r3]
  linarith



-- ===== from HF.lean =====
/-! ## F. Assembly -/

theorem Ncount_nonneg (σ T : ℝ) : 0 ≤ Ncount σ T :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem sum_le_Ncount {F : Finset ℂ} {σ T : ℝ} (hF : F ⊆ zbox σ T) :
    ∑ ρ ∈ F, (mult ρ : ℝ) ≤ Ncount σ T :=
  Finset.sum_le_sum_of_subset_of_nonneg hF fun _ _ _ => Nat.cast_nonneg _

/-- Zeros near the line, summed in layers of width `c / log (T+3)`. -/
theorem layer_sum {c A C κ ℓ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hZF : ∀ ρ : ℂ, Z ρ = 0 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3))
    (hD : ∀ T : ℝ, 3 ≤ T → ∀ σ : ℝ, 1 - κ ≤ σ → Ncount σ T ≤ C * T ^ (A * (1 - σ)))
    (hr : Real.exp ((A - ℓ / 2) * c) < 1) {T x : ℝ} (hT : 3 ≤ T) (hx : T ^ ℓ ≤ x)
    (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) :
    ∑ ρ ∈ (zbox (7 / 10) T).filter (fun ρ => 1 - κ ≤ ρ.re), (mult ρ : ℝ) * x ^ (ρ.re - 1) ≤
      |C| * Real.exp (A * c) * (Real.exp ((A - ℓ / 2) * c) / (1 - Real.exp ((A - ℓ / 2) * c))) := by
  set F := (zbox (7 / 10) T).filter (fun ρ => 1 - κ ≤ ρ.re) with hF
  set L := Real.log (T + 3) with hL
  set r := Real.exp ((A - ℓ / 2) * c) with hrdef
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hLT : Real.log T ≤ L := Real.log_le_log hT0 (by linarith)
  have hL0 : 0 < L := hlT.trans_le hLT
  have hLT2 : L ≤ 2 * Real.log T := by
    rw [hL, ← Real.log_rpow hT0]
    apply Real.log_le_log (by linarith)
    have : T ^ (2 : ℝ) = T * T := by rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hT0]; simp
    rw [this]; nlinarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hT1 hℓ) hx
  have hx0 : 0 < x := by linarith
  let jf : ℂ → ℕ := fun ρ => ⌊(1 - ρ.re) * L / c⌋₊
  have hmem : ∀ ρ ∈ F, Z ρ = 0 ∧ 1 - κ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    intro ρ hρ
    rw [hF, Finset.mem_filter, mem_zbox] at hρ
    exact ⟨hρ.1.1, hρ.2, hρ.1.2.2⟩
  have hbeta : ∀ ρ ∈ F, ρ.re ≤ 1 - c / L := by
    intro ρ hρ
    obtain ⟨hz, -, him⟩ := hmem ρ hρ
    have h1 := hZF ρ hz
    have h2 : Real.log (|ρ.im| + 3) ≤ L := Real.log_le_log (by positivity) (by linarith)
    have h3 : 0 < Real.log (|ρ.im| + 3) := Real.log_pos (by linarith [abs_nonneg ρ.im])
    have : c / L ≤ c / Real.log (|ρ.im| + 3) := div_le_div_of_nonneg_left hc.le h3 h2
    linarith
  -- each term
  have hterm : ∀ ρ ∈ F, (mult ρ : ℝ) * x ^ (ρ.re - 1) ≤
      (mult ρ : ℝ) * Real.exp (-(ℓ * c * jf ρ / 2)) := by
    intro ρ hρ
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hj : (jf ρ : ℝ) ≤ (1 - ρ.re) * L / c :=
      Nat.floor_le (div_nonneg (mul_nonneg (by linarith [hbeta ρ hρ, div_pos hc hL0]) hL0.le) hc.le)
    have hj' : c * jf ρ / L ≤ 1 - ρ.re := by
      rw [le_div_iff₀ hc] at hj
      rw [div_le_iff₀ hL0]; linarith
    calc x ^ (ρ.re - 1) ≤ x ^ (-(c * jf ρ / L)) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ ≤ (T ^ ℓ) ^ (-(c * jf ρ / L)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hx
            (by have : 0 ≤ c * jf ρ / L := by positivity
                linarith)
      _ = Real.exp (Real.log T * (ℓ * -(c * jf ρ / L))) := by
          rw [← Real.rpow_mul hT0.le, Real.rpow_def_of_pos hT0]
      _ ≤ Real.exp (-(ℓ * c * jf ρ / 2)) := by
          apply Real.exp_le_exp.2
          have hj0 : 0 ≤ ℓ * c * jf ρ := by positivity
          have : Real.log T * (ℓ * -(c * jf ρ / L)) = -(ℓ * c * jf ρ) * (Real.log T / L) := by
            field_simp
          rw [this]
          have : 1 / 2 ≤ Real.log T / L := by rw [le_div_iff₀ hL0]; linarith
          nlinarith
  -- layer count
  have hlayer : ∀ j : ℕ, ∑ ρ ∈ F.filter (fun ρ => jf ρ = j), (mult ρ : ℝ) ≤
      |C| * Real.exp (A * c * (j + 1)) := by
    intro j
    set σj := max (1 - κ) (1 - c * (j + 1) / L)
    have hsub : F.filter (fun ρ => jf ρ = j) ⊆ zbox σj T := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, hk, him⟩ := hmem ρ hρ.1
      rw [mem_zbox]
      refine ⟨hz, max_le hk ?_, him⟩
      have h1 : (1 - ρ.re) * L / c < jf ρ + 1 := Nat.lt_floor_add_one _
      rw [hρ.2, div_lt_iff₀ hc] at h1
      have : 1 - ρ.re < c * (j + 1) / L := by rw [lt_div_iff₀ hL0]; linarith
      linarith
    have hσ : 1 - κ ≤ σj := le_max_left _ _
    have h1 := (sum_le_Ncount hsub).trans (hD T hT σj hσ)
    have h2 : T ^ (A * (1 - σj)) ≤ Real.exp (A * c * (j + 1)) := by
      rw [Real.rpow_def_of_pos hT0]
      apply Real.exp_le_exp.2
      have h3 : 1 - σj ≤ c * (j + 1) / L := by
        have := le_max_right (1 - κ) (1 - c * (j + 1) / L); linarith
      have h4 : 0 ≤ 1 - σj := by
        have : 0 < c * (j + 1) / L := by positivity
        rcases le_total (1 - κ) (1 - c * (j + 1) / L) with h | h
        · rw [show σj = 1 - c * (j + 1) / L from max_eq_right h]; linarith
        · rw [show σj = 1 - κ from max_eq_left h]; linarith
      calc Real.log T * (A * (1 - σj)) ≤ L * (A * (c * (j + 1) / L)) := by
            apply mul_le_mul hLT _ (by positivity) hL0.le
            exact mul_le_mul_of_nonneg_left h3 hA
        _ = A * c * (j + 1) := by field_simp
    calc ∑ ρ ∈ F.filter (fun ρ => jf ρ = j), (mult ρ : ℝ) ≤ C * T ^ (A * (1 - σj)) := h1
      _ ≤ |C| * T ^ (A * (1 - σj)) := by gcongr; exact le_abs_self C
      _ ≤ |C| * Real.exp (A * c * (j + 1)) := by gcongr
  -- assemble
  have hjrange : ∀ ρ ∈ F, jf ρ ∈ Finset.Ico 1 (⌊κ * L / c⌋₊ + 1) := by
    intro ρ hρ
    rw [Finset.mem_Ico]
    constructor
    · apply Nat.le_floor
      have := hbeta ρ hρ
      rw [Nat.cast_one, le_div_iff₀ hc]
      have : c / L * L = c := by field_simp
      nlinarith
    · rw [Nat.lt_succ_iff]
      apply Nat.floor_le_floor
      have := (hmem ρ hρ).2.1
      gcongr
      linarith
  calc ∑ ρ ∈ F, (mult ρ : ℝ) * x ^ (ρ.re - 1)
      ≤ ∑ ρ ∈ F, (mult ρ : ℝ) * Real.exp (-(ℓ * c * jf ρ / 2)) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.Ico 1 (⌊κ * L / c⌋₊ + 1),
          ∑ ρ ∈ F.filter (fun ρ => jf ρ = j), (mult ρ : ℝ) * Real.exp (-(ℓ * c * jf ρ / 2)) :=
        (Finset.sum_fiberwise_of_maps_to hjrange _).symm
    _ = ∑ j ∈ Finset.Ico 1 (⌊κ * L / c⌋₊ + 1),
          (∑ ρ ∈ F.filter (fun ρ => jf ρ = j), (mult ρ : ℝ)) * Real.exp (-(ℓ * c * j / 2)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [(Finset.mem_filter.1 hρ).2]
    _ ≤ ∑ j ∈ Finset.Ico 1 (⌊κ * L / c⌋₊ + 1),
          |C| * Real.exp (A * c * (j + 1)) * Real.exp (-(ℓ * c * j / 2)) := by
        gcongr with j hj
        exact hlayer j
    _ = |C| * Real.exp (A * c) * ∑ j ∈ Finset.Ico 1 (⌊κ * L / c⌋₊ + 1), r ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hrdef, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2; ring
    _ ≤ |C| * Real.exp (A * c) * (r ^ 1 / (1 - r)) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one (Real.exp_pos _).le hr
    _ = _ := by rw [pow_one]

theorem zero_sum_small : ∃ ℓ0 T0 : ℝ, 0 < ℓ0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ x : ℝ, T ^ ℓ0 ≤ x →
    ∑ ρ ∈ zbox (7 / 10) T, (mult ρ : ℝ) * x ^ (ρ.re - 1) ≤ 1 / 8 := by
  obtain ⟨c, hc, hZF⟩ := zero_free'
  obtain ⟨A, C, κ, hA, hκ, hD⟩ := density
  obtain ⟨C', hC'⟩ := count_total'
  set K : ℝ := |C| * Real.exp (A * c) with hK
  have hK0 : 0 ≤ K := by positivity
  -- choose ℓ0 with (ℓ0/2 - A) c ≥ log (32 (K+1)) + 1 and ℓ0 κ ≥ 3
  set ℓ0 : ℝ := 2 * A + 2 * (Real.log (32 * (K + 1)) + 1) / c + 3 / κ with hℓ0
  have hlog0 : 0 ≤ Real.log (32 * (K + 1)) := Real.log_nonneg (by linarith)
  have hℓ0pos : 0 < ℓ0 := by positivity
  have hℓκ : 3 ≤ ℓ0 * κ := by
    have : 3 / κ * κ = 3 := by field_simp
    have h1 : 0 ≤ (2 * A + 2 * (Real.log (32 * (K + 1)) + 1) / c) * κ := by positivity
    nlinarith
  have hexp : Real.log (32 * (K + 1)) + 1 ≤ (ℓ0 / 2 - A) * c := by
    have : (ℓ0 / 2 - A) * c = Real.log (32 * (K + 1)) + 1 + 3 / κ / 2 * c := by
      rw [hℓ0]; field_simp; ring
    rw [this]; have : 0 ≤ 3 / κ / 2 * c := by positivity
    linarith
  set r := Real.exp ((A - ℓ0 / 2) * c) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hrle : r ≤ Real.exp (-1) / (32 * (K + 1)) := by
    rw [hr, le_div_iff₀ (by positivity), ← Real.exp_log (by positivity : (0:ℝ) < 32 * (K + 1)),
      ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have he1 : Real.exp (-1) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have hr12 : r ≤ 1 / 2 := by
    have : Real.exp (-1) / (32 * (K + 1)) ≤ Real.exp (-1) :=
      div_le_self (Real.exp_pos _).le (by linarith)
    linarith
  have hr1 : r < 1 := by linarith
  refine ⟨ℓ0, 16 * (|C'| + 1) + 3, hℓ0pos, fun T hT x hx => ?_⟩
  have hT3 : 3 ≤ T := by linarith [abs_nonneg C']
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hT1 hℓ0pos.le) hx
  have hx0 : 0 < x := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not (zbox (7 / 10) T) (fun ρ => 1 - κ ≤ ρ.re)]
  have h2 := layer_sum hc hκ hZF hD hr1 hT3 hx hℓ0pos.le hA.le
  have h2' : K * (r / (1 - r)) ≤ 1 / 16 := by
    have h1r : r / (1 - r) ≤ 2 * r := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [hr0, hr12]
    have hKr : K * (2 * r) ≤ 1 / 16 := by
      have : K * r ≤ (K + 1) * (Real.exp (-1) / (32 * (K + 1))) := by
        apply mul_le_mul (by linarith) hrle hr0.le (by linarith)
      have e : (K + 1) * (Real.exp (-1) / (32 * (K + 1))) = Real.exp (-1) / 32 := by
        field_simp
      nlinarith
    calc K * (r / (1 - r)) ≤ K * (2 * r) := mul_le_mul_of_nonneg_left h1r hK0
      _ ≤ 1 / 16 := hKr
  have h1 : ∑ ρ ∈ (zbox (7 / 10) T).filter (fun ρ => ¬ 1 - κ ≤ ρ.re),
      (mult ρ : ℝ) * x ^ (ρ.re - 1) ≤ 1 / 16 := by
    have hxk : x ^ (-κ) ≤ T ^ (-(3 : ℝ)) := by
      calc x ^ (-κ) ≤ (T ^ ℓ0) ^ (-κ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)
        _ = T ^ (-(ℓ0 * κ)) := by rw [← Real.rpow_mul hT0.le]; ring_nf
        _ ≤ T ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    calc ∑ ρ ∈ (zbox (7 / 10) T).filter (fun ρ => ¬ 1 - κ ≤ ρ.re), (mult ρ : ℝ) * x ^ (ρ.re - 1)
        ≤ ∑ ρ ∈ (zbox (7 / 10) T).filter (fun ρ => ¬ 1 - κ ≤ ρ.re), (mult ρ : ℝ) * T ^ (-(3 : ℝ)) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [Finset.mem_filter] at hρ
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hρ.2])).trans hxk
      _ = (∑ ρ ∈ (zbox (7 / 10) T).filter (fun ρ => ¬ 1 - κ ≤ ρ.re), (mult ρ : ℝ)) *
            T ^ (-(3 : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ Ncount (7 / 10) T * T ^ (-(3 : ℝ)) := by
          gcongr; exact sum_le_Ncount (Finset.filter_subset _ _)
      _ ≤ C' * T ^ 2 * T ^ (-(3 : ℝ)) := by gcongr; exact hC' T hT3
      _ = C' / T := by
          rw [Real.rpow_neg hT0.le, ← Real.rpow_natCast, mul_assoc, ← div_eq_mul_inv,
            ← Real.rpow_sub hT0]
          norm_num; rw [Real.rpow_neg_one]; ring
      _ ≤ 1 / 16 := by
          rw [div_le_iff₀ hT0]
          have := le_abs_self C'; nlinarith
  linarith

/-- Hoheisel-type short-interval prime statement. -/
def Hoheisel : Prop :=
  ∃ θ : ℝ, θ < 1 ∧ ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m →
    ∃ p : ℕ, p.Prime ∧ m < p ∧ (p : ℝ) ≤ m + (m : ℝ) ^ θ

theorem trap (a l : ℝ) (hl : 0 ≤ l) :
    max (a + 4 * l) 0 - max (a + 3 * l) 0 - max (a + l) 0 + max a 0 ≤ l ∧
    (0 ≤ a → max (a + 4 * l) 0 - max (a + 3 * l) 0 - max (a + l) 0 + max a 0 = 0) ∧
    (a ≤ -(4 * l) → max (a + 4 * l) 0 - max (a + 3 * l) 0 - max (a + l) 0 + max a 0 = 0) := by
  refine ⟨?_, fun h => ?_, fun h => ?_⟩ <;>
  · simp only [max_def]; split_ifs <;> linarith

theorem lp_mul_pow {y q : ℝ} (hy : 0 < y) (hq : 0 < q) (k : ℕ) :
    lp (y * q ^ k) = max (Real.log y + k * Real.log q) 0 := by
  unfold lp; rw [Real.log_mul hy.ne' (pow_pos hq k).ne', Real.log_pow]

theorem gw_eq {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu : 0 < u) :
    gw x δ u = max (Real.log (x / u) + 4 * Real.log (1 + δ)) 0
      - max (Real.log (x / u) + 3 * Real.log (1 + δ)) 0
      - max (Real.log (x / u) + Real.log (1 + δ)) 0 + max (Real.log (x / u)) 0 := by
  have hxu : 0 < x / u := div_pos hx hu
  have hq : (0 : ℝ) < 1 + δ := by linarith
  have e4 : x * (1 + δ) ^ 4 / u = x / u * (1 + δ) ^ 4 := by ring
  have e3 : x * (1 + δ) ^ 3 / u = x / u * (1 + δ) ^ 3 := by ring
  have e1 : x * (1 + δ) / u = x / u * (1 + δ) ^ 1 := by ring
  unfold gw
  rw [e4, e3, e1, lp_mul_pow hxu hq, lp_mul_pow hxu hq, lp_mul_pow hxu hq]
  simp [lp]

theorem gw_le {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu : 0 < u) : gw x δ u ≤ δ := by
  rw [gw_eq hx hδ hu]
  have hl : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have h2 : Real.log (1 + δ) ≤ δ := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + δ)]
  linarith [(trap (Real.log (x / u)) _ hl).1]

theorem gw_zero_left {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu : 0 < u) (h : u ≤ x) :
    gw x δ u = 0 := by
  rw [gw_eq hx hδ hu]
  have hl : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  exact (trap _ _ hl).2.1 (Real.log_nonneg (by rw [le_div_iff₀ hu]; linarith))

theorem gw_zero_right {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu : 0 < u)
    (h : x * (1 + δ) ^ 4 ≤ u) : gw x δ u = 0 := by
  rw [gw_eq hx hδ hu]
  have hl : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  apply (trap _ _ hl).2.2
  have hq : (0 : ℝ) < (1 + δ) ^ 4 := by positivity
  have : x / u ≤ ((1 + δ) ^ 4)⁻¹ := by
    rw [div_le_iff₀ hu, ← div_eq_inv_mul, le_div_iff₀ hq]; linarith
  have := Real.log_le_log (div_pos hx hu) this
  rw [Real.log_inv, Real.log_pow] at this
  push_cast at this
  linarith

/-- Numbers `≤ N` that are prime powers but not primes. -/
theorem card_pp_le (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card ≤
      (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  calc ((Finset.range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)).card
      ≤ ((Finset.range (Nat.sqrt N + 1) ×ˢ Finset.range (Nat.log 2 N + 1)).image
          (fun pk : ℕ × ℕ => pk.1 ^ pk.2)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        obtain ⟨hnN, ⟨p, k, hp, hk, rfl⟩, hnp⟩ := hn
        have hp' := hp.nat_prime
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h | h
          · interval_cases k
            simp at hnp; exact absurd hp' hnp
          · exact h
        simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
        refine ⟨(p, k), ⟨?_, ?_⟩, rfl⟩
        · rw [Nat.lt_succ_iff, Nat.le_sqrt]
          calc p * p = p ^ 2 := by ring
            _ ≤ p ^ k := Nat.pow_le_pow_right hp'.pos hk2
            _ ≤ N := by omega
        · rw [Nat.lt_succ_iff]
          apply Nat.le_log_of_pow_le (by norm_num)
          calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp'.two_le k
            _ ≤ N := by omega
    _ ≤ _ := Finset.card_image_le.trans (by simp)

theorem log_le_rpow_ev {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ≤ x ^ ε := by
  have h := (isLittleO_log_rpow_atTop hε).bound (c := 1 / (|K| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hp : 0 ≤ x ^ ε := by positivity
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp] at hx
  have hK : K ≤ |K| + 1 := by linarith [le_abs_self K]
  calc K * Real.log x ≤ (|K| + 1) * Real.log x := by nlinarith
    _ ≤ (|K| + 1) * (1 / (|K| + 1) * x ^ ε) := by gcongr
    _ = x ^ ε := by field_simp

theorem pp_bound_ev {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 60) : ∀ᶠ x : ℝ in atTop,
    Real.log (2 * x) * ((Real.sqrt (2 * x) + 1) * (Real.log (2 * x) / Real.log 2 + 1)) <
      x ^ (1 - η) / 5 := by
  have hε : 0 < (1 / 2 - η) / 2 := by linarith
  filter_upwards [log_le_rpow_ev hε 13, eventually_ge_atTop (4 : ℝ)] with x hx hx4
  have hx0 : 0 < x := by linarith
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have hlx0 : 0 < Real.log x := by linarith
  have h2x : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']; linarith
  have h2x0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt (2 * x) + 1 ≤ 3 * x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h1 : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg x]
    have h2 : 1 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    linarith
  have hq : Real.log (2 * x) / Real.log 2 + 1 ≤ 5 * Real.log x := by
    rw [div_add_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hlx0 (by linarith : (0:ℝ) < Real.log 2 - 0.69)]
  have hpow : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 - η) = x ^ (1 - η) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hx' : (13 * Real.log x) ^ 2 ≤ x ^ ((1 / 2 - η) / 2) * x ^ ((1 / 2 - η) / 2) := by
    nlinarith
  rw [← Real.rpow_add hx0] at hx'
  have hhalf : 0 < x ^ (1 / 2 : ℝ) := by positivity
  calc Real.log (2 * x) * ((Real.sqrt (2 * x) + 1) * (Real.log (2 * x) / Real.log 2 + 1))
      ≤ (2 * Real.log x) * ((3 * x ^ (1 / 2 : ℝ)) * (5 * Real.log x)) := by
        gcongr
    _ = 30 * Real.log x ^ 2 * x ^ (1 / 2 : ℝ) := by ring
    _ < 169 / 5 * Real.log x ^ 2 * x ^ (1 / 2 : ℝ) := by
        have : 0 < Real.log x ^ 2 * x ^ (1 / 2 : ℝ) := by positivity
        nlinarith
    _ ≤ x ^ (1 / 2 - η) / 5 * x ^ (1 / 2 : ℝ) := by
        have : (1 / 2 - η) / 2 + (1 / 2 - η) / 2 = 1 / 2 - η := by ring
        rw [this] at hx'
        gcongr
        nlinarith
    _ = x ^ (1 - η) / 5 := by rw [← hpow]; ring


/-- Hoheisel's theorem in counting form. -/
def HoheiselCount : Prop :=
  ∃ θ : ℝ, θ < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m →
    c * (m : ℝ) ^ θ / Real.log m ≤
      (((Finset.Ioc m (m + ⌊(m : ℝ) ^ θ⌋₊)).filter Nat.Prime).card : ℝ)

set_option maxHeartbeats 1000000 in
theorem hoheisel_count : HoheiselCount := by
  obtain ⟨C, X0, hE⟩ := explicit_ineq
  obtain ⟨ℓ0, T0, hℓ0, hS⟩ := zero_sum_small
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 60 ∧ 3 * η * ℓ0 ≤ 1 / 2 := by
    refine ⟨min (1 / 60) (1 / (6 * ℓ0)), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    have h := min_le_right (1 / 60 : ℝ) (1 / (6 * ℓ0))
    calc 3 * min (1 / 60) (1 / (6 * ℓ0)) * ℓ0 ≤ 3 * (1 / (6 * ℓ0)) * ℓ0 := by gcongr
      _ = 1 / 2 := by field_simp; ring
  -- eventual conditions
  have c3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x ^ (3 * η) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop 3
  have c4 : ∀ᶠ x : ℝ in atTop, T0 ≤ x ^ (3 * η) + 1 :=
    (tendsto_atTop_add_const_right _ 1 (tendsto_rpow_atTop (by linarith))).eventually_ge_atTop T0
  have c5 : ∀ᶠ x : ℝ in atTop, (x ^ (3 * η) + 1) ^ ℓ0 ≤ x := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop
      ((2 : ℝ) ^ ℓ0)
    filter_upwards [h, c3, eventually_ge_atTop (1 : ℝ)] with x hx h3 hx1
    have hx0 : 0 < x := by linarith
    have h1 : x ^ (3 * η) + 1 ≤ 2 * x ^ (3 * η) := by linarith
    calc (x ^ (3 * η) + 1) ^ ℓ0 ≤ (2 * x ^ (3 * η)) ^ ℓ0 := by gcongr
      _ = 2 ^ ℓ0 * x ^ (3 * η * ℓ0) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
      _ ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
          exact mul_le_mul hx (Real.rpow_le_rpow_of_exponent_le hx1 hη2) (by positivity)
            (by positivity)
      _ = x := by rw [← Real.rpow_add hx0]; norm_num
  have c6 : ∀ᶠ x : ℝ in atTop,
      C * (x ^ (3 * η)) ^ 3 * x ^ ((3 : ℝ) / 4) ≤ (x ^ (-η) / 5) ^ 2 * x / 4 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 15)).eventually
      (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / (100 * (|C| + 1))))
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith
    have e1 : (x ^ (3 * η)) ^ 3 * x ^ ((3 : ℝ) / 4) = x ^ (9 * η + 3 / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; push_cast; ring_nf
    have e2 : (x ^ (-η) / 5) ^ 2 * x / 4 = x ^ (1 - 2 * η) / 100 := by
      have h2 : (x ^ (-η)) ^ 2 * x = x ^ (1 - 2 * η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add_one hx0.ne']
        push_cast; ring_nf
      rw [div_pow, ← h2]; ring
    have e3 : x ^ (9 * η + 3 / 4) ≤ x ^ (1 - 2 * η) * x ^ (-(1 / 15 : ℝ)) := by
      rw [← Real.rpow_add hx0]; apply Real.rpow_le_rpow_of_exponent_le hx1; linarith
    rw [mul_assoc, e1, e2]
    have hp : 0 ≤ x ^ (9 * η + 3 / 4) := by positivity
    have hq : 0 ≤ x ^ (1 - 2 * η) := by positivity
    calc C * x ^ (9 * η + 3 / 4) ≤ (|C| + 1) * x ^ (9 * η + 3 / 4) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hp
      _ ≤ (|C| + 1) * (x ^ (1 - 2 * η) * x ^ (-(1 / 15 : ℝ))) := by gcongr
      _ ≤ (|C| + 1) * (x ^ (1 - 2 * η) * (1 / (100 * (|C| + 1)))) := by gcongr
      _ = x ^ (1 - 2 * η) / 100 := by field_simp
  have c7 : ∀ᶠ x : ℝ in atTop, C * x * Real.log x / x ^ (3 * η) ≤ (x ^ (-η) / 5) ^ 2 * x / 4 := by
    filter_upwards [log_le_rpow_ev hη0 (100 * C), eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith
    have e : (x ^ (-η) / 5) ^ 2 * x / 4 = x * x ^ η / (100 * x ^ (3 * η)) := by
      have : (x ^ (-η)) ^ 2 * x ^ (3 * η) = x ^ η := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; push_cast; ring_nf
      field_simp; rw [← this]; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ x * x ^ (3 * η) := by positivity
    nlinarith
  have c8 : ∀ᶠ x : ℝ in atTop,
      C * x * Real.log (x ^ (3 * η)) ^ 2 / (x ^ (3 * η)) ^ 2 ≤ (x ^ (-η) / 5) ^ 2 * x / 4 := by
    filter_upwards [log_le_rpow_ev hη0 (30 * η * (|C| + 1)), eventually_ge_atTop (1 : ℝ)]
      with x hx hx1
    have hx0 : 0 < x := by linarith
    rw [Real.log_rpow hx0]
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have e : (x ^ (-η) / 5) ^ 2 * x / 4 = x * (x ^ η) ^ 2 * x ^ (2 * η) / (100 * (x ^ (3 * η)) ^ 2) := by
      have : (x ^ (-η)) ^ 2 * (x ^ (3 * η)) ^ 2 = (x ^ η) ^ 2 * x ^ (2 * η) := by
        simp only [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        push_cast; ring_nf
      have h5 : (x ^ (-η)) ^ 2 = (x ^ η) ^ 2 * x ^ (2 * η) / (x ^ (3 * η)) ^ 2 := by
        rw [eq_div_iff (by positivity)]; exact this
      rw [div_pow, h5]
      generalize x ^ η = a; generalize x ^ (2 * η) = b
      generalize hc : x ^ (3 * η) = c
      have : c ≠ 0 := by rw [← hc]; positivity
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 ≤ x ^ (2 * η) := Real.one_le_rpow hx1 (by linarith)
    have hsq : (30 * η * (|C| + 1) * Real.log x) ^ 2 ≤ (x ^ η) ^ 2 := by
      gcongr
    have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
    have hp : 0 ≤ x * (x ^ (3 * η)) ^ 2 := by positivity
    have hq : 0 ≤ (3 * η * Real.log x) ^ 2 := by positivity
    calc C * x * (3 * η * Real.log x) ^ 2 * (100 * (x ^ (3 * η)) ^ 2)
        ≤ (|C| + 1) * x * (3 * η * Real.log x) ^ 2 * (100 * (x ^ (3 * η)) ^ 2) := by
          gcongr
      _ = (30 * η * (|C| + 1) * Real.log x) ^ 2 * (x * (x ^ (3 * η)) ^ 2) / (|C| + 1) := by
          field_simp; ring
      _ ≤ (30 * η * (|C| + 1) * Real.log x) ^ 2 * (x * (x ^ (3 * η)) ^ 2) := by
          apply div_le_self (by positivity); linarith [abs_nonneg C]
      _ ≤ (x ^ η) ^ 2 * (x * (x ^ (3 * η)) ^ 2) := by gcongr
      _ ≤ x * (x ^ η) ^ 2 * x ^ (2 * η) * (x ^ (3 * η)) ^ 2 := by
          have : 0 ≤ (x ^ η) ^ 2 * (x * (x ^ (3 * η)) ^ 2) := by positivity
          nlinarith
  have c10 : ∀ᶠ x : ℝ in atTop, x ^ (-η) ≤ 1 / 2 :=
    (tendsto_rpow_neg_atTop hη0).eventually (ge_mem_nhds (by norm_num))
  have ev := (eventually_ge_atTop X0).and ((eventually_ge_atTop (4 : ℝ)).and (c3.and (c4.and
    (c5.and (c6.and (c7.and (c8.and (c10.and (pp_bound_ev hη0 hη1)))))))))
  obtain ⟨X, hX⟩ := eventually_atTop.1 ev
  refine ⟨1 - η, by linarith, 1 / 12, by norm_num, ⌈X⌉₊, fun m hm => ?_⟩
  have hxX : X ≤ (m : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hm)
  obtain ⟨h0, h4, h3, h4', h5, h6, h7, h8, h10, h9⟩ := hX _ hxX
  set x : ℝ := (m : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set T : ℝ := x ^ (3 * η) with hT
  set δ : ℝ := x ^ (-η) / 5 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 10 := by rw [hδ]; linarith
  have hTx : T ≤ x := by
    calc T ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hlow := hE x h0 δ hδ0 hδ1 T h3 hTx
  have hSb := hS (T + 1) h4' x h5
  have hW : 3 * δ ^ 2 * x ≤ δ * x * ((1 + δ) ^ 3 - 1) := by
    have : 3 * δ ≤ (1 + δ) ^ 3 - 1 := by nlinarith
    calc 3 * δ ^ 2 * x = δ * x * (3 * δ) := by ring
      _ ≤ _ := by gcongr
  have hW0 : 0 ≤ δ * x * ((1 + δ) ^ 3 - 1) :=
    mul_nonneg (by positivity) (by nlinarith)
  have hbr : 7 / 8 ≤ 1 - ∑ ρ ∈ zbox (7 / 10) (T + 1), (mult ρ : ℝ) * x ^ (ρ.re - 1) := by
    linarith
  have hlow2 : 15 / 8 * (δ ^ 2 * x) ≤ ∑ n ∈ Finset.range (⌊2 * x⌋₊ + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n := by
    have := mul_le_mul_of_nonneg_left hbr hW0
    nlinarith
  have hint : x * (1 + δ) ^ 4 ≤ x + x ^ (1 - η) := by
    have h5δ : (1 + δ) ^ 4 ≤ 1 + 5 * δ := by
      have e : (1 + δ) ^ 4 = 1 + 4 * δ + δ * (6 * δ + 4 * δ ^ 2 + δ ^ 3) := by ring
      have : 6 * δ + 4 * δ ^ 2 + δ ^ 3 ≤ 1 := by nlinarith
      rw [e]; nlinarith
    have : 5 * δ * x = x ^ (1 - η) := by
      rw [hδ, Real.rpow_sub hx0, Real.rpow_one]
      rw [Real.rpow_neg hx0.le]; field_simp
    calc x * (1 + δ) ^ 4 ≤ x * (1 + 5 * δ) := by gcongr
      _ = x + 5 * δ * x := by ring
      _ = x + x ^ (1 - η) := by rw [this]
  set P := (Finset.Ioc m (m + ⌊(m : ℝ) ^ (1 - η)⌋₊)).filter Nat.Prime with hPdef
  have hl2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlx2 : 0 ≤ δ * Real.log (2 * x) := mul_nonneg hδ0.le hl2x
  have hterm : ∀ n ∈ Finset.range (⌊2 * x⌋₊ + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n ≤
        δ * Real.log (2 * x) * ((if n ∈ P then (1 : ℝ) else 0) +
          (if IsPrimePow n ∧ ¬ n.Prime then (1 : ℝ) else 0)) := by
    intro n hn
    have hn2 : (n : ℝ) ≤ 2 * x := by
      have := Finset.mem_range.1 hn
      have h2 : n ≤ ⌊2 * x⌋₊ := by omega
      exact (Nat.cast_le.2 h2).trans (Nat.floor_le (by positivity))
    have hRHS : 0 ≤ δ * Real.log (2 * x) * ((if n ∈ P then (1 : ℝ) else 0) +
          (if IsPrimePow n ∧ ¬ n.Prime then (1 : ℝ) else 0)) := by
      apply mul_nonneg hlx2; split_ifs <;> norm_num
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_mul]; exact hRHS
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log (2 * x) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnR hn2)
    have hg := gw_le hx0 hδ0 hnR
    have hbase : (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n ≤ δ * Real.log (2 * x) := by
      rcases le_or_gt 0 (gw x δ n) with hg' | hg'
      · calc (ArithmeticFunction.vonMangoldt n : ℝ) * gw x δ n ≤ Real.log (2 * x) * δ :=
              mul_le_mul hΛ hg hg' hl2x
          _ = δ * Real.log (2 * x) := by ring
      · nlinarith
    by_cases hin : x < n ∧ (n : ℝ) < x * (1 + δ) ^ 4
    · by_cases hpr : n.Prime
      · have hnP : n ∈ P := by
          rw [hPdef, Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨?_, ?_⟩, hpr⟩
          · have h1 : ((m : ℕ) : ℝ) < (n : ℝ) := hxdef ▸ hin.1
            exact_mod_cast h1
          · have h1 : (n : ℝ) < m + (m : ℝ) ^ (1 - η) := by
              have := hin.2; rw [← hxdef]; linarith
            have hmn : m ≤ n := by
              have : ((m : ℕ) : ℝ) < (n : ℝ) := hxdef ▸ hin.1
              exact_mod_cast this.le
            have h2 : ((n - m : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 - η) := by
              rw [Nat.cast_sub hmn]; linarith
            have h3 : n - m ≤ ⌊(m : ℝ) ^ (1 - η)⌋₊ := Nat.le_floor h2
            omega
        rw [if_pos hnP]
        have : (0 : ℝ) ≤ (if IsPrimePow n ∧ ¬ n.Prime then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        nlinarith
      · by_cases hpp : IsPrimePow n
        · rw [if_pos (show IsPrimePow n ∧ ¬ n.Prime from ⟨hpp, hpr⟩)]
          have : (0 : ℝ) ≤ (if n ∈ P then (1 : ℝ) else 0) := by split_ifs <;> norm_num
          nlinarith
        · rw [← ArithmeticFunction.vonMangoldt_ne_zero_iff, not_not] at hpp
          rw [hpp, zero_mul]; exact hRHS
    · rw [not_and_or, not_lt, not_lt] at hin
      have hg0 : gw x δ n = 0 := by
        rcases hin with h | h
        · exact gw_zero_left hx0 hδ0 hnR h
        · exact gw_zero_right hx0 hδ0 hnR h
      rw [hg0, mul_zero]; exact hRHS
  have hup := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole] at hup
  have hPsub : (((Finset.range (⌊2 * x⌋₊ + 1)).filter (fun n => n ∈ P)).card : ℝ) ≤
      (P.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (fun n hn => (Finset.mem_filter.1 hn).2)
  have hcard := card_pp_le ⌊2 * x⌋₊
  have hN : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by positivity)
  have hNpos : 0 < ⌊2 * x⌋₊ := Nat.floor_pos.2 (by linarith)
  have hsq : (Nat.sqrt ⌊2 * x⌋₊ : ℝ) ≤ Real.sqrt (2 * x) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have := Nat.sqrt_le' ⌊2 * x⌋₊
    calc (Nat.sqrt ⌊2 * x⌋₊ : ℝ) ^ 2 = ((Nat.sqrt ⌊2 * x⌋₊ ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ 2 * x := hN
  have hlg : (Nat.log 2 ⌊2 * x⌋₊ : ℝ) ≤ Real.log (2 * x) / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have h := Nat.pow_log_le_self 2 hNpos.ne'
    have h' : ((2 : ℝ) ^ Nat.log 2 ⌊2 * x⌋₊) ≤ 2 * x := by
      calc ((2 : ℝ) ^ Nat.log 2 ⌊2 * x⌋₊) = ((2 ^ Nat.log 2 ⌊2 * x⌋₊ : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊2 * x⌋₊ : ℝ) := by exact_mod_cast h
        _ ≤ 2 * x := hN
    have := Real.log_le_log (by positivity) h'
    rw [Real.log_pow] at this
    linarith
  have hcardR : (((Finset.range (⌊2 * x⌋₊ + 1)).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ) ≤
      (Real.sqrt (2 * x) + 1) * (Real.log (2 * x) / Real.log 2 + 1) := by
    calc _ ≤ (((Nat.sqrt ⌊2 * x⌋₊ + 1) * (Nat.log 2 ⌊2 * x⌋₊ + 1) : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ = ((Nat.sqrt ⌊2 * x⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊2 * x⌋₊ : ℝ) + 1) := by push_cast; ring
      _ ≤ _ := by gcongr
  have hδx : δ * x = x ^ (1 - η) / 5 := by
    rw [hδ, Real.rpow_sub hx0, Real.rpow_one, Real.rpow_neg hx0.le]; field_simp
  -- `log (2x) · #pp < δ x`
  have hppb : Real.log (2 * x) * (((Finset.range (⌊2 * x⌋₊ + 1)).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ) < δ * x := by
    rw [hδx]
    calc _ ≤ Real.log (2 * x) * ((Real.sqrt (2 * x) + 1) * (Real.log (2 * x) / Real.log 2 + 1)) :=
          mul_le_mul_of_nonneg_left hcardR hl2x
      _ < _ := h9
  -- `log (2x) · #P ≥ (7/8) δ x`
  have hmain : 7 / 8 * (δ * x) ≤ Real.log (2 * x) * (P.card : ℝ) := by
    have h1 : 15 / 8 * (δ ^ 2 * x) ≤ δ * Real.log (2 * x) *
        ((P.card : ℝ) + (((Finset.range (⌊2 * x⌋₊ + 1)).filter
          (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ)) := by
      refine hlow2.trans (hup.trans ?_)
      apply mul_le_mul_of_nonneg_left _ hlx2
      linarith
    have h2 : 15 / 8 * (δ * x) ≤ Real.log (2 * x) *
        ((P.card : ℝ) + (((Finset.range (⌊2 * x⌋₊ + 1)).filter
          (fun n => IsPrimePow n ∧ ¬ n.Prime)).card : ℝ)) := by
      have e : 15 / 8 * (δ ^ 2 * x) = δ * (15 / 8 * (δ * x)) := by ring
      rw [e, mul_assoc] at h1
      exact le_of_mul_le_mul_left h1 hδ0
    nlinarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith [Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ x)]
  show 1 / 12 * (m : ℝ) ^ (1 - η) / Real.log m ≤ (P.card : ℝ)
  rw [← hxdef, div_le_iff₀ hlogx]
  have hPc : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hxp : 0 ≤ x ^ (1 - η) := by positivity
  nlinarith

theorem hoheisel : Hoheisel := by
  obtain ⟨θ, hθ, c, hc, M0, h⟩ := hoheisel_count
  refine ⟨θ, hθ, max M0 3, fun m hm => ?_⟩
  have hm3 : 3 ≤ m := le_of_max_le_right hm
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hpos : 0 < c * (m : ℝ) ^ θ / Real.log m :=
    div_pos (mul_pos hc (by positivity)) (Real.log_pos (by linarith))
  have hcard := (hpos.trans_le (h m (le_of_max_le_left hm)))
  have hne : ((Finset.Ioc m (m + ⌊(m : ℝ) ^ θ⌋₊)).filter Nat.Prime).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hcard
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, hp.1.1, ?_⟩
  have h1 : (p : ℝ) ≤ (m : ℝ) + (⌊(m : ℝ) ^ θ⌋₊ : ℝ) := by exact_mod_cast hp.1.2
  have h2 : (⌊(m : ℝ) ^ θ⌋₊ : ℝ) ≤ (m : ℝ) ^ θ := Nat.floor_le (by positivity)
  linarith


end OMAHoheisel

end


/-!
# Erdős 32 (`erdos_32.variants.log_squared`), conditional on Hoheisel (counting form)

Erdős (1954): there is an additive complement `A` of the primes with `|A ∩ [1,N]| ≪ log² N`.

Route (Erdős's idea, own write-up):
* Hypothesis `HoheiselCount`: `#{primes in (m, m + ⌊m^θ⌋]} ≥ c m^θ / log m` for large `m`.
  Chaining these windows gives `#{primes in (u, u+d]} ≥ c/log Y · (d - Y^θ)` for `u + d ≤ Y`.
* Exponent stages `a_{j+1} = a_j + ⌊a_j/(2q)⌋` (with `θ ≤ 1 - 1/q`). Stage `j` covers
  `n ∈ [2^{a_j}, 2^{a_{j+1}})` with shifts from `[M, 2M)`, `M = 2^{a_j - 2}`: every such `n`
  has `≥ δ M` good shifts (`n - x` prime), `δ ≍ 1/a_{j+1}`, so a counting (union bound) argument
  over `t = K (a_{j+1}+1)²` shift tuples finds a set of `t` shifts covering the whole stage.
* `a_j` grows geometrically, so `Σ_{a_j ≲ log N} a_j² ≪ log² N`.

The existence-only form of Hoheisel (one prime per window) is not enough for this route:
it gives no density of primes in `(n - 2M, n - M]`.
-/

namespace OMA32

open Real Filter Asymptotics

/-- Hoheisel's theorem in counting form: `≫ m^θ / log m` primes in `(m, m + m^θ]`. -/
def HoheiselCount : Prop :=
  ∃ θ : ℝ, θ < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m →
    c * (m : ℝ) ^ θ / Real.log m ≤
      (((Finset.Ioc m (m + ⌊(m : ℝ) ^ θ⌋₊)).filter Nat.Prime).card : ℝ)

/-- Number of primes in `(u, v]`. -/
def pc (u v : ℕ) : ℕ := ((Finset.Ioc u v).filter Nat.Prime).card

lemma pc_add {u v w : ℕ} (h1 : u ≤ v) (h2 : v ≤ w) : pc u w = pc u v + pc v w := by
  unfold pc
  rw [← Finset.Ioc_union_Ioc_eq_Ioc h1 h2, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)

/-- Chaining Hoheisel windows: primes in `(u, u + d]` when `u + d ≤ Y`. -/
lemma dens {θ c : ℝ} {M0 : ℕ} (hc : 0 < c) (hθ : 0 ≤ θ)
    (hM : ∀ m : ℕ, M0 ≤ m → c * (m : ℝ) ^ θ / Real.log m ≤ (pc m (m + ⌊(m : ℝ) ^ θ⌋₊) : ℝ))
    (Y : ℕ) : ∀ d u : ℕ, M0 ≤ u → 2 ≤ u → u + d ≤ Y →
      c / Real.log Y * ((d : ℝ) - (Y : ℝ) ^ θ) ≤ (pc u (u + d) : ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro u hu0 hu2 hY
  have hu2' : (2 : ℝ) ≤ u := by exact_mod_cast hu2
  have hYu : (u : ℝ) ≤ Y := by exact_mod_cast (by omega : u ≤ Y)
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogY : Real.log u ≤ Real.log Y := Real.log_le_log (by linarith) hYu
  have hκ : 0 ≤ c / Real.log Y := div_nonneg hc.le (by linarith)
  have hpow : (u : ℝ) ^ θ ≤ (Y : ℝ) ^ θ := Real.rpow_le_rpow (by linarith) hYu hθ
  obtain ⟨s, hs⟩ : ∃ s, s = ⌊(u : ℝ) ^ θ⌋₊ := ⟨_, rfl⟩
  have hsle : (s : ℝ) ≤ (u : ℝ) ^ θ := by
    rw [hs]; exact Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have h1 := hM u hu0
  rw [← hs] at h1
  by_cases hsd : s ≤ d
  · have hpos : 0 < c * (u : ℝ) ^ θ / Real.log u :=
      div_pos (mul_pos hc (Real.rpow_pos_of_pos (by linarith) _)) hlogu
    have hs1 : 1 ≤ s := by
      by_contra h0
      have hs0 : s = 0 := by omega
      have hz : pc u (u + s) = 0 := by rw [hs0]; simp [pc]
      rw [hz] at h1
      push_cast at h1
      linarith
    have ih' := ih (d - s) (by omega) (u + s) (by omega) (by omega) (by omega)
    rw [show u + s + (d - s) = u + d by omega, Nat.cast_sub hsd] at ih'
    rw [pc_add (show u ≤ u + s by omega) (show u + s ≤ u + d by omega)]
    have h2 : c / Real.log Y * s ≤ c * (u : ℝ) ^ θ / Real.log u := by
      calc c / Real.log Y * s = c * s / Real.log Y := by ring
        _ ≤ c * (u : ℝ) ^ θ / Real.log Y :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsle hc.le)
            (le_of_lt (lt_of_lt_of_le hlogu hlogY))
        _ ≤ c * (u : ℝ) ^ θ / Real.log u :=
          div_le_div_of_nonneg_left (by positivity) hlogu hlogY
    have h3 : c / Real.log Y * ((d : ℝ) - (Y : ℝ) ^ θ) =
        c / Real.log Y * s + c / Real.log Y * (((d : ℝ) - s) - (Y : ℝ) ^ θ) := by ring
    push_cast
    linarith
  · have hds : (d : ℝ) + 1 ≤ s := by exact_mod_cast (by omega : d + 1 ≤ s)
    have hneg : (d : ℝ) - (Y : ℝ) ^ θ ≤ 0 := by linarith
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hκ hneg) (Nat.cast_nonneg _)

/-- Union-bound covering: if every target has a `δ` fraction of good shifts in `R`, and
`|T| (1-δ)^t < 1`, then some `t` shifts from `R` cover every target. -/
lemma cover (T R : Finset ℕ) (good : ℕ → ℕ → Prop) [∀ n, DecidablePred (good n)]
    (δ : ℝ) (t : ℕ) (hR : 0 < R.card)
    (hg : ∀ n ∈ T, δ * R.card ≤ ((R.filter (good n)).card : ℝ))
    (hsm : (T.card : ℝ) * (1 - δ) ^ t < 1) :
    ∃ f : Fin t → ℕ, (∀ i, f i ∈ R) ∧ ∀ n ∈ T, ∃ i, good n (f i) := by
  by_contra hcon
  push Not at hcon
  have hsub : Fintype.piFinset (fun _ : Fin t => R) ⊆
      T.biUnion (fun n => Fintype.piFinset (fun _ : Fin t => R.filter (fun a => ¬ good n a))) := by
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    obtain ⟨n, hn, hb⟩ := hcon f hf
    rw [Finset.mem_biUnion]
    refine ⟨n, hn, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_filter]
    exact ⟨hf i, hb i⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  simp only [Fintype.card_piFinset_const] at hcard
  have hbad : ∀ n ∈ T, ((R.filter (fun a => ¬ good n a)).card : ℝ) ≤ (1 - δ) * R.card := by
    intro n hn
    have h1 := Finset.card_filter_add_card_filter_not (s := R) (p := good n)
    have h2 := hg n hn
    have h3 : ((R.filter (good n)).card : ℝ) + (R.filter (fun a => ¬ good n a)).card =
        R.card := by exact_mod_cast h1
    linarith
  have hR' : (0 : ℝ) < R.card := by exact_mod_cast hR
  have key : ((R.card ^ t : ℕ) : ℝ) ≤
      ∑ n ∈ T, (((R.filter (fun a => ¬ good n a)).card ^ t : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have key2 : ∑ n ∈ T, (((R.filter (fun a => ¬ good n a)).card ^ t : ℕ) : ℝ) ≤
      ∑ n ∈ T, ((1 - δ) * R.card) ^ t := by
    apply Finset.sum_le_sum
    intro n hn
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hbad n hn) t
  rw [Finset.sum_const, nsmul_eq_mul, mul_pow] at key2
  push_cast at key key2
  have hp : 0 < (R.card : ℝ) ^ t := pow_pos hR' t
  have : (T.card : ℝ) * ((1 - δ) ^ t * (R.card : ℝ) ^ t) < (R.card : ℝ) ^ t := by
    calc (T.card : ℝ) * ((1 - δ) ^ t * (R.card : ℝ) ^ t)
        = ((T.card : ℝ) * (1 - δ) ^ t) * (R.card : ℝ) ^ t := by ring
      _ < 1 * (R.card : ℝ) ^ t := mul_lt_mul_of_pos_right hsm hp
      _ = (R.card : ℝ) ^ t := one_mul _
  linarith

/-- Exponent stages. -/
def seqA (q A0 : ℕ) : ℕ → ℕ
  | 0 => A0
  | j + 1 => seqA q A0 j + seqA q A0 j / (2 * q)

lemma seqA_ge {q A0 : ℕ} (hq : 1 ≤ q) (hA : 2 * q ≤ A0) (j : ℕ) : A0 + j ≤ seqA q A0 j := by
  induction j with
  | zero => simp [seqA]
  | succ j ih =>
    have h1 : 1 ≤ seqA q A0 j / (2 * q) :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    simp only [seqA]
    omega

lemma seqA_le2 (q A0 j : ℕ) : seqA q A0 (j + 1) ≤ 2 * seqA q A0 j := by
  simp only [seqA]
  have := Nat.div_le_self (seqA q A0 j) (2 * q)
  omega

lemma seqA_ratio {q A0 : ℕ} (hq : 1 ≤ q) (hA : 4 * q ≤ A0) (j : ℕ) :
    (4 * q + 1) * seqA q A0 j ≤ 4 * q * seqA q A0 (j + 1) := by
  have hge := seqA_ge hq (by omega : 2 * q ≤ A0) j
  simp only [seqA]
  have h1 := Nat.div_add_mod (seqA q A0 j) (2 * q)
  have h2 := Nat.mod_lt (seqA q A0 j) (show 2 * q > 0 by omega)
  nlinarith

lemma seqA_sum {q A0 : ℕ} (hq : 1 ≤ q) (hA : 4 * q ≤ A0) (J : ℕ) :
    ∑ i ∈ Finset.range (J + 1), (seqA q A0 i) ^ 2 ≤ (4 * q + 1) * (seqA q A0 J) ^ 2 := by
  induction J with
  | zero => simp; nlinarith
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hr := seqA_ratio hq hA J
    have h1 : (4 * q + 1) ^ 2 * (seqA q A0 J) ^ 2 ≤ (4 * q) ^ 2 * (seqA q A0 (J + 1)) ^ 2 := by
      rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left hr 2
    have h2 : (4 * q) * ((4 * q + 1) * (seqA q A0 J) ^ 2) ≤
        (4 * q) * (4 * q * (seqA q A0 (J + 1)) ^ 2) := by nlinarith [h1]
    have h3 := Nat.le_of_mul_le_mul_left h2 (by omega)
    nlinarith [ih, h3]

lemma seqA_sum_real {q A0 : ℕ} (hq : 1 ≤ q) (hA : 4 * q ≤ A0) (F : Finset ℕ) (X : ℝ)
    (hF : ∀ j ∈ F, (seqA q A0 j : ℝ) ≤ X) :
    ∑ j ∈ F, (seqA q A0 j : ℝ) ^ 2 ≤ (4 * q + 1) * X ^ 2 := by
  rcases F.eq_empty_or_nonempty with h | h
  · subst h; simp; positivity
  · set J := F.max' h
    have hsub : F ⊆ Finset.range (J + 1) := by
      intro j hj; rw [Finset.mem_range]; have := F.le_max' j hj; omega
    have h1 : ∑ j ∈ F, (seqA q A0 j : ℝ) ^ 2 ≤ ∑ j ∈ Finset.range (J + 1), (seqA q A0 j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h2 : ((∑ i ∈ Finset.range (J + 1), (seqA q A0 i) ^ 2 : ℕ) : ℝ) ≤
        (((4 * q + 1) * (seqA q A0 J) ^ 2 : ℕ) : ℝ) := by exact_mod_cast seqA_sum hq hA J
    push_cast at h2
    have hJ : (seqA q A0 J : ℝ) ≤ X := hF J (F.max'_mem h)
    have h0 : (0 : ℝ) ≤ seqA q A0 J := Nat.cast_nonneg _
    have h3 : (seqA q A0 J : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ h0 hJ 2
    have h4 : (0 : ℝ) ≤ 4 * q + 1 := by positivity
    nlinarith

/-- One stage of the construction. -/
lemma stage {θ c : ℝ} {M0 q K : ℕ} (hc : 0 < c) (hc1 : c ≤ 1) (hθ : 0 ≤ θ) (hq : 1 ≤ q)
    (hθq : (q : ℝ) * θ ≤ q - 1) (hK : 2 / c ≤ K)
    (hM : ∀ m : ℕ, M0 ≤ m → c * (m : ℝ) ^ θ / Real.log m ≤ (pc m (m + ⌊(m : ℝ) ^ θ⌋₊) : ℝ))
    (a b : ℕ) (ha : 8 * q ≤ a) (ha0 : M0 + 3 ≤ a) (hb : b = a + a / (2 * q)) :
    ∃ S : Finset ℕ, S.card ≤ K * (b + 1) ^ 2 ∧ (∀ x ∈ S, 2 ^ (a - 2) ≤ x) ∧
      ∀ n, 2 ^ a ≤ n → n < 2 ^ b → ∃ x ∈ S, x ≤ n ∧ (n - x).Prime := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ (a - 2) := ⟨_, rfl⟩
  have h4 : 2 ^ a = 4 * M := by
    rw [hMdef, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hMa : a ≤ 2 * M := by
    have h5 := (a - 1).lt_two_pow_self
    have h6 : 2 ^ (a - 1) = 2 * M := by
      rw [hMdef, ← pow_succ']; congr 1; omega
    omega
  have hMpos : 0 < M := by omega
  have hab : a ≤ b := by rw [hb]; exact Nat.le_add_right _ _
  -- exponent inequality
  have hexp : ((b : ℝ) + 1) * θ ≤ (a : ℝ) - 3 := by
    obtain ⟨X, hX⟩ : ∃ X, X = a / (2 * q) := ⟨_, rfl⟩
    have hX1 : X * (2 * q) ≤ a := by rw [hX]; exact Nat.div_mul_le_self a (2 * q)
    have hX1' : (X : ℝ) * (2 * q) ≤ a := by exact_mod_cast hX1
    have hbX : (b : ℝ) = a + X := by rw [hb, ← hX]; push_cast; ring
    have ha' : (8 : ℝ) * q ≤ a := by exact_mod_cast ha
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    have k1 : ((b : ℝ) + 1) * ((q : ℝ) - 1) ≤ ((a : ℝ) - 3) * q := by
      rw [hbX]; nlinarith
    have k2 : ((b : ℝ) + 1) * ((q : ℝ) * θ) ≤ ((b : ℝ) + 1) * ((q : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hθq (by positivity)
    have k3 : (((b : ℝ) + 1) * θ) * q ≤ ((a : ℝ) - 3) * q := by nlinarith
    exact le_of_mul_le_mul_right k3 (by linarith)
  -- parameters
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = c / (2 * ((b : ℝ) + 1) * Real.log 2) := ⟨_, rfl⟩
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hden : 0 < 2 * ((b : ℝ) + 1) * Real.log 2 := by positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hden]; nlinarith
  obtain ⟨t, ht⟩ : ∃ t, t = K * (b + 1) ^ 2 := ⟨_, rfl⟩
  have hKc : 2 ≤ (K : ℝ) * c := by rw [div_le_iff₀ hc] at hK; linarith
  have htδ : (b : ℝ) + 1 ≤ t * δ := by
    have e : (t : ℝ) * δ = ((K : ℝ) * c) * ((b : ℝ) + 1) / (2 * Real.log 2) := by
      rw [hδ, ht]; push_cast; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  -- covering
  have hcov := cover (Finset.Ico (2 ^ a) (2 ^ b)) (Finset.Ico M (2 * M))
    (fun n x => (n - x).Prime) δ t (by rw [Nat.card_Ico]; omega) ?_ ?_
  · obtain ⟨f, hfR, hfc⟩ := hcov
    refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
    · rw [← ht]
      exact Finset.card_image_le.trans (by simp)
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      have := hfR i
      rw [Finset.mem_Ico] at this
      omega
    · intro n hn1 hn2
      obtain ⟨i, hi⟩ := hfc n (Finset.mem_Ico.2 ⟨hn1, hn2⟩)
      have := hfR i
      rw [Finset.mem_Ico] at this
      exact ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i), by omega, hi⟩
  · -- density of good shifts
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hcardR : ((Finset.Ico M (2 * M)).card : ℝ) = M := by
      rw [Nat.card_Ico]; push_cast [show 2 * M - M = M by omega]; ring
    have heq : ((Finset.Ico M (2 * M)).filter (fun x => (n - x).Prime)).card =
        pc (n - 2 * M) (n - 2 * M + M) := by
      unfold pc
      refine Finset.card_bij' (fun x _ => n - x) (fun p _ => n - p) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hx ⊢
        exact ⟨⟨by omega, by omega⟩, hx.2⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hp ⊢
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [show n - (n - p) = p by omega]; exact hp.2
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ico] at hx
        omega
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
        omega
    rw [hcardR, heq]
    have hd := dens hc hθ hM (2 * n) M (n - 2 * M) (by omega) (by omega) (by omega)
    -- bounds
    have hn2 : (2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * n)
    have hnb : ((2 * n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (b + 1) := by
      exact_mod_cast (by rw [pow_succ]; omega : 2 * n ≤ 2 ^ (b + 1))
    have hlog : Real.log ((2 * n : ℕ) : ℝ) ≤ ((b : ℝ) + 1) * Real.log 2 := by
      calc Real.log ((2 * n : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (b + 1)) :=
            Real.log_le_log (by linarith) hnb
        _ = ((b : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have hlogpos : 0 < Real.log ((2 * n : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hMr : (M : ℝ) = (2 : ℝ) ^ ((a : ℝ) - 2) := by
      rw [hMdef]; push_cast
      rw [show (a : ℝ) - 2 = ((a - 2 : ℕ) : ℝ) by push_cast [Nat.cast_sub (by omega : 2 ≤ a)]; ring,
        Real.rpow_natCast]
    have hpowb : ((2 * n : ℕ) : ℝ) ^ θ ≤ (M : ℝ) / 2 := by
      calc ((2 * n : ℕ) : ℝ) ^ θ ≤ ((2 : ℝ) ^ (b + 1)) ^ θ :=
            Real.rpow_le_rpow (by linarith) hnb hθ
        _ = (2 : ℝ) ^ (((b : ℝ) + 1) * θ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
        _ ≤ (2 : ℝ) ^ ((a : ℝ) - 3) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (M : ℝ) / 2 := by
            rw [hMr, show (a : ℝ) - 3 = ((a : ℝ) - 2) - 1 by ring,
              Real.rpow_sub (by norm_num), Real.rpow_one]
    have hκ : c / (((b : ℝ) + 1) * Real.log 2) ≤ c / Real.log ((2 * n : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hc.le hlogpos hlog
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hA : (M : ℝ) / 2 ≤ (M : ℝ) - ((2 * n : ℕ) : ℝ) ^ θ := by linarith
    have hm : c / (((b : ℝ) + 1) * Real.log 2) * ((M : ℝ) / 2) ≤
        c / Real.log ((2 * n : ℕ) : ℝ) * ((M : ℝ) - ((2 * n : ℕ) : ℝ) ^ θ) :=
      mul_le_mul hκ hA (by positivity) (div_nonneg hc.le hlogpos.le)
    have he : δ * M = c / (((b : ℝ) + 1) * Real.log 2) * ((M : ℝ) / 2) := by
      rw [hδ]; field_simp
    rw [he]
    exact hm.trans hd
  · -- union bound
    have hT : ((Finset.Ico (2 ^ a) (2 ^ b)).card : ℝ) ≤ (2 : ℝ) ^ b := by
      rw [Nat.card_Ico]
      exact_mod_cast (Nat.sub_le _ _)
    have h1 : (1 - δ) ^ t ≤ Real.exp (-(t * δ)) := by
      calc (1 - δ) ^ t ≤ (Real.exp (-δ)) ^ t :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ)]) t
        _ = Real.exp (-(t * δ)) := by rw [← Real.exp_nat_mul]; ring_nf
    have h2b : (2 : ℝ) ^ b = Real.exp (b * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h3 : (2 : ℝ) ^ b * Real.exp (-(t * δ)) < 1 := by
      rw [h2b, ← Real.exp_add, show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
      nlinarith
    calc ((Finset.Ico (2 ^ a) (2 ^ b)).card : ℝ) * (1 - δ) ^ t
        ≤ (2 : ℝ) ^ b * Real.exp (-(t * δ)) :=
          mul_le_mul hT h1 (pow_nonneg (by linarith) t) (by positivity)
      _ < 1 := h3

open scoped Classical in
theorem erdos32_log_squared_of_hoheisel (h : HoheiselCount) : ∃ A : Set ℕ,
    Erdos32.IsAdditiveComplementToPrimes A ∧
    (fun N => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) =O[atTop]
      fun N => (Real.log N) ^ 2 := by
  obtain ⟨θ, hθ1, c0, hc0, M0, hM⟩ := h
  -- θ ≥ 0
  have hθ : 0 ≤ θ := by
    by_contra hneg
    push Not at hneg
    have h1 := hM (M0 + 2) (by omega)
    have hm : (1 : ℝ) < ((M0 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < M0 + 2)
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hm hneg
    have hfl : ⌊((M0 + 2 : ℕ) : ℝ) ^ θ⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt
    rw [hfl, add_zero, Finset.Ioc_self] at h1
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero] at h1
    have : 0 < c0 * ((M0 + 2 : ℕ) : ℝ) ^ θ / Real.log ((M0 + 2 : ℕ) : ℝ) :=
      div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (by linarith) _)) (Real.log_pos hm)
    linarith
  -- c ≤ 1
  obtain ⟨c, hcdef⟩ : ∃ c, c = min c0 1 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min hc0 one_pos
  have hc1 : c ≤ 1 := by rw [hcdef]; exact min_le_right _ _
  have hM' : ∀ m : ℕ, M0 ≤ m →
      c * (m : ℝ) ^ θ / Real.log m ≤ (pc m (m + ⌊(m : ℝ) ^ θ⌋₊) : ℝ) := by
    intro m hm
    refine le_trans ?_ (hM m hm)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by rw [hcdef]; exact min_le_left _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.log_natCast_nonneg m)
  -- q with θ ≤ 1 - 1/q
  obtain ⟨q0, hq0⟩ := exists_nat_ge (1 / (1 - θ))
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = q0 + 1 := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by omega
  have hθQ : (Q : ℝ) * θ ≤ Q - 1 := by
    have h1 : 0 < 1 - θ := by linarith
    have h2 : 1 / (1 - θ) ≤ Q := by rw [hQ]; push_cast; linarith
    rw [div_le_iff₀ h1] at h2
    linarith
  obtain ⟨K, hK⟩ := exists_nat_ge (2 / c)
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = 8 * Q + M0 + 3 := ⟨_, rfl⟩
  have hst : ∀ j, ∃ S : Finset ℕ, S.card ≤ K * (seqA Q A0 (j + 1) + 1) ^ 2 ∧
      (∀ x ∈ S, 2 ^ (seqA Q A0 j - 2) ≤ x) ∧
      ∀ n, 2 ^ (seqA Q A0 j) ≤ n → n < 2 ^ (seqA Q A0 (j + 1)) →
        ∃ x ∈ S, x ≤ n ∧ (n - x).Prime := by
    intro j
    have hge := seqA_ge hQ1 (by omega : 2 * Q ≤ A0) j
    exact stage hc hc1 hθ hQ1 hθQ hK hM' (seqA Q A0 j) (seqA Q A0 (j + 1))
      (by omega) (by omega) rfl
  choose S hScard hSlow hScov using hst
  refine ⟨{x | ∃ j, x ∈ S j}, ?_, ?_⟩
  · -- every large n is p + a
    rw [Erdos32.IsAdditiveComplementToPrimes, eventually_atTop]
    refine ⟨2 ^ A0, fun n hn => ?_⟩
    have hex : ∃ j, n < 2 ^ (seqA Q A0 (j + 1)) := by
      refine ⟨n, lt_of_lt_of_le n.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) ?_)⟩
      have := seqA_ge hQ1 (by omega : 2 * Q ≤ A0) (n + 1)
      omega
    have hlt := Nat.find_spec hex
    have hlo : 2 ^ (seqA Q A0 (Nat.find hex)) ≤ n := by
      rcases hj : Nat.find hex with _ | i
      · simp only [seqA]; exact hn
      · have := Nat.find_min hex (show i < Nat.find hex by omega)
        push Not at this
        exact this
    obtain ⟨x, hxS, hxn, hp⟩ := hScov (Nat.find hex) n hlo hlt
    exact ⟨n - x, hp, x, ⟨Nat.find hex, hxS⟩, by omega⟩
  · -- counting
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hl2' : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    apply Asymptotics.IsBigO.of_bound
      (9 * K * (4 * Q + 1) * (1 / Real.log 2 + 2) ^ 2)
    rw [eventually_atTop]
    refine ⟨3, fun N hN => ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    set F := (Finset.range (N + 3)).filter (fun j => 2 ^ (seqA Q A0 j - 2) ≤ N) with hF
    have hsub : (Finset.Icc 1 N).filter (· ∈ {x | ∃ j, x ∈ S j}) ⊆ F.biUnion S := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨⟨-, hxN⟩, j, hj⟩ := hx
      rw [Finset.mem_biUnion]
      refine ⟨j, ?_, hj⟩
      have hlow := hSlow j x hj
      have hge := seqA_ge hQ1 (by omega : 2 * Q ≤ A0) j
      have h2 := (seqA Q A0 j - 2).lt_two_pow_self
      rw [hF, Finset.mem_filter, Finset.mem_range]
      omega
    have hc1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hc2 : ∑ j ∈ F, (S j).card ≤ ∑ j ∈ F, 9 * K * (seqA Q A0 j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h1 := hScard j
      have h2 := seqA_le2 Q A0 j
      have hge := seqA_ge hQ1 (by omega : 2 * Q ≤ A0) j
      have h3 : seqA Q A0 (j + 1) + 1 ≤ 3 * seqA Q A0 j := by omega
      have h4 : (seqA Q A0 (j + 1) + 1) ^ 2 ≤ (3 * seqA Q A0 j) ^ 2 := Nat.pow_le_pow_left h3 2
      calc (S j).card ≤ K * (seqA Q A0 (j + 1) + 1) ^ 2 := h1
        _ ≤ K * (3 * seqA Q A0 j) ^ 2 := Nat.mul_le_mul_left K h4
        _ = 9 * K * (seqA Q A0 j) ^ 2 := by ring
    have hcR : (((Finset.Icc 1 N).filter (· ∈ {x | ∃ j, x ∈ S j})).card : ℝ) ≤
        9 * K * ∑ j ∈ F, (seqA Q A0 j : ℝ) ^ 2 := by
      have := hc1.trans hc2
      rw [Finset.mul_sum]
      exact_mod_cast this
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hNpos]
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hX : ∀ j ∈ F, (seqA Q A0 j : ℝ) ≤ Real.log N / Real.log 2 + 2 := by
      intro j hj
      rw [hF, Finset.mem_filter] at hj
      have h1 : ((2 ^ (seqA Q A0 j - 2) : ℕ) : ℝ) ≤ N := by exact_mod_cast hj.2
      push_cast at h1
      have h2 : Real.log ((2 : ℝ) ^ (seqA Q A0 j - 2)) ≤ Real.log N :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      have h3 : ((seqA Q A0 j - 2 : ℕ) : ℝ) ≤ Real.log N / Real.log 2 := by
        rw [le_div_iff₀ (by linarith)]; exact h2
      have h4 : (seqA Q A0 j : ℝ) ≤ ((seqA Q A0 j - 2 : ℕ) : ℝ) + 2 := by
        have : seqA Q A0 j ≤ (seqA Q A0 j - 2) + 2 := by omega
        exact_mod_cast this
      linarith
    have hsum := seqA_sum_real hQ1 (by omega : 4 * Q ≤ A0) F _ hX
    have hXb : Real.log N / Real.log 2 + 2 ≤ (1 / Real.log 2 + 2) * Real.log N := by
      have : Real.log N / Real.log 2 = 1 / Real.log 2 * Real.log N := by ring
      rw [this]; nlinarith
    have hX0 : 0 ≤ Real.log N / Real.log 2 + 2 := by
      have : 0 ≤ Real.log N / Real.log 2 := div_nonneg (by linarith) (by linarith)
      linarith
    have hXsq : (Real.log N / Real.log 2 + 2) ^ 2 ≤ ((1 / Real.log 2 + 2) * Real.log N) ^ 2 :=
      pow_le_pow_left₀ hX0 hXb 2
    have hK0 : (0 : ℝ) ≤ 9 * K := by positivity
    have hQ0 : (0 : ℝ) ≤ 4 * Q + 1 := by positivity
    calc (((Finset.Icc 1 N).filter (· ∈ {x | ∃ j, x ∈ S j})).card : ℝ)
        ≤ 9 * K * ∑ j ∈ F, (seqA Q A0 j : ℝ) ^ 2 := hcR
      _ ≤ 9 * K * ((4 * Q + 1) * (Real.log N / Real.log 2 + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum hK0
      _ ≤ 9 * K * ((4 * Q + 1) * ((1 / Real.log 2 + 2) * Real.log N) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXsq hQ0) hK0
      _ = 9 * K * (4 * Q + 1) * (1 / Real.log 2 + 2) ^ 2 * Real.log N ^ 2 := by ring

end OMA32

theorem OMA.solution : type_of% @Erdos32.erdos_32.variants.log_squared :=
  OMA32.erdos32_log_squared_of_hoheisel OMAHoheisel.hoheisel_count
