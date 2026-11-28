import OMAReductions.R_Erdos768_erdos_768_R1_H1_R1
import Mathlib

-- Step Erdos768.erdos_768.R1.H1.R1.H2 of Erdős Problem 768: from the prime number theorem with error term for psi to the
-- count of primes in a logarithmic interval (Lemma 2.8, elementary passage psi, theta, pi, li and a calculus estimate).
-- Adapted from github.com/ericlisg/erdos768-lean (commit e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9), (c) Eric Li and the
-- contributors of that repository (proofs generated with Aristotle by Harmonic), Apache-2.0 licence. Ported from Lean 4.28.
-- The lemma x_eps_to_inf is from the PrimeNumberTheoremAnd project (github.com/AlexKontorovich/PrimeNumberTheoremAnd), Apache-2.0.
-- The source formalises an unrefereed preprint (arXiv:2606.24872); the argument here is only that source, not new work.
section P

open scoped Classical BigOperators Topology Nat.Prime
open Filter Asymptotics
namespace Erdos768
def MediumPNTStmt : Prop :=
  ∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))
variable [hM : Fact MediumPNTStmt]
include hM
section XE
open Filter Topology Real
omit hM in
lemma x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg),
      zero_rpow (ne_of_lt B_minus_1_neg)]
    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop
  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring
    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx
    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one
  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf
  rw [tendsto_congr' (x_εx_eq c B)]
  exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)
end XE
noncomputable def li2 (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t
lemma errBound_isBigO_of_le {c₁ c₂ : ℝ} (_hc₂ : 0 ≤ c₂) (h : c₂ ≤ c₁) :
    (fun x : ℝ => x * Real.exp (-c₁ * Real.log x ^ ((1 : ℝ) / 10)))
      =O[atTop] (fun x : ℝ => x * Real.exp (-c₂ * Real.log x ^ ((1 : ℝ) / 10))) := by
  refine' Asymptotics.isBigO_iff.mpr _;
  refine' ⟨ 1, _ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx ; rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; norm_num;
  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ Real.rpow_nonneg ( Real.log_nonneg hx ) ( 1 / 10 : ℝ ) ] ) ( by positivity )
lemma one_isBigO_errBound {c : ℝ} (_hc : 0 < c) :
    (fun _ : ℝ => (1 : ℝ))
      =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  have h_tendsto : Filter.Tendsto (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) Filter.atTop Filter.atTop := by
    have := x_ε_to_inf c ( show ( 1 : ℝ ) / 10 < 1 by norm_num );
    convert this using 1 <;> (try rfl);
  rw [ Asymptotics.isBigO_iff ];
  exact ⟨ 1, by filter_upwards [ h_tendsto.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ] ; linarith ⟩
lemma sqrt_mul_log_isBigO_errBound {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => 2 * Real.sqrt x * Real.log x)
      =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  have h_exp : Filter.Tendsto (fun x : ℝ => (2 * Real.sqrt x * Real.log x) / (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) Filter.atTop (nhds 0) := by
    suffices h_simplified : Filter.Tendsto (fun x : ℝ => 2 * Real.log x * Real.exp (Real.log x / 2 - Real.log x + c * (Real.log x) ^ ((1 : ℝ) / 10))) Filter.atTop (nhds 0) by
      refine h_simplified.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx ] ; ring_nf ; norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log hx ] ; ring_nf;
      rw [ ← Real.exp_neg ] ; rw [ Real.exp_neg, Real.exp_mul, Real.exp_log hx ] ; ring_nf;
      rw [ ← Real.sqrt_eq_rpow ] ; rw [ ← Real.sqrt_div_self ] ; ring;
    suffices h_log : Filter.Tendsto (fun y : ℝ => 2 * y * Real.exp (-y / 2 + c * y ^ ((1 : ℝ) / 10))) Filter.atTop (nhds 0) by
      convert h_log.comp ( Real.tendsto_log_atTop ) using 2 <;> (try rfl) ; norm_num ; ring_nf;
      norm_num;
    suffices h_factor : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y / 4)) Filter.atTop (nhds 0) by
      have h_bound : ∃ Y : ℝ, ∀ y > Y, y * Real.exp (-y / 2 + c * y ^ (1 / 10 : ℝ)) ≤ y * Real.exp (-y / 4) := by
        obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ y > Y, c * y ^ (1 / 10 : ℝ) ≤ y / 4 := by
          obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ y > Y, c ≤ y ^ (9 / 10 : ℝ) / 4 := by
            exact ⟨ ( c * 4 ) ^ ( 10 / 9 : ℝ ), fun y hy => by rw [ le_div_iff₀ ( by positivity ) ] ; exact le_trans ( by rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) hy.le ( by positivity ) ) ⟩;
          exact ⟨ Max.max Y 1, fun y hy => by have := hY y ( lt_of_le_of_lt ( le_max_left _ _ ) hy ) ; rw [ show ( 9 / 10 : ℝ ) = 1 - 1 / 10 by norm_num, Real.rpow_sub ( by linarith [ le_max_right Y 1 ] ) ] at this; norm_num at * ; nlinarith [ Real.rpow_pos_of_pos ( by linarith [ le_max_right Y 1 ] : 0 < y ) ( 1 / 10 : ℝ ), mul_div_cancel₀ ( y : ℝ ) ( ne_of_gt ( Real.rpow_pos_of_pos ( by linarith [ le_max_right Y 1 ] : 0 < y ) ( 1 / 10 : ℝ ) ) ) ] ⟩;
        exact ⟨ Max.max Y 1, fun y hy => mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith [ hY y <| lt_of_le_of_lt ( le_max_left _ _ ) hy ] ) <| by linarith [ le_max_right Y 1 ] ⟩;
      refine' squeeze_zero_norm' _ ( by simpa using h_factor.const_mul 2 );
      filter_upwards [ Filter.eventually_gt_atTop h_bound.choose, Filter.eventually_gt_atTop 0 ] with y hy₁ hy₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; linarith [ h_bound.choose_spec y hy₁ ] ;
    suffices h_lim_z : Filter.Tendsto (fun z : ℝ => 4 * z * Real.exp (-z)) Filter.atTop (nhds 0) by
      convert h_lim_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 4 : ℝ ) ⁻¹ ) ) using 2 <;> (try rfl) ; norm_num ; ring_nf;
    simpa [ mul_assoc ] using Filter.Tendsto.const_mul 4 ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
  rw [ Asymptotics.isBigO_iff' ];
  obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp h_exp 1 zero_lt_one;
  refine' ⟨ 1, zero_lt_one, Filter.eventually_atTop.mpr ⟨ Max.max N 2, fun x hx => _ ⟩ ⟩ ; specialize hN x ( le_trans ( le_max_left _ _ ) hx ) ; norm_num at *;
  rw [ div_lt_one ( mul_pos ( abs_pos.mpr ( by linarith ) ) ( Real.exp_pos _ ) ) ] at hN ; linarith
lemma theta_sub_id_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => Chebyshev.theta x - x)
        =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨ c, hc, hψ ⟩ := (Fact.out : MediumPNTStmt);
  refine' ⟨ c, hc, _ ⟩;
  have hθ : (fun x => Chebyshev.theta x - Chebyshev.psi x) =O[atTop] (fun x => 2 * Real.sqrt x * Real.log x) := by
    refine' Asymptotics.IsBigO.of_bound 1 _;
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by rw [ one_mul ] ; exact le_trans ( by simpa [ abs_sub_comm ] using Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx ) ( le_abs_self _ ) ;
  convert hθ.trans ( sqrt_mul_log_isBigO_errBound hc ) |> Asymptotics.IsBigO.add <| hψ using 1 <;> (try rfl);
  aesop
lemma li2_eq_sub_add_integral {x : ℝ} (hx : 2 ≤ x) :
    li2 x = x / Real.log x - 2 / Real.log 2
      + ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
  have h_parts : ∀ t ∈ Set.Icc (2 : ℝ) x, deriv (fun t => t / Real.log t) t = 1 / Real.log t - 1 / (Real.log t)^2 := by
    intro t ht; norm_num [ show t ≠ 0 by linarith [ ht.1 ], show Real.log t ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith [ ht.1 ], Real.differentiableAt_log, div_eq_mul_inv ] ; ring;
  have h_parts : ∫ t in (2:ℝ)..x, deriv (fun t => t / Real.log t) t = (x / Real.log x) - (2 / Real.log 2) := by
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    · rfl;
    · exact fun t ht => DifferentiableAt.div ( differentiableAt_id ) ( Real.differentiableAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) );
    · rw [ Set.uIcc_of_le hx ];
      exact ContinuousOn.congr ( by exact ContinuousOn.sub ( continuousOn_const.div ( Real.continuousOn_log.mono <| by norm_num ) fun t ht => ne_of_gt <| Real.log_pos <| by linarith [ ht.1 ] ) <| continuousOn_const.div ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by norm_num ) 2 ) fun t ht => ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ ht.1 ] ) h_parts
  generalize_proofs at *; (
  rw [ ← h_parts, intervalIntegral.integral_congr fun t ht => ‹∀ t ∈ Set.Icc 2 x, deriv ( fun t => t / Real.log t ) t = 1 / Real.log t - 1 / Real.log t ^ 2› t <| by simpa [ hx ] using ht ] ; ring_nf;
  rw [ intervalIntegral.integral_sub ] <;> norm_num [ li2 ];
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Real.continuousAt_log ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) ) ) ..;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) ) ) ) ..)
lemma primeCounting_sub_li2_eq {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - li2 x
      = (Chebyshev.theta x - x) / Real.log x + 2 / Real.log 2
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) := by
  convert congr_arg₂ ( · - · ) ( Chebyshev.primeCounting_eq_theta_div_log_add_integral hx ) ( li2_eq_sub_add_integral hx ) using 1 <;> (try rfl) ; ring_nf!;
  rw [ intervalIntegral.integral_sub ] ; ring_nf!;
  · congr 1; exact intervalIntegral.integral_congr fun t ht => by by_cases h : t = 0 <;> simp +decide [ h ];
  · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
    have := Chebyshev.integrableOn_theta_div_id_mul_log_sq x; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm ] ;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact ContinuousOn.mul ( ContinuousOn.mul continuousOn_id ( ContinuousOn.inv₀ continuousOn_id fun t ht => by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ContinuousOn.pow ( ContinuousOn.inv₀ ( Real.continuousOn_log.mono <| by norm_num [ hx ] ) fun t ht => ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> linarith ) _ )
lemma sqrt_isBigO_errBound {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.sqrt x)
      =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  have h_sqrt : (fun x => Real.sqrt x) =O[atTop] (fun x => 2 * Real.sqrt x * Real.log x) := by
    rw [ Asymptotics.isBigO_iff ];
    use 1; filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using by rw [ Real.norm_of_nonneg ( Real.sqrt_nonneg x ), Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( Real.sqrt_nonneg x ) ) ( Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] ) ) ) ] ; nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith [ Real.add_one_le_exp 1 ] ), Real.add_one_le_exp 1, Real.log_exp 1, Real.log_le_log ( by positivity ) hx.le ] ;
  exact h_sqrt.trans ( by simpa using sqrt_mul_log_isBigO_errBound hc )
lemma integral_head_isBigO_sqrt :
    (fun x : ℝ => ∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
      =O[atTop] (fun x : ℝ => Real.sqrt x) := by
  refine' Asymptotics.isBigO_iff.mpr _;
  refine' ⟨ ( Real.log 4 + 1 ) / ( Real.log 2 ) ^ 2, _ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop 4 ] with x hx ; norm_num at *;
  have h_bound : ∀ t ∈ Set.Icc 2 (Real.sqrt x), |(Chebyshev.theta t - t) / (t * (Real.log t)^2)| ≤ (Real.log 4 + 1) / (Real.log 2)^2 := by
    intros t ht
    have h_theta_le : Chebyshev.theta t ≤ Real.log 4 * t := by
      exact Chebyshev.theta_le_log4_mul_x ( by linarith [ ht.1 ] )
    have h_abs : |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := by
      rw [ abs_le ];
      constructor <;> nlinarith [ show 0 ≤ Chebyshev.theta t from Chebyshev.theta_nonneg t, show 0 < t from by linarith [ ht.1 ], show 0 < Real.log 4 from Real.log_pos ( by norm_num ) ]
    have h_div : |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ (Real.log 4 + 1) / (Real.log t) ^ 2 := by
      rw [ abs_div, abs_of_nonneg ( show 0 ≤ t * Real.log t ^ 2 by exact mul_nonneg ( by linarith [ ht.1 ] ) ( sq_nonneg _ ) ) ];
      rw [ div_le_div_iff₀ ] <;> nlinarith [ ht.1, ht.2, show 0 < t * Real.log t ^ 2 by exact mul_pos ( by linarith [ ht.1 ] ) ( sq_pos_of_pos ( Real.log_pos ( by linarith [ ht.1 ] ) ) ) ]
    have h_log_bound : Real.log t ≥ Real.log 2 := by
      exact Real.log_le_log ( by norm_num ) ht.1
    have h_final : (Real.log 4 + 1) / (Real.log t) ^ 2 ≤ (Real.log 4 + 1) / (Real.log 2) ^ 2 := by
      gcongr
    exact le_trans h_div h_final;
  rw [ intervalIntegral.integral_of_le ( Real.le_sqrt_of_sq_le ( by linarith ) ) ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun t => ( Real.log 4 + 1 ) / Real.log 2 ^ 2;
  · exact Filter.Eventually.of_forall fun t => norm_nonneg _;
  · norm_num;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_bound t <| Set.Ioc_subset_Icc_self ht;
  · norm_num [ mul_comm, abs_of_nonneg ( Real.sqrt_nonneg x ) ];
    exact mul_le_mul_of_nonneg_left ( max_le_iff.mpr ⟨ by linarith [ Real.sqrt_nonneg x ], by linarith [ Real.sqrt_nonneg x ] ⟩ ) ( by positivity )
lemma integral_tail_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∫ t in Real.sqrt x..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
        =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc⟩ : ∃ c, 0 < c ∧ (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    convert theta_sub_id_isBigO using 1 <;> (try rfl);
  obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ᶠ x in atTop, ∀ t ≥ Real.sqrt x, |(Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ K * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) / (Real.log (Real.sqrt x)) ^ 2 := by
    obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ᶠ x in atTop, ∀ t ≥ Real.sqrt x, |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * (Real.log t) ^ ((1 : ℝ) / 10)) := by
      obtain ⟨K, hKpos, hK⟩ : ∃ K > 0, ∀ᶠ x in atTop, |Chebyshev.theta x - x| ≤ K * x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
        have := hc.2.exists_pos;
        obtain ⟨ K, hK₁, hK₂ ⟩ := this; use K, hK₁; filter_upwards [ hK₂.bound, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂; simp_all +decide [ mul_assoc, abs_of_pos ] ;
      obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp hK;
      exact ⟨ K, hKpos, Filter.eventually_atTop.mpr ⟨ M ^ 2, fun x hx => fun t ht => hM t <| by nlinarith [ Real.sqrt_nonneg x, Real.mul_self_sqrt ( show 0 ≤ x by nlinarith ) ] ⟩ ⟩;
    refine' ⟨ K, hKpos, _ ⟩;
    filter_upwards [ hK, Filter.eventually_gt_atTop 4 ] with x hx₁ hx₂;
    intro t ht
    have h_abs : |Chebyshev.theta t - t| ≤ K * t * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) := by
      refine le_trans ( hx₁ t ht ) ?_;
      exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonpos_left ( Real.rpow_le_rpow ( Real.log_nonneg <| Real.le_sqrt_of_sq_le <| by linarith ) ( Real.log_le_log ( by positivity ) ht ) <| by positivity ) <| by linarith ) <| mul_nonneg hKpos.le <| by linarith [ Real.sqrt_nonneg x ] ;
    rw [ abs_div, abs_of_nonneg ( show 0 ≤ t * Real.log t ^ 2 by exact mul_nonneg ( by linarith [ Real.sqrt_nonneg x ] ) ( sq_nonneg _ ) ) ];
    rw [ div_le_div_iff₀ ];
    · refine le_trans ( mul_le_mul_of_nonneg_right h_abs ( sq_nonneg _ ) ) ?_;
      ring_nf;
      exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg <| Real.le_sqrt_of_sq_le <| by linarith ) ( Real.log_le_log ( Real.sqrt_pos.mpr <| by linarith ) ht ) _ ) <| mul_nonneg ( mul_nonneg hKpos.le <| by linarith [ Real.sqrt_nonneg x ] ) <| Real.exp_nonneg _;
    · exact mul_pos ( by linarith [ Real.sqrt_pos.mpr ( show 0 < x by linarith ) ] ) ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Real.sqrt_pos.mpr ( show 0 < x by linarith ), Real.lt_sqrt_of_sq_lt ( by linarith : 1 ^ 2 < x ) ] ) ) );
    · exact sq_pos_of_pos <| Real.log_pos <| Real.lt_sqrt_of_sq_lt <| by linarith;
  have h_integral_bound : ∀ᶠ x in atTop, |∫ t in (Real.sqrt x)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)| ≤ K * x * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) / (Real.log (Real.sqrt x)) ^ 2 := by
    filter_upwards [ hK, Filter.eventually_gt_atTop 4 ] with x hx hx';
    rw [ intervalIntegral.integral_of_le ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ) ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun t => K * Real.exp ( -c * Real.log ( Real.sqrt x ) ^ ( 1 / 10 : ℝ ) ) / Real.log ( Real.sqrt x ) ^ 2;
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
    · norm_num;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using hx t ht.1.le;
    · norm_num [ mul_assoc, mul_div_assoc ];
      rw [ max_eq_left ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ x by linarith ) ] ) ] ; ring_nf ; norm_num;
      positivity;
  have h_simplify : ∀ᶠ x in atTop, K * x * Real.exp (-c * (Real.log (Real.sqrt x)) ^ ((1 : ℝ) / 10)) / (Real.log (Real.sqrt x)) ^ 2 ≤ (4 * K) * x * Real.exp (-c * (1 / 2) ^ ((1 : ℝ) / 10) * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 2 ) ] with x hx₁ hx₂;
    rw [ Real.log_sqrt ( by positivity ) ] ; ring_nf ; norm_num;
    rw [ Real.mul_rpow ( by linarith [ Real.log_pos hx₁ ] ) ( by linarith [ Real.log_pos hx₁ ] ) ] ; ring_nf ; norm_num;
    exact mul_le_of_le_one_right ( by exact mul_nonneg ( mul_nonneg hKpos.le ( by positivity ) ) ( Real.exp_nonneg _ ) ) ( inv_le_one_of_one_le₀ ( by nlinarith [ Real.log_exp 2, Real.log_le_log ( by positivity ) hx₂.le ] ) );
  refine' ⟨ c * ( 1 / 2 ) ^ ( 1 / 10 : ℝ ), by exact mul_pos hc.1 ( Real.rpow_pos_of_pos ( by norm_num ) _ ), _ ⟩;
  rw [ Asymptotics.isBigO_iff ];
  use 4 * K;
  filter_upwards [ h_integral_bound, h_simplify, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂ hx₃;
  convert hx₁.trans hx₂ using 1 <;> (try rfl) ; norm_num [ abs_of_pos ( zero_lt_one.trans hx₃ ) ] ; ring
lemma integral_theta_sub_id_isBigO :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2))
        =O[atTop] (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc_pos, hc_tail⟩ := integral_tail_isBigO
  use c, hc_pos;
  have h_split : ∀ x ≥ 4, ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) = (∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) + (∫ t in (Real.sqrt x)..x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) := by
    intro x hx
    have h_integrable : IntervalIntegrable (fun t => (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) MeasureTheory.volume 2 x := by
      apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( |Chebyshev.theta t - t| ) / ( 2 * ( Real.log 2 ) ^ 2 );
      · refine' MeasureTheory.Integrable.div_const _ _;
        refine' MeasureTheory.Integrable.abs _;
        refine' MeasureTheory.Integrable.sub _ _;
        · refine' ( MonotoneOn.integrableOn_isCompact _ _ );
          · exact CompactIccSpace.isCompact_Icc;
          · exact fun a ha b hb hab => Chebyshev.theta_mono hab;
        · exact Continuous.integrableOn_Icc ( by continuity );
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.mul _ _;
        · refine' Measurable.sub _ measurable_id;
          refine' measurable_of_tendsto_metrizable _ _;
          use fun n t => ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.floor t)), Real.log p * (if p ≤ n then 1 else 0);
          · fun_prop;
          · refine' tendsto_pi_nhds.mpr _;
            intro x; refine' tendsto_const_nhds.congr' _; filter_upwards [ Filter.eventually_ge_atTop ⌊x⌋₊ ] with i hi; simp +decide [ Finset.sum_ite ] ;
            rw [ Finset.filter_true_of_mem fun p hp => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ] ; rfl;
        · exact Measurable.inv ( measurable_id.mul ( Measurable.pow_const ( Real.measurable_log ) _ ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht;
        rw [ Real.norm_eq_abs, abs_div ];
        gcongr;
        rw [ abs_of_nonneg ( mul_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( sq_nonneg _ ) ) ] ; exact mul_le_mul ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( pow_le_pow_left₀ ( Real.log_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( Real.log_le_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) 2 ) ( by positivity ) ( by cases Set.mem_uIcc.mp ht <;> linarith );
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ h_integrable.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hx ];
    · exact Or.inl <| Real.le_sqrt_of_sq_le (by linarith : (2:ℝ)^2 ≤ x);
    · exact Or.inr ⟨ by linarith, Or.inr (by linarith) ⟩;
    · exact Or.inl <| Real.le_sqrt_of_sq_le (by linarith : (2:ℝ)^2 ≤ x);
    · exact Or.inr (Or.inr (by linarith))
  have h_head : (fun x => ∫ t in (2 : ℝ)..Real.sqrt x, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) =O[atTop] (fun x => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) := by
    exact Asymptotics.IsBigO.trans ( integral_head_isBigO_sqrt ) ( sqrt_isBigO_errBound hc_pos );
  rw [ Asymptotics.isBigO_iff ] at *;
  obtain ⟨ c₁, hc₁ ⟩ := h_head; obtain ⟨ c₂, hc₂ ⟩ := hc_tail; use c₁ + c₂; filter_upwards [ hc₁, hc₂, Filter.eventually_ge_atTop 4 ] with x hx₁ hx₂ hx₃; rw [ h_split x hx₃ ] ; exact le_trans ( norm_add_le _ _ ) ( by nlinarith [ abs_nonneg ( x * Real.exp ( -c * Real.log x ^ ( 1 / 10 : ℝ ) ) ) ] ) ;
theorem pnt_li_error :
    ∃ c : ℝ, 0 < c ∧
      (fun y : ℝ => (Nat.primeCounting ⌊y⌋₊ : ℝ) - li2 y)
        =O[atTop] (fun y : ℝ => y * Real.exp (-c * Real.log y ^ ((1 : ℝ) / 10))) := by
  obtain ⟨ c₁, hc₁_pos, hc₁ ⟩ := theta_sub_id_isBigO
  obtain ⟨ c₂, hc₂_pos, hc₂ ⟩ := integral_theta_sub_id_isBigO
  use min c₁ c₂
  constructor
  · exact lt_min hc₁_pos hc₂_pos
  ·
    have h_combined : (fun y => (Chebyshev.theta y - y) / Real.log y + 2 / Real.log 2 + ∫ t in (2 : ℝ)..y, (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2)) =O[atTop] (fun y => y * Real.exp (-min c₁ c₂ * Real.log y ^ ((1:ℝ)/10))) := by
      refine' Asymptotics.IsBigO.add ( Asymptotics.IsBigO.add _ _ ) _;
      · refine' Asymptotics.IsBigO.trans _ ( hc₁.trans _ );
        · refine' Asymptotics.IsBigO.of_bound 1 _;
          filter_upwards [ Filter.eventually_gt_atTop ( Real.exp 1 ) ] with x hx using by rw [ one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div ] ; exact div_le_self ( abs_nonneg _ ) ( by rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith [ Real.add_one_le_exp 1 ] ) ) ] ; exact Real.le_log_iff_exp_le ( by linarith [ Real.add_one_le_exp 1 ] ) |>.2 <| by linarith [ Real.add_one_le_exp 1 ] ) ;
        · exact errBound_isBigO_of_le ( by positivity ) ( min_le_left _ _ );
      · have := one_isBigO_errBound ( show 0 < min c₁ c₂ by positivity );
        convert this.const_mul_left ( 2 / Real.log 2 ) using 2 <;> (try rfl) ; ring;
      · refine' hc₂.trans _;
        exact errBound_isBigO_of_le ( by positivity ) ( min_le_right _ _ );
    refine' h_combined.congr' _ _;
    · filter_upwards [ Filter.eventually_ge_atTop 2 ] with y hy using by rw [ primeCounting_sub_li2_eq hy ] ;
    · rfl
lemma count_eq_primeCounting_diff (u d : ℝ) (hd : 0 ≤ d) :
    (((Finset.Icc 1 ⌊Real.exp u⌋₊).filter
        (fun p => Nat.Prime p ∧ Real.exp (u - d) < (p : ℝ))).card : ℝ)
      = (Nat.primeCounting ⌊Real.exp u⌋₊ : ℝ)
          - (Nat.primeCounting ⌊Real.exp (u - d)⌋₊ : ℝ) := by
  rw [ eq_sub_iff_add_eq ];
  rw_mod_cast [ Nat.primeCounting, Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  rw [ ← Finset.card_union_of_disjoint ];
  · congr 1 with x ; by_cases hx : x ≤ ⌊Real.exp ( u - d ) ⌋₊ <;> simp_all +decide;
    · exact ⟨ fun h => ⟨ le_trans hx <| Nat.floor_mono <| Real.exp_le_exp.2 <| by linarith, h.elim ( fun h => h.2.1 ) fun h => h ⟩, fun h => Or.inr h.2 ⟩;
    · exact ⟨ fun h => by cases h <;> [ exact ⟨ by tauto, by tauto ⟩ ; exact False.elim <| by linarith ], fun h => Or.inl ⟨ ⟨ Nat.pos_of_ne_zero <| by aesop_cat, by tauto ⟩, by tauto, Nat.lt_of_floor_lt hx ⟩ ⟩;
  · norm_num [ Finset.disjoint_left ];
    intro a ha₁ ha₂ ha₃ ha₄ ha₅; rw [ Nat.le_floor_iff ( by positivity ) ] at *; linarith;
lemma main_term_ratio_tendsto
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n)))
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1) := by
  have h_fold : ∀ᶠ n in atTop, (li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) = ∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t := by
    filter_upwards [ hδ, hu.eventually_gt_atTop 2 ] with n hn hn';
    unfold li2;
    rw [ sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.add_one_le_exp ( u n - δ n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.add_one_le_exp ( u n - δ n ) ] ) ) );
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.exp_pos ( u n - δ n ), Real.exp_pos ( u n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ Real.add_one_le_exp ( u n - δ n ), Real.add_one_le_exp ( u n ) ] ) ) );
  have h_bound : ∀ᶠ n in atTop, (∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t) ≥ ((1 - Real.exp (-δ n)) * Real.exp (u n)) / (u n) ∧ (∫ t in (Real.exp (u n - δ n))..(Real.exp (u n)), 1 / Real.log t) ≤ ((1 - Real.exp (-δ n)) * Real.exp (u n)) / (u n - δ n) := by
    have h_log_bound : ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (Real.exp (u n - δ n)) (Real.exp (u n)), 1 / u n ≤ 1 / Real.log t ∧ 1 / Real.log t ≤ 1 / (u n - δ n) := by
      filter_upwards [ hu.eventually_gt_atTop 3, hδ ] with n hn hn';
      intro t ht; constructor <;> gcongr <;> nlinarith [ ht.1, ht.2, Real.add_one_le_exp ( u n - δ n ), Real.exp_pos ( u n - δ n ), Real.log_exp ( u n - δ n ), Real.log_le_log ( by positivity ) ht.1, Real.log_exp ( u n ), Real.log_le_log ( by linarith [ Real.exp_pos ( u n - δ n ), ht.1 ] ) ht.2 ] ;
    filter_upwards [ h_fold, h_log_bound, hu.eventually_gt_atTop 2, hδ ] with n hn hn' hn'' hn''' ; refine' ⟨ _, _ ⟩;
    · refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ fun t ht => hn' t ht |>.1 ) <;> norm_num;
      · rw [ show u n - δ n = u n + ( -δ n ) by ring, Real.exp_add ] ; ring_nf ; norm_num;
      · nlinarith;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.exp_pos ( u n - δ n ), Real.exp_pos ( u n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.add_one_le_exp ( u n - δ n ), Real.add_one_le_exp ( u n ), show 1 < u n - δ n from by nlinarith [ inv_mul_cancel₀ ( by linarith : ( u n ) ≠ 0 ) ] ] ) ) );
    · refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ fun t ht => hn' t ht |>.2 ) _ <;> norm_num;
      · nlinarith;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.exp_pos ( u n - δ n ), Real.exp_pos ( u n ) ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ Real.add_one_le_exp ( u n - δ n ), Real.add_one_le_exp ( u n ), inv_pos.mpr ( by linarith : 0 < u n ) ] ) ) );
      · rw [ show Real.exp ( u n - δ n ) = Real.exp ( u n ) * Real.exp ( -δ n ) by rw [ ← Real.exp_add ] ; ring_nf ] ; ring_nf ; norm_num;
  have h_div_bound : ∀ᶠ n in atTop, 1 ≤ ((li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) / ((1 - Real.exp (-δ n)) * Real.exp (u n) / (u n))) ∧ ((li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) / ((1 - Real.exp (-δ n)) * Real.exp (u n) / (u n))) ≤ (u n) / (u n - δ n) := by
    filter_upwards [ h_fold, h_bound, hδ, hu.eventually_gt_atTop 1 ] with n hn hn' hn'' hn''';
    rw [ hn, le_div_iff₀, div_le_iff₀ ];
    · convert And.intro hn'.1 hn'.2 using 1 <;> (try rfl) <;> ring_nf;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans hn''' ) ];
    · exact div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr ( lt_of_lt_of_le ( by positivity ) hn''.1 ) ) ) ) ( Real.exp_pos _ ) ) ( by positivity );
    · exact div_pos ( mul_pos ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr ( lt_of_lt_of_le ( by positivity ) hn''.1 ) ) ) ) ( Real.exp_pos _ ) ) ( by positivity );
  have h_squeeze : Filter.Tendsto (fun n => (u n) / (u n - δ n)) Filter.atTop (nhds 1) := by
    suffices h_div : Filter.Tendsto (fun n => 1 / (1 - δ n / u n)) Filter.atTop (nhds 1) by
      refine h_div.congr' ( by filter_upwards [ hu.eventually_ne_atTop 0 ] with n hn; rw [ one_sub_div hn ] ; norm_num [ hn ] );
    have h_delta_div_u_zero : Filter.Tendsto (fun n => δ n / u n) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ _;
      use fun n => 1 / u n;
      · filter_upwards [ hδ, hu.eventually_gt_atTop 0 ] with n hn hn' using by rw [ Real.norm_of_nonneg ( div_nonneg ( by nlinarith ) hn'.le ) ] ; exact div_le_div_of_nonneg_right ( by nlinarith ) hn'.le;
      · exact tendsto_const_nhds.div_atTop hu;
    simpa using Filter.Tendsto.inv₀ ( h_delta_div_u_zero.const_sub 1 ) ( by norm_num );
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_squeeze ( Filter.eventually_of_mem h_div_bound fun n hn => hn.1 ) ( Filter.eventually_of_mem h_div_bound fun n hn => hn.2 )
lemma error_over_denom_tendsto
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n)))
            - ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ)
                - li2 (Real.exp (u n - δ n))))
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 0) := by
  revert hδ;
  intro hδ
  obtain ⟨c, hc₀, hc⟩ := pnt_li_error
  obtain ⟨K, hK⟩ := hc.exists_pos
  have h_num : ∀ᶠ n in atTop, |((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n))) - ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n)))| ≤ 2 * K * Real.exp (u n) * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10)) := by
    have h_num_bound : ∀ᶠ n in atTop, abs ((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n))) ≤ K * Real.exp (u n) * Real.exp (-c * (u n) ^ ((1:ℝ)/10)) ∧ abs ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n))) ≤ K * Real.exp (u n) * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10)) := by
      have h_bound : ∀ᶠ n in atTop, |((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n)))| ≤ K * (Real.exp (u n)) * Real.exp (-c * (u n) ^ (1 / 10 : ℝ)) := by
        have := hK.2.bound;
        filter_upwards [ this.filter_mono ( Real.tendsto_exp_atTop.comp hu ) ] with n hn using by simpa [ mul_assoc, Real.exp_pos ] using hn;
      have h_bound' : ∀ᶠ n in atTop, |((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n)))| ≤ K * (Real.exp (u n - δ n)) * Real.exp (-c * (u n - δ n) ^ (1 / 10 : ℝ)) := by
        have := hK.2;
        rw [ IsBigOWith ] at this;
        simp +zetaDelta at *;
        obtain ⟨ a, ha ⟩ := this;
        obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( hu.eventually_ge_atTop ( Max.max a 2 + 1 ) );
        refine' ⟨ N + hδ.choose, fun n hn => _ ⟩ ; specialize ha ( Real.exp ( u n - δ n ) ) _;
        · have := hN n ( by linarith );
          linarith [ le_max_left a 2, le_max_right a 2, Real.add_one_le_exp ( u n - δ n ), hδ.choose_spec n ( by linarith ) ];
        · simp_all +decide [ mul_assoc, abs_of_nonneg, Real.exp_nonneg ];
      filter_upwards [ h_bound, h_bound', hδ, hu.eventually_gt_atTop 1 ] with n hn hn' hn'' hn''';
      refine ⟨ hn, hn'.trans ?_ ⟩;
      norm_num [ mul_assoc, ← Real.exp_add ];
      exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ show ( u n - δ n ) ^ ( 1 / 10 : ℝ ) ≥ ( u n - 1 ) ^ ( 1 / 10 : ℝ ) by exact Real.rpow_le_rpow ( by linarith ) ( by linarith ) ( by norm_num ) ] ) hK.1.le;
    filter_upwards [ h_num_bound, hδ, hu.eventually_gt_atTop 1 ] with n hn hn' hn'';
    refine' le_trans ( abs_sub _ _ ) _;
    nlinarith [ show 0 < K * Real.exp ( u n ) by exact mul_pos hK.1 ( Real.exp_pos _ ), show Real.exp ( -c * u n ^ ( 1 / 10 : ℝ ) ) ≤ Real.exp ( -c * ( u n - 1 ) ^ ( 1 / 10 : ℝ ) ) by exact Real.exp_le_exp.mpr ( mul_le_mul_of_nonpos_left ( Real.rpow_le_rpow ( by linarith ) ( by linarith ) ( by norm_num ) ) ( by linarith ) ) ];
  have h_denom : ∀ᶠ n in atTop, (1 - Real.exp (-δ n)) * Real.exp (u n) / u n ≥ Real.exp (u n) / (2 * (u n)^3) := by
    have h_exp_bound : ∀ᶠ n in atTop, 1 - Real.exp (-δ n) ≥ δ n / 2 := by
      filter_upwards [ hδ, hu.eventually_gt_atTop 1 ] with n hn hn';
      nlinarith [ Real.exp_pos ( -δ n ), Real.exp_neg ( δ n ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( δ n ) ) ), Real.add_one_le_exp ( δ n ), Real.add_one_le_exp ( -δ n ) ];
    filter_upwards [ hδ, h_exp_bound, hu.eventually_gt_atTop 1 ] with n hn hn' hn'';
    field_simp at *;
    nlinarith [ sq_nonneg ( u n - 1 ) ];
  have h_ratio : Filter.Tendsto (fun n => (2 * K * Real.exp (u n) * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10))) / (Real.exp (u n) / (2 * (u n)^3))) Filter.atTop (nhds 0) := by
    suffices h_simplify : Filter.Tendsto (fun n => 4 * K * (u n)^3 * Real.exp (-c * (u n - 1) ^ ((1:ℝ)/10))) Filter.atTop (nhds 0) by
      convert h_simplify using 2 <;> (try rfl) ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.exp_ne_zero ];
    suffices h_w : Filter.Tendsto (fun w => 4 * K * (w ^ 10 + 1) ^ 3 * Real.exp (-c * w)) Filter.atTop (nhds 0) by
      have h_subst : Filter.Tendsto (fun n => (u n - 1) ^ ((1:ℝ)/10)) Filter.atTop Filter.atTop := by
        exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ hu;
      refine' squeeze_zero_norm' _ ( h_w.comp h_subst );
      filter_upwards [ hu.eventually_gt_atTop 1, h_subst.eventually_gt_atTop 1 ] with n hn hn' ; norm_num [ abs_of_nonneg, hn.le, hn'.le ];
      rw [ abs_of_pos hK.1, abs_of_pos ( by linarith ) ] ; gcongr;
      · linarith;
      · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith ) ] ; norm_num;
    suffices h_factor : Filter.Tendsto (fun w => 4 * K * w ^ 30 * Real.exp (-c * w) * (1 + 1 / w ^ 10) ^ 3) Filter.atTop (nhds 0) by
      refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with w hw using by rw [ show ( w ^ 10 + 1 ) ^ 3 = ( w ^ 10 ) ^ 3 * ( 1 + 1 / w ^ 10 ) ^ 3 by rw [ show ( w ^ 10 + 1 ) = w ^ 10 * ( 1 + 1 / w ^ 10 ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; ring ] ; ring );
    have h_exp : Filter.Tendsto (fun w => w ^ 30 * Real.exp (-c * w)) Filter.atTop (nhds 0) := by
      have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 30;
      have := this.comp ( Filter.tendsto_id.const_mul_atTop hc₀ );
      convert this.div_const ( c ^ 30 ) using 2 <;> (try rfl) <;> norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm, hc₀.ne' ];
    simpa [ mul_assoc ] using Filter.Tendsto.mul ( h_exp.const_mul ( 4 * K ) ) ( Filter.Tendsto.pow ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero.comp ( by norm_num ) ) ) 3 );
  refine' squeeze_zero_norm' _ h_ratio;
  filter_upwards [ h_num, h_denom, hu.eventually_gt_atTop 0 ] with n hn hn' hn'' ; rw [ Real.norm_eq_abs, abs_div ] ; gcongr;
  · exact mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_two hK.1.le ) ( Real.exp_nonneg _ ) ) ( Real.exp_nonneg _ );
  · exact le_trans hn' ( le_abs_self _ )
theorem primes_in_log_interval_proof
    (u δ : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (hδ : ∀ᶠ n in atTop, (u n)⁻¹ ^ 2 ≤ δ n ∧ δ n ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        (((Finset.Icc 1 ⌊Real.exp (u n)⌋₊).filter
            (fun p => Nat.Prime p ∧ Real.exp (u n - δ n) < (p : ℝ))).card : ℝ)
          / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      atTop (nhds 1) := by
  have h_sum : Filter.Tendsto
      (fun n : ℕ =>
        (((Nat.primeCounting ⌊Real.exp (u n)⌋₊ : ℝ) - li2 (Real.exp (u n)))
            - ((Nat.primeCounting ⌊Real.exp (u n - δ n)⌋₊ : ℝ) - li2 (Real.exp (u n - δ n))))
            / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n))
        + (li2 (Real.exp (u n)) - li2 (Real.exp (u n - δ n))) / ((1 - Real.exp (-(δ n))) * Real.exp (u n) / (u n)))
      Filter.atTop (nhds (0 + 1)) := by
        convert Tendsto.add ( error_over_denom_tendsto u δ hu hδ ) ( main_term_ratio_tendsto u δ hu hδ ) using 1 <;> (try rfl);
  simp_all +decide;
  refine h_sum.congr' ?_ ; filter_upwards [ Filter.eventually_ge_atTop hδ.choose ] with n hn ; rw [ count_eq_primeCounting_diff _ _ ( by linarith [ hδ.choose_spec n hn, inv_nonneg.2 ( sq_nonneg ( u n ) ) ] ) ] ; ring;
end Erdos768
end P

theorem OMA.solution : OMA.R_Erdos768_erdos_768_R1_H1_R1.H2 := by
  intro h
  haveI : Fact Erdos768.MediumPNTStmt := ⟨h⟩
  exact fun u δ hu hδ => Erdos768.primes_in_log_interval_proof u δ hu hδ
