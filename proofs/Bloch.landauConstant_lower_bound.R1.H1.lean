import OMAReductions.R_Bloch_landauConstant_lower_bound_R1
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Covering-map parametrization for Landau lower bound (H1)

We prove `OMA.R_Bloch_landauConstant_lower_bound_R1.H1`: every holomorphic map
`f : ball 0 1 → ℂ` with `deriv f 0 = 1` omitting two distinct points admits a locally
univalent holomorphic map `g : ball 0 1 → ℂ` with `1 ≤ ‖deriv g 0‖` and
`g '' ball 0 1 ⊆ f '' ball 0 1`.

Proof overview:
1. Build the holomorphic covering map `j : H' → ℂ \ {0, 1728}` via `E₄, E₆, Δ`.
   (The asymptotic and Serre-derivative lemmas for `E₄, E₆, E₂` are adapted from
   `proofs/Bloch.landauConstant_upper_bound.lean` in this repository.)
2. Construct the universal cover `π : Ω̃ → Ω` of `Ω = f₁ '' ball 0 1 ⊆ ℂ \ {0, 1728}`
   and lift `π` through `j` and the Cayley transform to get a non-constant bounded
   holomorphic map `Φ : Ω̃ → ball 0 1`.
3. Uniformize `Ω̃ ≃ ball 0 1` via Perron's method for the Green's function `G_a`,
   constructing `ψ_a : Ω̃ → ball 0 1` by lifting through a flat `Circle`-covering,
   proving injectivity via symmetry + maximum modulus, and surjectivity via the
   Koebe square-root maximization trick.
4. Set `g₁ = π_ℂ ∘ ψ⁻¹` and apply Schwarz's lemma to `ψ ∘ f̃₁`.
-/

namespace LandauH1

noncomputable section

open Complex Real Metric Set Filter Topology Function
open UpperHalfPlane hiding I
open ModularForm ModularGroup MatrixGroups EisensteinSeries Derivative

/- ### Part 1: Asymptotics and Serre derivative for `E₄, E₆, E₂, Δ` -/

private lemma tendsto_atImInfty_E4 : Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hana := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos
    one_mem_strictPeriods_SL
  have hval : UpperHalfPlane.cuspFunction 1 ModularForm.E₄ 0 = 1 := by
    have h0 := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    simpa [UpperHalfPlane.qExpansion_coeff] using h0
  have heq : (UpperHalfPlane.cuspFunction 1 ModularForm.E₄ ∘ fun τ : ℍ => Periodic.qParam 1 τ) =
      ModularForm.E₄ := by
    funext τ
    exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ one_mem_strictPeriods_SL
      one_ne_zero
  simpa [heq, hval] using hana.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

private lemma tendsto_atImInfty_E6 : Tendsto (ModularForm.E₆ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hana := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ one_pos
    one_mem_strictPeriods_SL
  have hval : UpperHalfPlane.cuspFunction 1 ModularForm.E₆ 0 = 1 := by
    have h0 := EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) ⟨3, rfl⟩
    simpa [UpperHalfPlane.qExpansion_coeff] using h0
  have heq : (UpperHalfPlane.cuspFunction 1 ModularForm.E₆ ∘ fun τ : ℍ => Periodic.qParam 1 τ) =
      ModularForm.E₆ := by
    funext τ
    exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₆ τ one_mem_strictPeriods_SL
      one_ne_zero
  simpa [heq, hval] using hana.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

private lemma periodic_E2 : Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw1,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [EisensteinSeries.E2_eq_tsum_cexp, EisensteinSeries.E2_eq_tsum_cexp]
    congr 2
    refine tsum_congr fun n => ?_
    congr 2
    have : Complex.exp (2 * Real.pi * I * (w + 1)) = Complex.exp (2 * Real.pi * I * w) := by
      rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact this
  · have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hw),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw1]

private lemma tendsto_atImInfty_E2 : Tendsto EisensteinSeries.E2 atImInfty (𝓝 1) := by
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos periodic_E2
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hfps := UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos hana fun τ => by
    simpa only [Periodic.qParam, ofReal_one, div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z := τ)
  have hval : UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 0 = 1 := by
    have h0 := hfps.coeff_zero 1
    simpa using h0.symm
  have heq : (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 ∘
      fun τ : ℍ => Periodic.qParam 1 τ) = EisensteinSeries.E2 := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero periodic_E2
  simpa [heq, hval] using hana.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

private lemma tendsto_atImInfty_D_E4 :
    Tendsto (Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ)) atImInfty (𝓝 0) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
    one_mem_strictPeriods_SL
  have hdiff : DifferentiableOn ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.E₄)
      (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos hper ModularForm.E₄.holo'
      (ModularFormClass.bdd_at_infty ModularForm.E₄)
  have hderiv_cont : ContinuousAt (deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄)) 0 :=
    ((hdiff.deriv Metric.isOpen_ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))).continuousAt
  have hDeq : ∀ τ : ℍ, Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ) τ =
      Periodic.qParam 1 τ * deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄)
        (Periodic.qParam 1 τ) := by
    intro τ
    have hq_mem : Periodic.qParam 1 τ ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
    have hcf : HasDerivAt (UpperHalfPlane.cuspFunction 1 ModularForm.E₄)
        (deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (Periodic.qParam 1 τ))
        (Periodic.qParam 1 τ) :=
      (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hq_mem)).hasDerivAt
    have hqp : HasDerivAt (Periodic.qParam 1) (2 * Real.pi * I * Periodic.qParam 1 τ) (τ : ℂ) := by
      have h1 : Periodic.qParam 1 = fun w : ℂ => Complex.exp (2 * Real.pi * I * w) := by
        ext w; simp [Periodic.qParam]
      rw [h1]
      simpa [Periodic.qParam, mul_comm] using
        ((hasDerivAt_id (τ : ℂ)).const_mul (2 * Real.pi * I)).cexp
    have hcomp := hcf.comp (τ : ℂ) hqp
    have hev : (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
        (UpperHalfPlane.cuspFunction 1 ModularForm.E₄ ∘ Periodic.qParam 1) := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      exact (SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ ⟨w, hw⟩
        one_mem_strictPeriods_SL one_ne_zero).symm
    rw [Derivative.normalizedDerivOfComplex, (hcomp.congr_of_eventuallyEq hev).deriv]
    have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp [h2pi]
  have ht : Tendsto
      (fun τ : ℍ => Periodic.qParam 1 τ *
        deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (Periodic.qParam 1 τ))
      atImInfty (𝓝 0) := by
    simpa using (UpperHalfPlane.qParam_tendsto_atImInfty one_pos).mul
      (hderiv_cont.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos))
  exact ht.congr fun τ => (hDeq τ).symm

private lemma tendsto_atImInfty_serreE4 :
    Tendsto (Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ)) atImInfty (𝓝 (-1 / 3 : ℂ)) := by
  have h := tendsto_atImInfty_D_E4.sub
    ((tendsto_const_nhds (x := (4 * 12⁻¹ : ℂ)).mul tendsto_atImInfty_E2).mul tendsto_atImInfty_E4)
  have hval : (0 : ℂ) - 4 * 12⁻¹ * 1 * 1 = -1 / 3 := by norm_num
  rw [hval] at h
  exact h

private lemma serreE4_slash (γ : SL(2, ℤ)) :
    (Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) ∣[(6 : ℤ)] γ) =
      Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) := by
  have hinv : ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) = ModularForm.E₄ :=
    ModularForm.E₄.slash_action_eq' (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
  have h := Derivative.serreDerivative_slash_invariant (k := (4 : ℤ)) ModularForm.E₄.holo' hinv
  simpa [show (4 : ℤ) + 2 = 6 by norm_num] using h

private def serreE4MF : ModularForm 𝒮ℒ 6 where
  toFun := Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ)
  slash_action_eq' := fun _ ⟨γ, hγ⟩ => hγ ▸ serreE4_slash γ
  holo' := Derivative.serreDerivative_mdifferentiable 4 ModularForm.E₄.holo'
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [serreE4_slash γ]
    exact tendsto_atImInfty_serreE4.isBigO_one ℝ

private lemma serreDerivative_E4 :
    Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) =
      (-1 / 3 : ℂ) • (ModularForm.E₆ : ℍ → ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₆ = serreE4MF :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₆
      (EisensteinSeries.E_ne_zero (k := 6) (by norm_num) ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one) serreE4MF
  have hfun : (fun z : ℍ => c * ModularForm.E₆ z) =
      Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) := by
    funext z
    exact congr_fun (congr_arg DFunLike.coe hc) z
  have ht1 : Tendsto (fun z : ℍ => c * ModularForm.E₆ z) atImInfty (𝓝 (c * 1)) :=
    tendsto_const_nhds.mul tendsto_atImInfty_E6
  rw [hfun] at ht1
  have hc_eq : c = -1 / 3 := by
    have := tendsto_nhds_unique ht1 tendsto_atImInfty_serreE4
    simpa using this
  subst hc_eq
  ext z
  exact (congr_fun hfun z).symm

/- ### Part 2: The modular `j`-invariant covering map `H' → ℂ \ {0, 1728}` -/

private def jFn (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private def H' : Set ℍ := {τ | ModularForm.E₄ τ ≠ 0 ∧ ModularForm.E₆ τ ≠ 0}

private lemma jFn_ne_zero_and_1728_iff (τ : ℍ) :
    τ ∈ H' ↔ jFn τ ≠ 0 ∧ jFn τ ≠ 1728 := by
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  have hrel : (1728 : ℂ) * ModularForm.discriminant τ =
      ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2 := by
    have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
    linear_combination 1728 * h
  simp only [H', mem_ofPred_eq, jFn, ne_eq, div_eq_zero_iff, hΔ, or_false, pow_eq_zero_iff',
    OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
  constructor <;> rintro ⟨h4, h6⟩
  · refine ⟨h4, fun h => h6 ?_⟩
    have h1 : ModularForm.E₄ τ ^ 3 = 1728 * ModularForm.discriminant τ :=
      (div_eq_iff hΔ).mp h
    rw [h1] at hrel
    have h2 : ModularForm.E₆ τ ^ 2 = 0 := sub_eq_self.mp hrel.symm
    exact eq_zero_of_pow_eq_zero h2
  · refine ⟨h4, fun h => h6 ?_⟩
    rw [div_eq_iff hΔ]
    linear_combination -hrel + h * ModularForm.E₆ τ

private lemma isOpen_H' : IsOpen H' := by
  have h4 : Continuous (ModularForm.E₄ : ℍ → ℂ) := ModularForm.E₄.holo'.continuous
  have h6 : Continuous (ModularForm.E₆ : ℍ → ℂ) := ModularForm.E₆.holo'.continuous
  exact (isOpen_ne.preimage h4).inter (isOpen_ne.preimage h6)

private lemma jFn_continuous : Continuous jFn :=
  (ModularForm.E₄.holo'.continuous.pow 3).div CuspForm.discriminant.holo'.continuous
    ModularForm.discriminant_ne_zero

private lemma E4_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) = (denom γ τ) ^ 4 * ModularForm.E₄ τ := by
  have h := congr_fun (SlashInvariantForm.slash_action_eqn ModularForm.E₄ (γ : GL (Fin 2) ℝ)
    ⟨γ, rfl⟩) τ
  rw [show ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ)) τ =
      ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) τ from rfl,
    ModularForm.SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  have h' : ModularForm.E₄ (γ • τ) * ((denom γ τ) ^ 4)⁻¹ = ModularForm.E₄ τ := by
    simpa [zpow_neg, zpow_ofNat] using h
  have hpow : (denom γ τ) ^ 4 ≠ 0 := pow_ne_zero 4 hd
  calc ModularForm.E₄ (γ • τ)
      = ModularForm.E₄ (γ • τ) * ((denom γ τ) ^ 4)⁻¹ * (denom γ τ) ^ 4 := by
        rw [mul_assoc, inv_mul_cancel₀ hpow, mul_one]
    _ = (denom γ τ) ^ 4 * ModularForm.E₄ τ := by rw [h', mul_comm]

private lemma E6_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₆ (γ • τ) = (denom γ τ) ^ 6 * ModularForm.E₆ τ := by
  have h := congr_fun (SlashInvariantForm.slash_action_eqn ModularForm.E₆ (γ : GL (Fin 2) ℝ)
    ⟨γ, rfl⟩) τ
  rw [show ((ModularForm.E₆ : ℍ → ℂ) ∣[(6 : ℤ)] (γ : GL (Fin 2) ℝ)) τ =
      ((ModularForm.E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ) τ from rfl,
    ModularForm.SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  have h' : ModularForm.E₆ (γ • τ) * ((denom γ τ) ^ 6)⁻¹ = ModularForm.E₆ τ := by
    simpa [zpow_neg, zpow_ofNat] using h
  have hpow : (denom γ τ) ^ 6 ≠ 0 := pow_ne_zero 6 hd
  calc ModularForm.E₆ (γ • τ)
      = ModularForm.E₆ (γ • τ) * ((denom γ τ) ^ 6)⁻¹ * (denom γ τ) ^ 6 := by
        rw [mul_assoc, inv_mul_cancel₀ hpow, mul_one]
    _ = (denom γ τ) ^ 6 * ModularForm.E₆ τ := by rw [h', mul_comm]

private lemma discr_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = (denom γ τ) ^ 12 * ModularForm.discriminant τ := by
  have h := congr_fun (SlashInvariantForm.slash_action_eqn CuspForm.discriminant (γ : GL (Fin 2) ℝ)
    ⟨γ, rfl⟩) τ
  rw [show ((CuspForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ)) τ =
      ((CuspForm.discriminant : ℍ → ℂ) ∣[(12 : ℤ)] γ) τ from rfl,
    ModularForm.SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  have h' : ModularForm.discriminant (γ • τ) * ((denom γ τ) ^ 12)⁻¹ =
      ModularForm.discriminant τ := by
    simpa [zpow_neg, zpow_ofNat] using h
  have hpow : (denom γ τ) ^ 12 ≠ 0 := pow_ne_zero 12 hd
  calc ModularForm.discriminant (γ • τ)
      = ModularForm.discriminant (γ • τ) * ((denom γ τ) ^ 12)⁻¹ * (denom γ τ) ^ 12 := by
        rw [mul_assoc, inv_mul_cancel₀ hpow, mul_one]
    _ = (denom γ τ) ^ 12 * ModularForm.discriminant τ := by rw [h', mul_comm]

private lemma jFn_smul (γ : SL(2, ℤ)) (τ : ℍ) : jFn (γ • τ) = jFn τ := by
  simp only [jFn, E4_smul, discr_smul, mul_pow]
  have hpow : (denom γ τ) ^ 12 ≠ 0 := pow_ne_zero 12 (denom_ne_zero γ τ)
  rw [show ((denom γ τ) ^ 4) ^ 3 = (denom γ τ) ^ 12 by ring]
  exact mul_div_mul_left _ _ hpow

private lemma smul_mem_H'_iff (γ : SL(2, ℤ)) (τ : ℍ) : γ • τ ∈ H' ↔ τ ∈ H' := by
  rw [jFn_ne_zero_and_1728_iff, jFn_ne_zero_and_1728_iff, jFn_smul]

private lemma hasDerivAt_discriminant (τ : ℍ) :
    HasDerivAt (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * I * EisensteinSeries.E2 τ * ModularForm.discriminant τ) (τ : ℂ) := by
  have heta : HasDerivAt ModularForm.eta (deriv ModularForm.eta (τ : ℂ)) (τ : ℂ) :=
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).hasDerivAt
  have hpow : HasDerivAt (fun w => ModularForm.eta w ^ 24)
      (24 * ModularForm.eta (τ : ℂ) ^ 23 * deriv ModularForm.eta (τ : ℂ)) (τ : ℂ) := by
    simpa using heta.fun_pow 24
  have hlog := ModularForm.logDeriv_eta_eq_E2 τ
  rw [logDeriv_apply] at hlog
  have hne : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  have hderiv_eta : deriv ModularForm.eta (τ : ℂ) =
      (Real.pi * I / 12) * EisensteinSeries.E2 τ * ModularForm.eta (τ : ℂ) := by
    calc deriv ModularForm.eta (τ : ℂ)
        = (deriv ModularForm.eta (τ : ℂ) / ModularForm.eta (τ : ℂ)) * ModularForm.eta (τ : ℂ) :=
          (div_mul_cancel₀ _ hne).symm
      _ = (Real.pi * I / 12) * EisensteinSeries.E2 τ * ModularForm.eta (τ : ℂ) := by rw [hlog]
  have hev : (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun w => ModularForm.eta w ^ 24 := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw, ModularForm.discriminant]
  refine (hpow.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hderiv_eta, ModularForm.discriminant]
  ring

private lemma hasDerivAt_jFn (τ : ℍ) :
    HasDerivAt (jFn ∘ UpperHalfPlane.ofComplex)
      (-2 * Real.pi * I * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ /
        ModularForm.discriminant τ) (τ : ℂ) := by
  have hE4 : HasDerivAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex)
      (deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) (τ : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₄.holo' τ)).hasDerivAt
  have hΔ := hasDerivAt_discriminant τ
  have hdiv : HasDerivAt (fun w => (ModularForm.E₄ (UpperHalfPlane.ofComplex w)) ^ 3 /
        ModularForm.discriminant (UpperHalfPlane.ofComplex w))
      ((3 * (ModularForm.E₄ (UpperHalfPlane.ofComplex (τ : ℂ))) ^ 2 *
          deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ) *
          ModularForm.discriminant (UpperHalfPlane.ofComplex (τ : ℂ)) -
        (ModularForm.E₄ (UpperHalfPlane.ofComplex (τ : ℂ))) ^ 3 *
          (2 * Real.pi * I * EisensteinSeries.E2 τ * ModularForm.discriminant τ)) /
        (ModularForm.discriminant (UpperHalfPlane.ofComplex (τ : ℂ))) ^ 2) (τ : ℂ) := by
    have hnum : HasDerivAt (fun w => (ModularForm.E₄ (UpperHalfPlane.ofComplex w)) ^ 3)
        (3 * (ModularForm.E₄ (UpperHalfPlane.ofComplex (τ : ℂ))) ^ 2 *
          deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) (τ : ℂ) := by
      simpa using hE4.fun_pow 3
    exact hnum.div hΔ (by simpa [UpperHalfPlane.ofComplex_apply] using ModularForm.discriminant_ne_zero τ)
  have hserre := congr_fun serreDerivative_E4 τ
  simp only [Derivative.serreDerivative_apply, Derivative.normalizedDerivOfComplex,
    Pi.smul_apply, smul_eq_mul] at hserre
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hE4' : deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
      2 * Real.pi * I * (4 * 12⁻¹ * EisensteinSeries.E2 τ * ModularForm.E₄ τ +
        (-1 / 3 : ℂ) * ModularForm.E₆ τ) := by
    have h1 : (2 * Real.pi * I)⁻¹ * deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
        4 * 12⁻¹ * EisensteinSeries.E2 τ * ModularForm.E₄ τ + (-1 / 3 : ℂ) * ModularForm.E₆ τ := by
      linear_combination hserre
    calc deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ)
        = (2 * Real.pi * I) * ((2 * Real.pi * I)⁻¹ *
            deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ : ℂ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
      _ = _ := by rw [h1]
  have hΔne : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  refine hdiv.congr_deriv ?_
  simp only [UpperHalfPlane.ofComplex_apply]
  rw [hE4']
  field_simp [hΔne]
  ring

private lemma jFn_deriv_ne_zero {τ : ℍ} (hτ : τ ∈ H') :
    (-2 * Real.pi * I * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ /
      ModularForm.discriminant τ) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
      (pow_ne_zero 2 hτ.1)) hτ.2)
    (ModularForm.discriminant_ne_zero τ)

private lemma stabilizer_H'_eq_pm_one {τ : ℍ} (hτ : τ ∈ H') {γ : SL(2, ℤ)}
    (hfix : γ • τ = τ) : γ = 1 ∨ γ = -1 := by
  by_contra hne
  push Not at hne
  let g : GL (Fin 2) ℝ := γ
  have hdet : 0 < g.val.det := by
    have : g.val.det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      simp [g]
    linarith
  have hgfix : g • τ = τ := hfix
  have hnotcenter : g ∉ Subgroup.center (GL (Fin 2) ℝ) := by
    intro hmem
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h00 : (γ 0 0 : ℝ) = r := (by simpa [g] using congr_fun (congr_fun hr 0) 0 : r = (γ 0 0 : ℝ)).symm
    have h01 : (γ 0 1 : ℝ) = 0 := (by simpa [g] using congr_fun (congr_fun hr 0) 1 : (0 : ℝ) = (γ 0 1 : ℝ)).symm
    have h10 : (γ 1 0 : ℝ) = 0 := (by simpa [g] using congr_fun (congr_fun hr 1) 0 : (0 : ℝ) = (γ 1 0 : ℝ)).symm
    have h11 : (γ 1 1 : ℝ) = r := (by simpa [g] using congr_fun (congr_fun hr 1) 1 : r = (γ 1 1 : ℝ)).symm
    have h01z : γ 0 1 = 0 := by exact_mod_cast h01
    have h10z : γ 1 0 = 0 := by exact_mod_cast h10
    have h0011 : γ 0 0 = γ 1 1 := by exact_mod_cast h00.trans h11.symm
    have hdet1 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have hd : γ.1.det = 1 := γ.2
      rwa [Matrix.det_fin_two] at hd
    rw [h01z, h10z, h0011] at hdet1
    have hsq : γ 1 1 * γ 1 1 = 1 := by linarith
    have hpm : γ 1 1 = 1 ∨ γ 1 1 = -1 := mul_self_eq_one_iff.mp hsq
    rcases hpm with h1 | h1
    · apply hne.1
      ext i j; fin_cases i <;> fin_cases j <;> simp [h0011, h1, h01z, h10z]
    · apply hne.2
      ext i j; fin_cases i <;> fin_cases j <;> simp [h0011, h1, h01z, h10z]
  have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hdet hnotcenter ⟨τ, hgfix⟩
  have htr_lt : g.val.trace ^ 2 < 4 := by
    have hdiscr : g.val.discr < 0 := hell
    rw [Matrix.discr_fin_two] at hdiscr
    have hd1 : g.val.det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp [g]
    linarith
  have htr_int : (γ.1.trace : ℤ) ^ 2 < 4 := by
    have : (g.val.trace : ℝ) = ((γ.1.trace : ℤ) : ℝ) := by
      simp [g, Matrix.trace_fin_two]
    exact_mod_cast (this ▸ htr_lt)
  have hc_ne : (γ 1 0 : ℂ) ≠ 0 := by
    have hc : g 1 0 ≠ 0 := hell.c_ne_zero
    have : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by simpa [g] using hc
    exact_mod_cast this
  have hdenom_im : (denom γ τ).im ≠ 0 := by
    rw [ModularGroup.denom_apply]
    simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    have hcr : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by
      intro h; apply hc_ne; exact_mod_cast h
    exact mul_ne_zero hcr τ.im_pos.ne'
  have hdenom_sq_ne_one : (denom γ τ) ^ 2 ≠ 1 := by
    intro h
    have hpm : denom γ τ = 1 ∨ denom γ τ = -1 := sq_eq_one_iff.mp h
    rcases hpm with h1 | h1 <;> exact hdenom_im (by simp [h1])
  have hnum_div : num g τ / denom g τ = (τ : ℂ) := by
    have h1 : ((γ • τ : ℍ) : ℂ) = num g τ / denom g τ := by
      simpa [g, num, denom] using congr_arg UpperHalfPlane.coe (UpperHalfPlane.specialLinearGroup_apply γ τ)
    rw [← h1, hfix]
  have hsq_denom : denom (γ * γ : SL(2, ℤ)) τ = (denom γ τ) ^ 2 := by
    have h1 := denom_cocycle g g τ.im_pos.ne'
    have h2 : ((γ * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = g * g := by
      simp [g, map_mul]
    rw [h2, h1, hnum_div, sq]
  have hcube_denom : denom (γ * γ * γ : SL(2, ℤ)) τ = (denom γ τ) ^ 3 := by
    have h1 := denom_cocycle (g * g) g τ.im_pos.ne'
    have h2 : ((γ * γ * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (g * g) * g := by
      simp [g, map_mul]
    have h3 : denom (g * g) τ = (denom γ τ) ^ 2 := by
      have h2' : ((γ * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = g * g := by simp [g, map_mul]
      rw [← h2']; exact hsq_denom
    rw [h2, h1, hnum_div, h3]
    ring
  have hch : γ.1 * γ.1 - γ.1.trace • γ.1 + (1 : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
    have hd : γ.1.det = 1 := γ.2
    rw [Matrix.det_fin_two] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.one_apply,
        Matrix.zero_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, ↓reduceIte,
        Fin.reduceEq] <;>
      nlinarith
  have htr_cases : γ.1.trace = 0 ∨ γ.1.trace = 1 ∨ γ.1.trace = -1 := by
    have hlt : -2 < γ.1.trace ∧ γ.1.trace < 2 := by constructor <;> nlinarith
    omega
  have hdenom_neg_one : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -1 := by
    simp [denom]
  have hdenom_one : denom ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
    simp [denom]
  rcases htr_cases with htr | htr | htr
  · have hγ2 : γ * γ = -1 := by
      ext i j
      have hij := congr_fun (congr_fun hch i) j
      simp [htr] at hij
      change (γ.1 * γ.1) i j = -((1 : Matrix (Fin 2) (Fin 2) ℤ) i j)
      omega
    have hd2 : (denom γ τ) ^ 2 = -1 := by
      rw [← hsq_denom, hγ2]
      exact hdenom_neg_one
    have hE6 := E6_smul γ τ
    rw [hfix, show (denom γ τ) ^ 6 = ((denom γ τ) ^ 2) ^ 3 by ring, hd2] at hE6
    have : ModularForm.E₆ τ = 0 := by linear_combination hE6 / 2
    exact hτ.2 this
  · have hγ3 : γ * γ * γ = -1 := by
      have h1 : γ.1 * γ.1 = γ.1 - 1 := by
        ext i j
        have hij := congr_fun (congr_fun hch i) j
        simp [htr] at hij
        change (γ.1 * γ.1) i j = γ.1 i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
        omega
      ext i j
      have h2 : γ.1 * γ.1 * γ.1 = -1 := by
        calc γ.1 * γ.1 * γ.1 = (γ.1 - 1) * γ.1 := by rw [h1]
          _ = γ.1 * γ.1 - γ.1 := by rw [sub_mul, one_mul]
          _ = -1 := by rw [h1]; simp
      simpa using congr_fun (congr_fun h2 i) j
    have hd3 : (denom γ τ) ^ 3 = -1 := by
      rw [← hcube_denom, hγ3]
      exact hdenom_neg_one
    have hE4 := E4_smul γ τ
    rw [hfix] at hE4
    have hd4_ne : (denom γ τ) ^ 4 ≠ 1 := by
      intro hd4
      have : (denom γ τ) ^ 2 = 1 := by
        have hd6 : (denom γ τ) ^ 6 = 1 := by
          rw [show (denom γ τ) ^ 6 = ((denom γ τ) ^ 3) ^ 2 by ring, hd3]; norm_num
        linear_combination hd6 - hd4 * (denom γ τ) ^ 2
      exact hdenom_sq_ne_one this
    have : ModularForm.E₄ τ * ((denom γ τ) ^ 4 - 1) = 0 := by linear_combination -hE4
    rcases mul_eq_zero.mp this with h0 | h1
    · exact hτ.1 h0
    · exact hd4_ne (sub_eq_zero.mp h1)
  · have hγ3 : γ * γ * γ = 1 := by
      have h1 : γ.1 * γ.1 = -γ.1 - 1 := by
        ext i j
        have hij := congr_fun (congr_fun hch i) j
        simp [htr] at hij
        change (γ.1 * γ.1) i j = -(γ.1 i j) - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
        omega
      ext i j
      have h2 : γ.1 * γ.1 * γ.1 = 1 := by
        calc γ.1 * γ.1 * γ.1 = (-γ.1 - 1) * γ.1 := by rw [h1]
          _ = -(γ.1 * γ.1) - γ.1 := by rw [sub_mul, neg_mul, one_mul]
          _ = 1 := by rw [h1]; abel
      simpa using congr_fun (congr_fun h2 i) j
    have hd3 : (denom γ τ) ^ 3 = 1 := by
      rw [← hcube_denom, hγ3]
      exact hdenom_one
    have hE4 := E4_smul γ τ
    rw [hfix] at hE4
    have hd4_ne : (denom γ τ) ^ 4 ≠ 1 := by
      intro hd4
      have : (denom γ τ) ^ 2 = 1 := by
        have hd6 : (denom γ τ) ^ 6 = 1 := by
          rw [show (denom γ τ) ^ 6 = ((denom γ τ) ^ 3) ^ 2 by ring, hd3]; norm_num
        linear_combination hd6 - hd4 * (denom γ τ) ^ 2
      exact hdenom_sq_ne_one this
    have : ModularForm.E₄ τ * ((denom γ τ) ^ 4 - 1) = 0 := by linear_combination -hE4
    rcases mul_eq_zero.mp this with h0 | h1
    · exact hτ.1 h0
    · exact hd4_ne (sub_eq_zero.mp h1)

private lemma tendsto_norm_jFn_atImInfty :
    Tendsto (fun τ : ℍ => ‖jFn τ‖) atImInfty atTop := by
  have hnum : Tendsto (fun τ : ℍ => ‖ModularForm.E₄ τ ^ 3‖) atImInfty (𝓝 1) := by
    simpa using (tendsto_atImInfty_E4.pow 3).norm
  have hden0 : Tendsto (fun τ : ℍ => ‖ModularForm.discriminant τ‖) atImInfty (𝓝 0) := by
    simpa using ModularForm.discriminant_isZeroAtImInfty.norm
  have hden : Tendsto (fun τ : ℍ => ‖ModularForm.discriminant τ‖) atImInfty (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hden0
      (Eventually.of_forall fun τ => norm_pos_iff.mpr (ModularForm.discriminant_ne_zero τ))
  have hinv : Tendsto (fun τ : ℍ => (‖ModularForm.discriminant τ‖)⁻¹) atImInfty atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  have hprod := hnum.pos_mul_atTop zero_lt_one hinv
  refine hprod.congr fun τ => ?_
  simp [jFn, div_eq_mul_inv]

private lemma isCompact_fd_im_le (Y : ℝ) :
    IsCompact {τ : ℍ | τ ∈ ModularGroup.fd ∧ τ.im ≤ Y} := by
  let K : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2 ∧ Real.sqrt 3 / 2 ≤ z.im ∧ z.im ≤ Y}
  have hK_closed : IsClosed K := by
    refine (isClosed_le (_root_.continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  have hK_bdd : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max (1 / 2) (max Y (Real.sqrt 3 / 2)) * 2 + 1, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ 1 / 2 := hz.1
    have him0 : 0 ≤ z.im := le_trans (by positivity) hz.2.1
    have him : |z.im| ≤ Y := by rw [abs_of_nonneg him0]; exact hz.2.2
    have hle := Complex.norm_le_abs_re_add_abs_im z
    have hm1 : (1 / 2 : ℝ) ≤ max (1 / 2) (max Y (Real.sqrt 3 / 2)) := le_max_left _ _
    have hm2 : Y ≤ max (1 / 2) (max Y (Real.sqrt 3 / 2)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hK_cpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  have hK_sub : K ⊆ UpperHalfPlane.upperHalfPlaneSet := fun z hz =>
    lt_of_lt_of_le (by positivity) hz.2.1
  let S : Set ℍ := {τ : ℍ | τ ∈ ModularGroup.fd ∧ τ.im ≤ Y}
  have hS_sub : ((↑) : ℍ → ℂ) '' S ⊆ K := by
    rintro _ ⟨τ, ⟨hfd, hY⟩, rfl⟩
    refine ⟨hfd.2, ?_, hY⟩
    have h1 : (1 : ℝ) ≤ Complex.normSq (τ : ℂ) := hfd.1
    rw [Complex.normSq_apply] at h1
    have hab := abs_le.mp hfd.2
    have hre_eq : (τ : ℂ).re = τ.re := rfl
    have him_eq : (τ : ℂ).im = τ.im := rfl
    have hre2 : (τ : ℂ).re ^ 2 ≤ 1 / 4 := by rw [hre_eq]; nlinarith
    have him2 : 3 / 4 ≤ (τ : ℂ).im ^ 2 := by nlinarith
    have hsq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have him_pos : 0 < (τ : ℂ).im := τ.im_pos
    nlinarith [Real.sqrt_nonneg 3]
  have hS_closed : IsClosed S := by
    have hfd_closed : IsClosed ModularGroup.fd := by
      refine (isClosed_le continuous_const (Complex.continuous_normSq.comp
        UpperHalfPlane.continuous_coe)).inter
        (isClosed_le (_root_.continuous_abs.comp (Complex.continuous_re.comp
          UpperHalfPlane.continuous_coe)) continuous_const)
    exact hfd_closed.inter (isClosed_le (Complex.continuous_im.comp UpperHalfPlane.continuous_coe)
      continuous_const)
  have hK_pre_cpt : IsCompact (((↑) : ℍ → ℂ) ⁻¹' K) := by
    have himg : ((↑) : ℍ → ℂ) '' (((↑) : ℍ → ℂ) ⁻¹' K) = K := by
      ext z; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨τ, hτ, heq⟩ => heq ▸ hτ, fun hz => ⟨⟨z, hK_sub hz⟩, hz, rfl⟩⟩
    exact UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_iff.mpr (himg.symm ▸ hK_cpt)
  exact hK_pre_cpt.of_isClosed_subset hS_closed fun τ hτ => hS_sub ⟨τ, hτ, rfl⟩

/- ### Part 2b: Local homeomorphism, surjectivity, and covering map property of `jFn` -/

private def PSet : Set ℂ := ({(0 : ℂ), 1728} : Set ℂ)ᶜ

private lemma mem_PSet_iff {w : ℂ} : w ∈ PSet ↔ w ≠ 0 ∧ w ≠ 1728 := by
  simp [PSet, not_or]

private lemma isOpen_PSet : IsOpen PSet :=
  (isClosed_singleton.union isClosed_singleton).isOpen_compl

private lemma isPathConnected_PSet : IsPathConnected PSet := by
  have hR_pos : (0 : ℝ) < 1729 := by norm_num
  have hcirc : ∀ θ : ℝ, ((1729 : ℝ) : ℂ) * Complex.exp (θ * I) ∈ PSet := by
    intro θ
    rw [mem_PSet_iff]
    have hnorm : ‖((1729 : ℝ) : ℂ) * Complex.exp (θ * I)‖ = 1729 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR_pos.le,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    constructor
    · intro h; rw [h, norm_zero] at hnorm; norm_num at hnorm
    · intro h; rw [h] at hnorm; norm_num at hnorm
  have hjoin_circ : ∀ θ₁ θ₂ : ℝ, JoinedIn PSet (((1729 : ℝ) : ℂ) * Complex.exp (θ₁ * I))
      (((1729 : ℝ) : ℂ) * Complex.exp (θ₂ * I)) := by
    intro θ₁ θ₂
    refine ⟨{
      toFun := fun t => ((1729 : ℝ) : ℂ) * Complex.exp (((1 - (t : ℝ)) * θ₁ + (t : ℝ) * θ₂) * I)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => by simpa using hcirc ((1 - (t : ℝ)) * θ₁ + (t : ℝ) * θ₂)⟩
  have hjoin_base : ∀ u ∈ PSet, JoinedIn PSet u ((1729 : ℝ) : ℂ) := by
    intro u hu
    -- Pick k ∈ {0, 1, 2} such that ray u + t * (1 + k * I) for t ≥ 0 avoids {0, 1728}.
    have hex_k : ∃ k : Fin 3, ∀ t : ℝ, 0 ≤ t → u + (t : ℂ) * (1 + (k : ℂ) * I) ∈ PSet := by
      by_contra hall
      push Not at hall
      choose t ht0 hmem using hall
      have hbad : ∀ k : Fin 3, u + (t k : ℂ) * (1 + (k : ℂ) * I) = 0 ∨
          u + (t k : ℂ) * (1 + (k : ℂ) * I) = 1728 := by
        intro k
        have hk := hmem k
        rw [mem_PSet_iff] at hk
        tauto
      have htpos : ∀ k : Fin 3, 0 < t k := by
        intro k
        rcases eq_or_lt_of_le (ht0 k) with h0 | hp
        · exfalso; have := hmem k; rw [← h0] at this; simp [hu] at this
        · exact hp
      have hinj : ∀ k₁ k₂ : Fin 3,
          u + (t k₁ : ℂ) * (1 + (k₁ : ℂ) * I) = u + (t k₂ : ℂ) * (1 + (k₂ : ℂ) * I) →
          k₁ = k₂ := by
        intro k₁ k₂ heq
        have hmul : (t k₁ : ℂ) * (1 + (k₁ : ℂ) * I) = (t k₂ : ℂ) * (1 + (k₂ : ℂ) * I) :=
          add_left_cancel heq
        have hre : t k₁ = t k₂ := by
          have := congr_arg Complex.re hmul
          simpa using this
        have him : t k₁ * (k₁ : ℝ) = t k₂ * (k₂ : ℝ) := by
          have := congr_arg Complex.im hmul
          simpa using this
        rw [hre] at him
        have hk : (k₁ : ℝ) = (k₂ : ℝ) := mul_left_cancel₀ (htpos k₂).ne' him
        exact Fin.ext (by exact_mod_cast hk)
      rcases hbad 0 with h0 | h0 <;> rcases hbad 1 with h1 | h1 <;> rcases hbad 2 with h2 | h2
      · exact absurd (hinj 0 1 (h0.trans h1.symm)) (by decide)
      · exact absurd (hinj 0 1 (h0.trans h1.symm)) (by decide)
      · exact absurd (hinj 0 2 (h0.trans h2.symm)) (by decide)
      · exact absurd (hinj 1 2 (h1.trans h2.symm)) (by decide)
      · exact absurd (hinj 1 2 (h1.trans h2.symm)) (by decide)
      · exact absurd (hinj 0 2 (h0.trans h2.symm)) (by decide)
      · exact absurd (hinj 0 1 (h0.trans h1.symm)) (by decide)
      · exact absurd (hinj 0 1 (h0.trans h1.symm)) (by decide)
    obtain ⟨k, hk⟩ := hex_k
    let d : ℂ := 1 + (k : ℂ) * I
    have hd_ge : (1 : ℝ) ≤ ‖d‖ := by
      have hre : d.re = 1 := by simp [d]
      calc (1 : ℝ) = |d.re| := by rw [hre]; norm_num
        _ ≤ ‖d‖ := Complex.abs_re_le_norm d
    let T : ℝ := ‖u‖ + 1729
    have hT_pos : 0 < T := by positivity
    let v : ℂ := u + (T : ℂ) * d
    have hv_norm : 1729 ≤ ‖v‖ := by
      have h1 : ‖(T : ℂ) * d‖ - ‖u‖ ≤ ‖v‖ := by
        have := norm_sub_norm_le ((T : ℂ) * d) (-u)
        simpa [v, sub_neg_eq_add, add_comm] using this
      have h2 : T ≤ ‖(T : ℂ) * d‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT_pos.le]
        nlinarith
      linarith
    have huv : JoinedIn PSet u v := by
      refine ⟨{
        toFun := fun s => u + (((s : ℝ) * T : ℝ) : ℂ) * d
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp [v]
      }, fun s => hk ((s : ℝ) * T) (mul_nonneg s.2.1 hT_pos.le)⟩
    have hv_ne : v ≠ 0 := by intro h; rw [h, norm_zero] at hv_norm; linarith
    let w : ℂ := ((1729 : ℝ) : ℂ) * Complex.exp (v.arg * I)
    have hvw : JoinedIn PSet v w := by
      refine ⟨{
        toFun := fun s => (((1 - (s : ℝ)) * ‖v‖ + (s : ℝ) * 1729 : ℝ) : ℂ) *
          Complex.exp (v.arg * I)
        continuous_toFun := by fun_prop
        source' := by
          simp [Complex.norm_mul_exp_arg_mul_I]
        target' := by simp [w]
      }, fun s => ?_⟩
      rw [mem_PSet_iff]
      have hr : 1729 ≤ (1 - (s : ℝ)) * ‖v‖ + (s : ℝ) * 1729 := by
        nlinarith [s.2.1, s.2.2, hv_norm]
      have hnorm : ‖(((1 - (s : ℝ)) * ‖v‖ + (s : ℝ) * 1729 : ℝ) : ℂ) *
          Complex.exp (v.arg * I)‖ = (1 - (s : ℝ)) * ‖v‖ + (s : ℝ) * 1729 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
          Complex.norm_exp_ofReal_mul_I, mul_one]
      constructor
      · intro h
        change (((1 - (s : ℝ)) * ‖v‖ + (s : ℝ) * 1729 : ℝ) : ℂ) * Complex.exp (v.arg * I) = 0 at h
        rw [h, norm_zero] at hnorm; linarith
      · intro h
        change (((1 - (s : ℝ)) * ‖v‖ + (s : ℝ) * 1729 : ℝ) : ℂ) * Complex.exp (v.arg * I) = 1728 at h
        rw [h] at hnorm; norm_num at hnorm; linarith
    have hw_base : JoinedIn PSet w ((1729 : ℝ) : ℂ) := by
      simpa [w] using hjoin_circ v.arg 0
    exact (huv.trans hvw).trans hw_base
  refine ⟨(1729 : ℝ), by rw [mem_PSet_iff]; norm_num, fun y hy => (hjoin_base y hy).symm⟩

private lemma jFn_hasStrictDerivAt (τ : ℍ) :
    HasStrictDerivAt (jFn ∘ UpperHalfPlane.ofComplex)
      (-2 * Real.pi * I * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ /
        ModularForm.discriminant τ) (τ : ℂ) := by
  have hdiff : DifferentiableOn ℂ (jFn ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet := fun z hz =>
    (hasDerivAt_jFn ⟨z, hz⟩).differentiableAt.differentiableWithinAt
  have hana : AnalyticAt ℂ (jFn ∘ UpperHalfPlane.ofComplex) (τ : ℂ) :=
    hdiff.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  simpa [(hasDerivAt_jFn τ).deriv] using hana.hasStrictDerivAt

private lemma jFn_openPartialHomeomorph {τ : ℍ} (hτ : τ ∈ H') :
    ∃ φ : OpenPartialHomeomorph ℍ ℂ, τ ∈ φ.source ∧ φ.source ⊆ H' ∧
      ∀ x ∈ φ.source, φ x = jFn x := by
  let d := -2 * Real.pi * I * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ /
    ModularForm.discriminant τ
  have hd : d ≠ 0 := jFn_deriv_ne_zero hτ
  have hsd := jFn_hasStrictDerivAt τ
  let ψ := (hsd.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph (jFn ∘ UpperHalfPlane.ofComplex)
  have hτ_src : (τ : ℂ) ∈ ψ.source := (hsd.hasStrictFDerivAt_equiv hd).mem_toOpenPartialHomeomorph_source
  have hψ_coe : ∀ z, ψ z = (jFn ∘ UpperHalfPlane.ofComplex) z := fun _ => rfl
  let U_ℂ : Set ℂ := ψ.source ∩ ((↑) : ℍ → ℂ) '' H'
  have hU_ℂ_open : IsOpen U_ℂ := ψ.open_source.inter
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_H')
  have hU_ℂ_sub : U_ℂ ⊆ ψ.source := inter_subset_left
  let ψ' := ψ.restrOpen U_ℂ hU_ℂ_open
  have hτ_src' : (τ : ℂ) ∈ ψ'.source := ⟨hτ_src, ⟨hτ_src, ⟨τ, hτ, rfl⟩⟩⟩
  let e : OpenPartialHomeomorph ℍ ℂ := UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : ℍ → ℂ)
  let φ : OpenPartialHomeomorph ℍ ℂ := e.trans ψ'
  refine ⟨φ, ?_, ?_, ?_⟩
  · refine ⟨trivial, ?_⟩
    exact hτ_src'
  · intro x hx
    have hx' : (x : ℂ) ∈ U_ℂ := hx.2.2
    obtain ⟨y, hy, hyx⟩ := hx'.2
    have hxy : y = x := UpperHalfPlane.coe_injective hyx
    exact hxy ▸ hy
  · intro x _
    change jFn (UpperHalfPlane.ofComplex (x : ℂ)) = jFn x
    rw [UpperHalfPlane.ofComplex_apply]

private lemma jFn_surjective_on_H' : ∀ w ∈ PSet, ∃ τ ∈ H', jFn τ = w := by
  let S : Set PSet := {w : PSet | ∃ τ ∈ H', jFn τ = w.1}
  have hS_nonempty : S.Nonempty := by
    have h4 := tendsto_atImInfty_E4.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
    have h6 := tendsto_atImInfty_E6.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨Y, -, hY⟩ := (UpperHalfPlane.atImInfty_basis.eventually_iff.mp (h4.and h6))
    let τ : ℍ := ⟨((max Y 1 : ℝ) : ℂ) * I, by simp⟩
    have hτ_im : Y ≤ τ.im := by simp [τ]
    obtain ⟨h4τ, h6τ⟩ := hY hτ_im
    have h4ne : ModularForm.E₄ τ ≠ 0 := by
      intro h; rw [h] at h4τ; simp at h4τ; norm_num at h4τ
    have h6ne : ModularForm.E₆ τ ≠ 0 := by
      intro h; rw [h] at h6τ; simp at h6τ; norm_num at h6τ
    have hτH' : τ ∈ H' := ⟨h4ne, h6ne⟩
    have hwP : jFn τ ∈ PSet := mem_PSet_iff.mpr ((jFn_ne_zero_and_1728_iff τ).mp hτH')
    exact ⟨⟨jFn τ, hwP⟩, τ, hτH', rfl⟩
  have hS_open : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro ⟨w, hw⟩ ⟨τ, hτ, rfl⟩
    obtain ⟨φ, hτ_src, hsrc_sub, hφ_eq⟩ := jFn_openPartialHomeomorph hτ
    refine ⟨Subtype.val ⁻¹' φ.target, ?_, φ.open_target.preimage continuous_subtype_val, ?_⟩
    · rintro ⟨z, hz⟩ hz_tgt
      refine ⟨φ.symm z, hsrc_sub (φ.map_target hz_tgt), ?_⟩
      rw [← hφ_eq _ (φ.map_target hz_tgt), φ.right_inv hz_tgt]
    · change jFn τ ∈ φ.target
      rw [← hφ_eq τ hτ_src]
      exact φ.map_source hτ_src
  have hS_closed : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    rintro ⟨w, hw⟩ hw_cl
    rw [mem_closure_iff_seq_limit] at hw_cl
    obtain ⟨u, huS, hu_lim⟩ := hw_cl
    choose τ hτH' hτ_eq using huS
    have hlim_ℂ : Tendsto (fun n => jFn (τ n)) atTop (𝓝 w) := by
      have := (continuous_subtype_val.tendsto ⟨w, hw⟩).comp hu_lim
      exact this.congr fun n => (hτ_eq n).symm
    obtain ⟨Y, -, hY⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp
      (tendsto_norm_jFn_atImInfty.eventually (Filter.eventually_gt_atTop (‖w‖ + 1)))
    have hbdd : ∀ᶠ n in atTop, ‖jFn (τ n)‖ < ‖w‖ + 1 := by
      have := hlim_ℂ.norm.eventually (Iio_mem_nhds (by linarith : ‖w‖ < ‖w‖ + 1))
      exact this
    choose γ hγ_fd using fun n => ModularGroup.exists_smul_mem_fd (τ n)
    let σ : ℕ → ℍ := fun n => γ n • τ n
    have hσ_lim : Tendsto (fun n => jFn (σ n)) atTop (𝓝 w) :=
      hlim_ℂ.congr fun n => (jFn_smul (γ n) (τ n)).symm
    have hσ_mem : ∀ᶠ n in atTop, σ n ∈ {ξ : ℍ | ξ ∈ ModularGroup.fd ∧ ξ.im ≤ Y} := by
      filter_upwards [hbdd] with n hn
      refine ⟨hγ_fd n, ?_⟩
      by_contra hgt
      push Not at hgt
      have h1 := hY (le_of_lt hgt)
      rw [jFn_smul] at h1
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp hσ_mem
    obtain ⟨ξ, -, φn, hφn_mono, hφn_lim⟩ := (isCompact_fd_im_le Y).tendsto_subseq
      (fun n => hN (n + N) (Nat.le_add_left N n))
    have hξ_eq : jFn ξ = w := by
      have h1 : Tendsto (fun n => jFn (σ (φn n + N))) atTop (𝓝 (jFn ξ)) :=
        (jFn_continuous.tendsto ξ).comp hφn_lim
      have hadd : Tendsto (fun n => φn n + N) atTop atTop :=
        Filter.tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hφn_mono.tendsto_atTop
      have h2 : Tendsto (fun n => jFn (σ (φn n + N))) atTop (𝓝 w) :=
        hσ_lim.comp hadd
      exact tendsto_nhds_unique h1 h2
    have hξH' : ξ ∈ H' := (jFn_ne_zero_and_1728_iff ξ).mpr (hξ_eq ▸ mem_PSet_iff.mp hw)
    exact ⟨ξ, hξH', hξ_eq⟩
  have : PreconnectedSpace PSet :=
    isPreconnected_iff_preconnectedSpace.mp isPathConnected_PSet.isConnected.isPreconnected
  have hS_univ : S = univ :=
    (isClopen_iff.mp ⟨hS_closed, hS_open⟩).resolve_left hS_nonempty.ne_empty
  intro w hw
  have : (⟨w, hw⟩ : PSet) ∈ S := hS_univ.symm ▸ trivial
  exact this

private def PSL2ZRel (γ₁ γ₂ : SL(2, ℤ)) : Prop := γ₁ = γ₂ ∨ γ₁ = -γ₂

private def PSL2ZQuot : Type := Quot PSL2ZRel

private instance : TopologicalSpace PSL2ZQuot := ⊥

private instance : DiscreteTopology PSL2ZQuot := ⟨rfl⟩

private lemma neg_one_smul_H (τ : ℍ) : (-1 : SL(2, ℤ)) • τ = τ := by
  ext
  simp

private lemma neg_smul_H (γ : SL(2, ℤ)) (τ : ℍ) : (-γ) • τ = γ • τ := by
  rw [show -γ = γ * (-1) by simp, mul_smul, neg_one_smul_H]

private def pslAct (q : PSL2ZQuot) (τ : ℍ) : ℍ :=
  Quot.lift (fun γ : SL(2, ℤ) => γ • τ)
    (fun γ₁ γ₂ h => by rcases h with rfl | rfl; rfl; exact neg_smul_H γ₂ τ) q

private lemma pslAct_mk (γ : SL(2, ℤ)) (τ : ℍ) : pslAct (Quot.mk _ γ) τ = γ • τ := rfl

private lemma continuous_sl2z_smul (γ : SL(2, ℤ)) : Continuous (fun τ : ℍ => γ • τ) :=
  continuous_const_smul (γ : GL (Fin 2) ℝ)

private lemma pslAct_continuous (q : PSL2ZQuot) : Continuous (pslAct q) := by
  induction q using Quot.ind with | _ γ =>
  exact continuous_sl2z_smul γ

private def pslHomeo (q : PSL2ZQuot) : ℍ ≃ₜ ℍ :=
  Quot.lift
    (fun γ : SL(2, ℤ) =>
      { toFun := fun τ => γ • τ
        invFun := fun τ => γ⁻¹ • τ
        left_inv := fun τ => inv_smul_smul γ τ
        right_inv := fun τ => smul_inv_smul γ τ
        continuous_toFun := continuous_sl2z_smul γ
        continuous_invFun := continuous_sl2z_smul γ⁻¹ })
    (fun γ₁ γ₂ h => by
      rcases h with rfl | rfl
      · rfl
      · ext τ; exact congr_arg UpperHalfPlane.coe (neg_smul_H γ₂ τ)) q

private lemma pslHomeo_apply (q : PSL2ZQuot) (τ : ℍ) : pslHomeo q τ = pslAct q τ := by
  induction q using Quot.ind with | _ γ =>
  change γ • τ = γ • τ
  rfl

private lemma jFn_pslAct (q : PSL2ZQuot) (τ : ℍ) : jFn (pslAct q τ) = jFn τ := by
  induction q using Quot.ind with | _ γ => exact jFn_smul γ τ

private lemma pslAct_mem_H'_iff (q : PSL2ZQuot) (τ : ℍ) : pslAct q τ ∈ H' ↔ τ ∈ H' := by
  induction q using Quot.ind with | _ γ => exact smul_mem_H'_iff γ τ

private def jMap : H' → PSet := fun τ => ⟨jFn τ.1, mem_PSet_iff.mpr ((jFn_ne_zero_and_1728_iff τ.1).mp τ.2)⟩

private lemma isCoveringMap_jMap : IsCoveringMap jMap := by
  intro w
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp isOpen_PSet w.1 w.2
  obtain ⟨Y, -, hY⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp
    (tendsto_norm_jFn_atImInfty.eventually (Filter.eventually_gt_atTop (‖w.1‖ + r)))
  let F_Y : Set ℍ := {τ : ℍ | τ ∈ ModularGroup.fd ∧ τ.im ≤ Y}
  have hFY_cpt : IsCompact F_Y := isCompact_fd_im_le Y
  let S : Set ℍ := {τ : ℍ | τ ∈ F_Y ∧ jFn τ = w.1}
  have hS_cpt : IsCompact S :=
    hFY_cpt.of_isClosed_subset (hFY_cpt.isClosed.inter (isClosed_singleton.preimage jFn_continuous))
      (fun _ h => h.1)
  have hS_H' : ∀ τ ∈ S, τ ∈ H' := fun τ hτ =>
    (jFn_ne_zero_and_1728_iff τ).mpr (hτ.2.symm ▸ mem_PSet_iff.mp w.2)
  have hS_fin : S.Finite := by
    refine hS_cpt.finite ?_
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro τ hτ
    obtain ⟨φ, hτ_src, -, hφ_eq⟩ := jFn_openPartialHomeomorph (hS_H' τ hτ)
    refine ⟨φ.source, φ.open_source, subset_antisymm ?_ (singleton_subset_iff.mpr ⟨hτ_src, hτ⟩)⟩
    rintro τ' ⟨hτ'_src, hτ'_S⟩
    rw [mem_singleton_iff]
    exact φ.injOn hτ'_src hτ_src ((hφ_eq τ' hτ'_src).trans (hτ'_S.2.trans hτ.2.symm) |>.trans
      (hφ_eq τ hτ_src).symm)
  -- Pick a finite set T ⊆ S of pairwise distinct SL(2, ℤ)-orbit representatives.
  have hex_T : ∃ T : Finset ℍ, (∀ τ ∈ T, τ ∈ S) ∧
      (∀ τ ∈ S, ∃ τ' ∈ T, ∃ γ : SL(2, ℤ), γ • τ' = τ) ∧
      (∀ τ₁ ∈ T, ∀ τ₂ ∈ T, (∃ γ : SL(2, ℤ), γ • τ₁ = τ₂) → τ₁ = τ₂) := by
    have haux : ∀ A : Finset ℍ, (∀ τ ∈ A, τ ∈ S) →
        ∃ T : Finset ℍ, (∀ τ ∈ T, τ ∈ S) ∧
          (∀ τ ∈ A, ∃ τ' ∈ T, ∃ γ : SL(2, ℤ), γ • τ' = τ) ∧
          (∀ τ₁ ∈ T, ∀ τ₂ ∈ T, (∃ γ : SL(2, ℤ), γ • τ₁ = τ₂) → τ₁ = τ₂) := by
      intro A
      classical
      refine Finset.induction_on A ?_ (fun {a B} ha ih hAB => ?_)
      · intro _
        exact ⟨∅, by simp, by simp, by simp⟩
      · obtain ⟨T, hTS, hTB, hTdisj⟩ := ih (fun τ hτ => hAB τ (Finset.mem_insert_of_mem hτ))
        by_cases horb : ∃ τ' ∈ T, ∃ γ : SL(2, ℤ), γ • τ' = a
        · refine ⟨T, hTS, fun τ hτ => ?_, hTdisj⟩
          rcases Finset.mem_insert.mp hτ with rfl | hB
          · exact horb
          · exact hTB τ hB
        · refine ⟨insert a T, ?_, ?_, ?_⟩
          · intro τ hτ
            rcases Finset.mem_insert.mp hτ with rfl | hT
            · exact hAB τ (Finset.mem_insert_self τ B)
            · exact hTS τ hT
          · intro τ hτ
            rcases Finset.mem_insert.mp hτ with rfl | hB
            · exact ⟨τ, Finset.mem_insert_self τ T, 1, one_smul _ _⟩
            · obtain ⟨τ', hτ'T, γ, hγ⟩ := hTB τ hB
              exact ⟨τ', Finset.mem_insert_of_mem hτ'T, γ, hγ⟩
          · intro τ₁ hτ₁ τ₂ hτ₂ ⟨γ, hγ⟩
            rcases Finset.mem_insert.mp hτ₁ with rfl | h₁ <;>
              rcases Finset.mem_insert.mp hτ₂ with rfl | h₂
            · rfl
            · exfalso; exact horb ⟨τ₂, h₂, γ⁻¹, by rw [← hγ, inv_smul_smul]⟩
            · exfalso; exact horb ⟨τ₁, h₁, γ, hγ⟩
            · exact hTdisj τ₁ h₁ τ₂ h₂ ⟨γ, hγ⟩
    obtain ⟨T, h1, h2, h3⟩ := haux hS_fin.toFinset (fun τ hτ => hS_fin.mem_toFinset.mp hτ)
    exact ⟨T, h1, fun τ hτ => h2 τ (hS_fin.mem_toFinset.mpr hτ), h3⟩
  obtain ⟨T, hTS, hTcover, hTdisj⟩ := hex_T
  have hT_nonempty : T.Nonempty := by
    obtain ⟨τ₀, -, hτ₀⟩ := jFn_surjective_on_H' w.1 w.2
    obtain ⟨γ₀, hγ₀⟩ := ModularGroup.exists_smul_mem_fd τ₀
    have hmemS : γ₀ • τ₀ ∈ S := by
      refine ⟨⟨hγ₀, ?_⟩, (jFn_smul γ₀ τ₀).trans hτ₀⟩
      by_contra hgt; push Not at hgt
      have := hY (le_of_lt hgt)
      rw [jFn_smul, hτ₀] at this
      linarith
    obtain ⟨τ', hτ'T, -⟩ := hTcover (γ₀ • τ₀) hmemS
    exact ⟨τ', hτ'T⟩
  -- For each τ ∈ T, pick a local homeomorphism and a compact neighborhood inside its source.
  choose φ hφ_mem hφ_sub hφ_eq using fun τ : {x // x ∈ T} =>
    jFn_openPartialHomeomorph (hS_H' τ.1 (hTS τ.1 τ.2))
  choose K hK_nhds hK_sub hK_cpt using fun τ : {x // x ∈ T} =>
    LocallyCompactSpace.local_compact_nhds τ.1 (φ τ).source ((φ τ).open_source.mem_nhds (hφ_mem τ))
  let Kall : Set ℍ := ⋃ τ : {x // x ∈ T}, K τ
  have hKall_cpt : IsCompact Kall := isCompact_iUnion hK_cpt
  -- Use proper discontinuity of 𝒮ℒ on ℍ to get finitely many bad SL(2, ℤ) elements.
  have hbad_fin : {γ : SL(2, ℤ) | ((γ • ·) '' Kall ∩ Kall).Nonempty}.Finite := by
    have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ)
      hKall_cpt hKall_cpt
    have hinj : Function.Injective
        (fun γ : SL(2, ℤ) => (⟨Matrix.SpecialLinearGroup.mapGL ℝ γ, ⟨γ, rfl⟩⟩ : 𝒮ℒ)) := by
      intro γ₁ γ₂ h
      have h1 : Matrix.SpecialLinearGroup.mapGL ℝ γ₁ = Matrix.SpecialLinearGroup.mapGL ℝ γ₂ :=
        congr_arg Subtype.val h
      ext i j
      have h2 : ((γ₁ i j : ℤ) : ℝ) = ((γ₂ i j : ℤ) : ℝ) :=
        congr_arg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h1
      exact_mod_cast h2
    refine hfin.preimage hinj.injOn |>.subset fun γ hγ => ?_
    exact hγ
  -- Shrink neighborhoods W τ ⊆ K τ so translates by distinct orbits/non-±1 are disjoint.
  have hex_W : ∃ W : {x // x ∈ T} → Set ℍ,
      (∀ τ, τ.1 ∈ W τ ∧ IsOpen (W τ) ∧ W τ ⊆ (φ τ).source) ∧
      (∀ (τ₁ τ₂ : {x // x ∈ T}) (γ : SL(2, ℤ)),
        ((γ • ·) '' W τ₁ ∩ W τ₂).Nonempty → τ₁ = τ₂ ∧ (γ = 1 ∨ γ = -1)) := by
    have hpair : ∀ (τ₁ τ₂ : {x // x ∈ T}) (γ : SL(2, ℤ)),
        ¬(τ₁ = τ₂ ∧ (γ = 1 ∨ γ = -1)) →
        ∃ U₁ U₂ : Set ℍ, τ₁.1 ∈ U₁ ∧ IsOpen U₁ ∧ τ₂.1 ∈ U₂ ∧ IsOpen U₂ ∧
          Disjoint ((γ • ·) '' U₁) U₂ := by
      intro τ₁ τ₂ γ hnot
      have hne : γ • τ₁.1 ≠ τ₂.1 := by
        intro heq
        have ht : τ₁ = τ₂ := Subtype.ext (hTdisj τ₁.1 τ₁.2 τ₂.1 τ₂.2 ⟨γ, heq⟩)
        subst ht
        exact hnot ⟨rfl, stabilizer_H'_eq_pm_one (hS_H' τ₁.1 (hTS τ₁.1 τ₁.2)) heq⟩
      obtain ⟨V₁, V₂, hV₁, hV₂, h1, h2, hdisj⟩ := t2_separation hne
      have hcont : Continuous (fun x : ℍ => γ • x) := continuous_const_smul (γ : GL (Fin 2) ℝ)
      refine ⟨(fun x : ℍ => γ • x) ⁻¹' V₁, V₂, h1, hV₁.preimage hcont, h2, hV₂, ?_⟩
      exact hdisj.mono_left (image_preimage_subset _ _)
    let BadTriple : Set ({x // x ∈ T} × {x // x ∈ T} × SL(2, ℤ)) :=
      {p | p.2.2 ∈ {γ : SL(2, ℤ) | ((γ • ·) '' Kall ∩ Kall).Nonempty} ∧
        ¬(p.1 = p.2.1 ∧ (p.2.2 = 1 ∨ p.2.2 = -1))}
    have hBT_fin : BadTriple.Finite := by
      have h1 : (univ ×ˢ univ ×ˢ {γ : SL(2, ℤ) | ((γ • ·) '' Kall ∩ Kall).Nonempty} :
          Set ({x // x ∈ T} × {x // x ∈ T} × SL(2, ℤ))).Finite :=
        finite_univ.prod (finite_univ.prod hbad_fin)
      exact h1.subset fun p hp => ⟨trivial, trivial, hp.1⟩
    choose U1 U2 hU1m hU1o hU2m hU2o hUdisj using fun p : BadTriple =>
      hpair p.1.1 p.1.2.1 p.1.2.2 p.2.2
    let W : {x // x ∈ T} → Set ℍ := fun τ =>
      interior (K τ) ∩ (⋂ p : {q : BadTriple // q.1.1 = τ}, U1 p.1) ∩
        (⋂ p : {q : BadTriple // q.1.2.1 = τ}, U2 p.1)
    have : Finite BadTriple := hBT_fin
    refine ⟨W, fun τ => ⟨?_, ?_, ?_⟩, fun τ₁ τ₂ γ hne => ?_⟩
    · refine ⟨⟨mem_interior_iff_mem_nhds.mpr (hK_nhds τ), ?_⟩, ?_⟩
      · exact mem_iInter.mpr fun (p : {q : BadTriple // q.1.1 = τ}) => by
          have h := hU1m p.1; rwa [p.2] at h
      · exact mem_iInter.mpr fun (p : {q : BadTriple // q.1.2.1 = τ}) => by
          have h := hU2m p.1; rwa [p.2] at h
    · exact (isOpen_interior.inter
        (isOpen_iInter_of_finite fun (p : {q : BadTriple // q.1.1 = τ}) => hU1o p.1)).inter
        (isOpen_iInter_of_finite fun (p : {q : BadTriple // q.1.2.1 = τ}) => hU2o p.1)
    · exact (inter_subset_left.trans inter_subset_left).trans (interior_subset.trans (hK_sub τ))
    · by_contra hnot
      have hγ_bad : γ ∈ {γ' : SL(2, ℤ) | ((γ' • ·) '' Kall ∩ Kall).Nonempty} := by
        obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hne
        exact ⟨γ • x, ⟨x, mem_iUnion.mpr ⟨τ₁, interior_subset hx.1.1⟩, rfl⟩,
          mem_iUnion.mpr ⟨τ₂, interior_subset hy.1.1⟩⟩
      let p : BadTriple := ⟨(τ₁, τ₂, γ), ⟨hγ_bad, hnot⟩⟩
      obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hne
      have hx1 : x ∈ U1 p := (mem_iInter.mp hx.1.2) ⟨p, rfl⟩
      have hy2 : γ • x ∈ U2 p := (mem_iInter.mp hy.2) ⟨p, rfl⟩
      exact (hUdisj p).le_bot ⟨⟨x, hx1, rfl⟩, hy2⟩
  obtain ⟨W, hW_prop, hW_disj⟩ := hex_W
  -- Shrink δ ∈ (0, r] so ball w.1 δ is inside every jFn '' W τ and its preimage is covered.
  have hball_in_imgs : ∃ δ₁ > 0, δ₁ ≤ r ∧ ∀ τ : {x // x ∈ T}, ball w.1 δ₁ ⊆ jFn '' W τ := by
    have hopen : IsOpen (ball w.1 r ∩ ⋂ τ : {x // x ∈ T}, jFn '' W τ) := by
      refine isOpen_ball.inter (isOpen_iInter_of_finite fun τ => ?_)
      have himg : jFn '' W τ = (φ τ) '' W τ :=
        image_congr fun x hx => (hφ_eq τ x ((hW_prop τ).2.2 hx)).symm
      rw [himg]
      exact (φ τ).isOpen_image_of_subset_source (hW_prop τ).2.1 (hW_prop τ).2.2
    have hmem : w.1 ∈ ball w.1 r ∩ ⋂ τ : {x // x ∈ T}, jFn '' W τ :=
      ⟨mem_ball_self hr_pos, mem_iInter.mpr fun τ => ⟨τ.1, (hW_prop τ).1, (hTS τ.1 τ.2).2⟩⟩
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.isOpen_iff.mp hopen w.1 hmem
    refine ⟨δ₁, hδ₁, ?_, fun τ => hsub.trans (inter_subset_right.trans (iInter_subset _ τ))⟩
    by_contra hgt; push Not at hgt
    have : w.1 + (r : ℂ) ∈ ball w.1 δ₁ := by
      rw [mem_ball_iff_norm]; simp [abs_of_pos hr_pos, hgt]
    have h2 := (hsub this).1
    rw [mem_ball_iff_norm] at h2
    simp [abs_of_pos hr_pos] at h2
  obtain ⟨δ₁, hδ₁_pos, hδ₁_le, hδ₁_sub⟩ := hball_in_imgs
  have hex_δ : ∃ δ > 0, δ ≤ δ₁ ∧
      ∀ τ : ℍ, jFn τ ∈ ball w.1 δ → ∃ τ' : {x // x ∈ T}, ∃ γ : SL(2, ℤ), τ ∈ (γ • ·) '' W τ' := by
    by_contra hno
    push Not at hno
    have hseq : ∀ n : ℕ, ∃ τ : ℍ, jFn τ ∈ ball w.1 (δ₁ / (n + 1)) ∧
        ∀ (τ' : {x // x ∈ T}) (γ : SL(2, ℤ)), τ ∉ (γ • ·) '' W τ' :=
      fun n => hno (δ₁ / (n + 1)) (by positivity) (div_le_self hδ₁_pos.le (by linarith))
    choose τ hτ_ball hτ_out using hseq
    choose γ hγ_fd using fun n => ModularGroup.exists_smul_mem_fd (τ n)
    let σ : ℕ → ℍ := fun n => γ n • τ n
    have hσ_mem : ∀ n, σ n ∈ F_Y := by
      intro n
      refine ⟨hγ_fd n, ?_⟩
      by_contra hgt; push Not at hgt
      have h1 := hY (le_of_lt hgt)
      rw [jFn_smul] at h1
      have h2 := mem_ball_iff_norm.mp (hτ_ball n)
      have h3 : δ₁ / (n + 1 : ℝ) ≤ r := le_trans (div_le_self hδ₁_pos.le (by linarith)) hδ₁_le
      have h4 : ‖jFn (τ n)‖ ≤ ‖jFn (τ n) - w.1‖ + ‖w.1‖ := by
        simpa using norm_add_le (jFn (τ n) - w.1) w.1
      linarith
    obtain ⟨ξ, hξ_FY, φn, hφn_mono, hφn_lim⟩ := hFY_cpt.tendsto_subseq hσ_mem
    have hξ_eq : jFn ξ = w.1 := by
      have h1 : Tendsto (fun n => jFn (σ (φn n))) atTop (𝓝 (jFn ξ)) :=
        (jFn_continuous.tendsto ξ).comp hφn_lim
      have h2 : Tendsto (fun n => jFn (σ (φn n))) atTop (𝓝 w.1) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_gt (δ₁ / ε)
        refine ⟨N, fun n hn => ?_⟩
        rw [jFn_smul, dist_eq_norm]
        have hb := mem_ball_iff_norm.mp (hτ_ball (φn n))
        have hle : (N : ℝ) ≤ (φn n : ℝ) := by exact_mod_cast le_trans hn (hφn_mono.id_le n)
        have hdiv : δ₁ / ((φn n : ℝ) + 1) < ε := by
          rw [div_lt_iff₀ (by positivity)]
          have : δ₁ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
          nlinarith
        exact hb.trans hdiv
      exact tendsto_nhds_unique h1 h2
    have hξ_S : ξ ∈ S := ⟨hξ_FY, hξ_eq⟩
    obtain ⟨τ', hτ'T, γ₀, hγ₀⟩ := hTcover ξ hξ_S
    let Uopen : Set ℍ := (γ₀ • ·) '' W ⟨τ', hτ'T⟩
    have hUopen : IsOpen Uopen := by
      let hhom : Homeomorph ℍ ℍ := pslHomeo (Quot.mk _ γ₀)
      have heqU : Uopen = hhom '' W ⟨τ', hτ'T⟩ :=
        image_congr fun x _ => by rw [← pslAct_mk γ₀ x]; exact (pslHomeo_apply (Quot.mk _ γ₀) x).symm
      rw [heqU]
      exact hhom.isOpenMap _ (hW_prop ⟨τ', hτ'T⟩).2.1
    have hξ_mem : ξ ∈ Uopen := ⟨τ', (hW_prop ⟨τ', hτ'T⟩).1, hγ₀⟩
    obtain ⟨n, hn⟩ := (hφn_lim.eventually (hUopen.mem_nhds hξ_mem)).exists
    obtain ⟨x, hxW, hx_eq⟩ := hn
    apply hτ_out (φn n) ⟨τ', hτ'T⟩ ((γ (φn n))⁻¹ * γ₀)
    refine ⟨x, hxW, ?_⟩
    dsimp only at hx_eq ⊢
    rw [mul_smul, hx_eq]
    exact inv_smul_smul (γ (φn n)) (τ (φn n))
  obtain ⟨δ, hδ_pos, hδ_le, hδ_cover⟩ := hex_δ
  -- Construct trivialization over V = Subtype.val ⁻¹' ball w.1 δ with fiber PSL2ZQuot × {x // x ∈ T}.
  let V : Set PSet := Subtype.val ⁻¹' ball w.1 δ
  have hV_open : IsOpen V := isOpen_ball.preimage continuous_subtype_val
  have hwV : w ∈ V := mem_ball_self hδ_pos
  let ι := PSL2ZQuot × {x // x ∈ T}
  have : Nonempty ι := ⟨(Quot.mk _ 1, ⟨hT_nonempty.choose, hT_nonempty.choose_spec⟩)⟩
  have : Nonempty (PSet → H') := ⟨fun _ => ⟨hT_nonempty.choose,
    hS_H' _ (hTS _ hT_nonempty.choose_spec)⟩⟩
  let U : ι → Set H' := fun i =>
    Subtype.val ⁻¹' (pslAct i.1 '' (W i.2 ∩ jFn ⁻¹' ball w.1 δ))
  have hU_open : ∀ i, IsOpen (U i) := fun i => by
    have h1 : IsOpen (W i.2 ∩ jFn ⁻¹' ball w.1 δ) :=
      (hW_prop i.2).2.1.inter (isOpen_ball.preimage jFn_continuous)
    have h2 : IsOpen (pslAct i.1 '' (W i.2 ∩ jFn ⁻¹' ball w.1 δ)) := by
      have heq : pslAct i.1 '' (W i.2 ∩ jFn ⁻¹' ball w.1 δ) =
          (pslHomeo i.1) '' (W i.2 ∩ jFn ⁻¹' ball w.1 δ) :=
        image_congr fun x _ => (pslHomeo_apply i.1 x).symm
      rw [heq]
      exact (pslHomeo i.1).isOpenMap _ h1
    exact h2.preimage continuous_subtype_val
  have hU_inj : ∀ i, (U i).InjOn jMap := by
    intro ⟨q, τ'⟩ x hx y hy hxy
    obtain ⟨x₀, ⟨hx₀W, -⟩, hx₀eq⟩ := hx
    obtain ⟨y₀, ⟨hy₀W, -⟩, hy₀eq⟩ := hy
    have hj : jFn x₀ = jFn y₀ := by
      have h1 : jFn x.1 = jFn y.1 := congr_arg Subtype.val hxy
      rw [← hx₀eq, ← hy₀eq, jFn_pslAct, jFn_pslAct] at h1
      exact h1
    have hxy0 : x₀ = y₀ := (φ τ').injOn ((hW_prop τ').2.2 hx₀W) ((hW_prop τ').2.2 hy₀W)
      ((hφ_eq τ' x₀ ((hW_prop τ').2.2 hx₀W)).trans (hj.trans
        (hφ_eq τ' y₀ ((hW_prop τ').2.2 hy₀W)).symm))
    exact Subtype.ext (hx₀eq.symm.trans (by rw [hxy0, hy₀eq]))
  have hU_surj : ∀ i, (U i).SurjOn jMap V := by
    intro ⟨q, τ'⟩ v hv
    have hv_ball : v.1 ∈ ball w.1 δ₁ := ball_subset_ball hδ_le hv
    obtain ⟨x₀, hx₀W, hx₀eq⟩ := hδ₁_sub τ' hv_ball
    have hxH' : pslAct q x₀ ∈ H' :=
      (pslAct_mem_H'_iff q x₀).mpr ((hφ_sub τ') ((hW_prop τ').2.2 hx₀W))
    refine ⟨⟨pslAct q x₀, hxH'⟩, ⟨x₀, ⟨hx₀W, by change jFn x₀ ∈ ball w.1 δ; rw [hx₀eq]; exact hv⟩, rfl⟩, ?_⟩
    exact Subtype.ext ((jFn_pslAct q x₀).trans hx₀eq)
  have hU_disj : Pairwise (Disjoint on U) := by
    rintro ⟨q₁, τ₁⟩ ⟨q₂, τ₂⟩ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨x₁, ⟨hx₁W, -⟩, hx₁eq⟩ := hx₁
    obtain ⟨x₂, ⟨hx₂W, -⟩, hx₂eq⟩ := hx₂
    induction q₁ using Quot.ind with | _ γ₁ =>
    induction q₂ using Quot.ind with | _ γ₂ =>
    have hmul : (γ₂⁻¹ * γ₁) • x₁ = x₂ := by
      rw [mul_smul, show γ₁ • x₁ = x.1 from hx₁eq, show x.1 = γ₂ • x₂ from hx₂eq.symm, inv_smul_smul]
    obtain ⟨hτ, hγ⟩ := hW_disj τ₁ τ₂ (γ₂⁻¹ * γ₁) ⟨x₂, ⟨x₁, hx₁W, hmul⟩, hx₂W⟩
    apply hne
    refine Prod.ext ?_ hτ
    apply Quot.sound
    rcases hγ with h1 | h1
    · left; exact inv_mul_eq_one.mp h1 |>.symm
    · right
      have : γ₁ = γ₂ * (-1) := by
        calc γ₁ = γ₂ * (γ₂⁻¹ * γ₁) := by group
          _ = γ₂ * (-1) := by rw [h1]
      simpa using this
  have hU_exh : jMap ⁻¹' V ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨τ', γ, y, hyW, hy_eq⟩ := hδ_cover x.1 hx
    refine mem_iUnion.mpr ⟨(Quot.mk _ γ, τ'), y, ⟨hyW, ?_⟩, hy_eq⟩
    change jFn y ∈ ball w.1 δ
    have : jFn y = jFn x.1 := by rw [← hy_eq, jFn_smul]
    rw [this]; exact hx
  have hU_open_iff : ∀ i {W'}, W' ⊆ V → (IsOpen W' ↔ IsOpen (jMap ⁻¹' W' ∩ U i)) := by
    intro ⟨q, τ'⟩ W' hW'V
    constructor
    · intro hW'
      exact (hW'.preimage (jFn_continuous.comp continuous_subtype_val |>.subtype_mk _)).inter
        (hU_open (q, τ'))
    · intro hpre
      -- Map hpre through pslHomeo q⁻¹ and φ τ' to show Subtype.val '' W' is open in ℂ.
      let A : Set ℍ := (pslHomeo q).symm '' (((↑) : H' → ℍ) '' (jMap ⁻¹' W' ∩ U (q, τ')))
      have hA_open : IsOpen A :=
        (pslHomeo q).symm.isOpenMap _ (isOpen_H'.isOpenMap_subtype_val _ hpre)
      have hA_sub : A ⊆ (φ τ').source := by
        rintro _ ⟨_, ⟨x, ⟨-, hxU⟩, rfl⟩, rfl⟩
        obtain ⟨x₀, ⟨hx₀W, -⟩, hx₀eq⟩ := hxU
        have : (pslHomeo q).symm x.1 = x₀ := by
          rw [← hx₀eq, ← pslHomeo_apply, Homeomorph.symm_apply_apply]
        rw [this]
        exact (hW_prop τ').2.2 hx₀W
      have himg_open : IsOpen ((φ τ') '' A) := (φ τ').isOpen_image_of_subset_source hA_open hA_sub
      have himg_eq : Subtype.val ⁻¹' ((φ τ') '' A) = W' := by
        ext v
        simp only [mem_preimage, mem_image]
        constructor
        · rintro ⟨x₀, ⟨_, ⟨x, ⟨hxW', hxU⟩, rfl⟩, hx₀eq⟩, hv_eq⟩
          have hxU' := hxU
          obtain ⟨y₀, ⟨hy₀W, -⟩, hy₀eq⟩ := hxU
          have hxy : x₀ = y₀ := by
            rw [← hx₀eq, ← hy₀eq, ← pslHomeo_apply, Homeomorph.symm_apply_apply]
          have hjx : jFn x.1 = v.1 := by
            rw [← hv_eq, hφ_eq τ' x₀ (hA_sub ⟨x.1, ⟨x, ⟨hxW', hxU'⟩, rfl⟩, hx₀eq⟩), hxy,
              ← jFn_pslAct q y₀, hy₀eq]
          have : v = jMap x := Subtype.ext hjx.symm
          exact this ▸ hxW'
        · intro hvW'
          obtain ⟨x, hxU, hxj⟩ := hU_surj (q, τ') (hW'V hvW')
          have hx_mem : x ∈ jMap ⁻¹' W' ∩ U (q, τ') := ⟨by simpa [hxj] using hvW', hxU⟩
          obtain ⟨y₀, ⟨hy₀W, -⟩, hy₀eq⟩ := hxU
          refine ⟨y₀, ⟨x.1, ⟨x, hx_mem, rfl⟩, ?_⟩, ?_⟩
          · rw [← hy₀eq, ← pslHomeo_apply, Homeomorph.symm_apply_apply]
          · rw [hφ_eq τ' y₀ ((hW_prop τ').2.2 hy₀W), ← jFn_pslAct q y₀, hy₀eq]
            exact congr_arg Subtype.val hxj
      rw [← himg_eq]
      exact himg_open.preimage continuous_subtype_val
  let triv := hV_open.trivializationDiscrete U V hU_open_iff hU_inj hU_surj hU_disj hU_exh
  exact (IsEvenlyCovered.of_trivialization (t := triv) hwV).to_isEvenlyCovered_preimage

/- ### Part 3: Universal cover `UCov Ω w₀` and bounded holomorphic lift `Φ` -/

private structure UCov (Ω : Set ℂ) (w₀ : Ω) where
  pt : Ω
  path : Path.Homotopic.Quotient w₀ pt

private lemma UCov.ext {Ω : Set ℂ} {w₀ : Ω} {p q : UCov Ω w₀}
    (hpt : p.pt = q.pt) (hpath : HEq p.path q.path) : p = q := by
  cases p; cases q; simp only at hpt hpath; subst hpt; subst hpath; rfl

private def uProj {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) : Ω := p.pt
private def uProjC {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) : ℂ := p.pt.1
private def uBase {Ω : Set ℂ} (w₀ : Ω) : UCov Ω w₀ := ⟨w₀, Path.Homotopic.Quotient.refl w₀⟩

private def segPath {Ω : Set ℂ} {c : ℂ} {r : ℝ} (hsub : ball c r ⊆ Ω)
    {a b : ℂ} (ha : a ∈ ball c r) (hb : b ∈ ball c r) :
    Path (⟨a, hsub ha⟩ : Ω) (⟨b, hsub hb⟩ : Ω) where
  toFun t := ⟨(1 - (t : ℝ)) • a + (t : ℝ) • b,
    hsub (convex_ball c r ha hb (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := by ext; simp
  target' := by ext; simp

private lemma homotopic_in_ball {Ω : Set ℂ} {c : ℂ} {r : ℝ} (hsub : ball c r ⊆ Ω)
    {x y : Ω} (γ₁ γ₂ : Path x y)
    (h₁ : ∀ t, (γ₁ t).1 ∈ ball c r) (h₂ : ∀ t, (γ₂ t).1 ∈ ball c r) :
    Path.Homotopic γ₁ γ₂ := by
  refine ⟨{
    toFun := fun p => ⟨(1 - (p.1 : ℝ)) • (γ₁ p.2).1 + (p.1 : ℝ) • (γ₂ p.2).1,
      hsub (convex_ball c r (h₁ p.2) (h₂ p.2) (sub_nonneg.mpr p.1.2.2) p.1.2.1
        (sub_add_cancel _ _))⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      have hc1 : Continuous fun p : unitInterval × unitInterval => (γ₁ p.2).1 :=
        continuous_subtype_val.comp (γ₁.continuous.comp continuous_snd)
      have hc2 : Continuous fun p : unitInterval × unitInterval => (γ₂ p.2).1 :=
        continuous_subtype_val.comp (γ₂.continuous.comp continuous_snd)
      fun_prop
    map_zero_left := fun s => by ext; simp
    map_one_left := fun s => by ext; simp
    prop' := fun t s hs => by
      rcases hs with rfl | rfl
      · ext; simp [γ₁.source, γ₂.source]; ring
      · ext; simp [γ₁.target, γ₂.target]; ring
  }⟩

private lemma segPath_refl_homotopic {Ω : Set ℂ} {c : ℂ} {r : ℝ} (hsub : ball c r ⊆ Ω)
    {a : ℂ} (ha : a ∈ ball c r) :
    Path.Homotopic.Quotient.mk (segPath hsub ha ha) =
      Path.Homotopic.Quotient.refl (⟨a, hsub ha⟩ : Ω) := by
  apply Quotient.sound
  exact homotopic_in_ball hsub _ _
    (fun t => convex_ball c r ha ha (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _))
    (fun _ => ha)

private lemma segPath_trans_homotopic {Ω : Set ℂ} {c : ℂ} {r : ℝ} (hsub : ball c r ⊆ Ω)
    {a b d : ℂ} (ha : a ∈ ball c r) (hb : b ∈ ball c r) (hd : d ∈ ball c r) :
    (Path.Homotopic.Quotient.mk (segPath hsub ha hb)).trans
      (Path.Homotopic.Quotient.mk (segPath hsub hb hd)) =
      Path.Homotopic.Quotient.mk (segPath hsub ha hd) := by
  rw [← Path.Homotopic.Quotient.mk_trans]
  apply Quotient.sound
  refine homotopic_in_ball hsub _ _ (fun t => ?_)
    (fun t => convex_ball c r ha hd (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _))
  simp only [Path.trans_apply]
  split_ifs with h
  · dsimp only [segPath]
    exact convex_ball c r ha hb (by linarith [t.2.1, h]) (by linarith [t.2.1]) (by ring)
  · dsimp only [segPath]
    exact convex_ball c r hb hd (by linarith [t.2.2]) (by linarith [h]) (by ring)

private def uChart {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r)
    (hsub : ball p.pt.1 r ⊆ Ω) (z : ℂ) (hz : z ∈ ball p.pt.1 r) : UCov Ω w₀ :=
  ⟨⟨z, hsub hz⟩, p.path.trans (Path.Homotopic.Quotient.mk (segPath hsub (mem_ball_self hr) hz))⟩

private lemma path_quot_trans_refl {X : Type*} [TopologicalSpace X] {x y : X}
    (a : Path.Homotopic.Quotient x y) : a.trans (Path.Homotopic.Quotient.refl y) = a := by
  induction a using Quotient.ind with | _ pa =>
  change Path.Homotopic.Quotient.mk (pa.trans (Path.refl y)) = Path.Homotopic.Quotient.mk pa
  exact Quotient.sound ⟨Path.Homotopy.transRefl pa⟩

private lemma path_quot_refl_trans {X : Type*} [TopologicalSpace X] {x y : X}
    (a : Path.Homotopic.Quotient x y) : (Path.Homotopic.Quotient.refl x).trans a = a := by
  induction a using Quotient.ind with | _ pa =>
  change Path.Homotopic.Quotient.mk ((Path.refl x).trans pa) = Path.Homotopic.Quotient.mk pa
  exact Quotient.sound ⟨Path.Homotopy.reflTrans pa⟩

private lemma uChart_self {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r)
    (hsub : ball p.pt.1 r ⊆ Ω) : uChart p hr hsub p.pt.1 (mem_ball_self hr) = p := by
  refine UCov.ext rfl ?_
  simp only [uChart, segPath_refl_homotopic, path_quot_trans_refl]
  rfl

private lemma uChart_pt {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r)
    (hsub : ball p.pt.1 r ⊆ Ω) (z : ℂ) (hz : z ∈ ball p.pt.1 r) :
    (uChart p hr hsub z hz).pt.1 = z := rfl

private lemma path_quot_trans_assoc {X : Type*} [TopologicalSpace X] {x y z w : X}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y z)
    (c : Path.Homotopic.Quotient z w) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  induction a using Quotient.ind with | _ pa =>
  induction b using Quotient.ind with | _ pb =>
  induction c using Quotient.ind with | _ pc =>
  change Path.Homotopic.Quotient.mk ((pa.trans pb).trans pc) =
    Path.Homotopic.Quotient.mk (pa.trans (pb.trans pc))
  exact Quotient.sound (Path.Homotopic.trans_assoc pa pb pc)

private lemma path_quot_trans_symm_cancel {X : Type*} [TopologicalSpace X] {x y z : X}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y z) :
    (a.trans b).trans b.symm = a := by
  rw [path_quot_trans_assoc]
  induction a using Quotient.ind with | _ pa =>
  induction b using Quotient.ind with | _ pb =>
  change Path.Homotopic.Quotient.mk (pa.trans (pb.trans pb.symm)) = Path.Homotopic.Quotient.mk pa
  have h1 : Path.Homotopic (pb.trans pb.symm) (Path.refl y) :=
    ⟨(Path.Homotopy.reflTransSymm pb).symm⟩
  exact Quotient.sound ((Path.Homotopic.hcomp (Path.Homotopic.refl pa) h1).trans
    ⟨Path.Homotopy.transRefl pa⟩)

private lemma uChart_eq_uChart {Ω : Set ℂ} {w₀ : Ω} {p : UCov Ω w₀} {r ρ : ℝ}
    (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
    {q : UCov Ω w₀} (hqz : q.pt.1 ∈ ball p.pt.1 r) (hq : q = uChart p hr hsub q.pt.1 hqz)
    (hρ : 0 < ρ) (hρsub : ball q.pt.1 ρ ⊆ ball p.pt.1 r)
    {z : ℂ} (hz : z ∈ ball q.pt.1 ρ) :
    uChart q hρ (hρsub.trans hsub) z hz = uChart p hr hsub z (hρsub hz) := by
  have hseg : Path.Homotopic.Quotient.mk (segPath (hρsub.trans hsub) (mem_ball_self hρ) hz) =
      Path.Homotopic.Quotient.mk (segPath hsub hqz (hρsub hz)) := by
    apply Quotient.sound
    exact homotopic_in_ball hsub _ _
      (fun t => hρsub (convex_ball q.pt.1 ρ (mem_ball_self hρ) hz
        (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _)))
      (fun t => convex_ball p.pt.1 r hqz (hρsub hz)
        (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _))
  refine UCov.ext rfl ?_
  have hpath : q.path = p.path.trans (Path.Homotopic.Quotient.mk (segPath hsub (mem_ball_self hr) hqz)) := by
    have hq' : q.path ≍ (uChart p hr hsub q.pt.1 hqz).path := by rw [← hq]
    exact eq_of_heq hq'
  apply heq_of_eq
  change q.path.trans (Path.Homotopic.Quotient.mk (segPath (hρsub.trans hsub) (mem_ball_self hρ) hz)) =
    p.path.trans (Path.Homotopic.Quotient.mk (segPath hsub (mem_ball_self hr) (hρsub hz)))
  rw [hpath, hseg, path_quot_trans_assoc, segPath_trans_homotopic]

private def uBall {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r)
    (hsub : ball p.pt.1 r ⊆ Ω) : Set (UCov Ω w₀) :=
  {q | ∃ hz : q.pt.1 ∈ ball p.pt.1 r, q = uChart p hr hsub q.pt.1 hz}

private lemma mem_uBall_self {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r)
    (hsub : ball p.pt.1 r ⊆ Ω) : p ∈ uBall p hr hsub :=
  ⟨mem_ball_self hr, (uChart_self p hr hsub).symm⟩

private lemma uChart_mem_uBall {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r)
    (hsub : ball p.pt.1 r ⊆ Ω) {z : ℂ} (hz : z ∈ ball p.pt.1 r) :
    uChart p hr hsub z hz ∈ uBall p hr hsub :=
  ⟨hz, rfl⟩

private lemma uBall_subset_uBall {Ω : Set ℂ} {w₀ : Ω} {p : UCov Ω w₀} {r ρ : ℝ}
    (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
    {q : UCov Ω w₀} (hq : q ∈ uBall p hr hsub)
    (hρ : 0 < ρ) (hρsub : ball q.pt.1 ρ ⊆ ball p.pt.1 r) :
    uBall q hρ (hρsub.trans hsub) ⊆ uBall p hr hsub := by
  obtain ⟨hqz, hqeq⟩ := hq
  rintro x ⟨hxρ, hxeq⟩
  exact ⟨hρsub hxρ, hxeq.trans (uChart_eq_uChart hr hsub hqz hqeq hρ hρsub hxρ)⟩

private def uBasis (Ω : Set ℂ) (w₀ : Ω) : Set (Set (UCov Ω w₀)) :=
  {S | ∃ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω), S = uBall p hr hsub}

private instance instTopologicalSpaceUCov {Ω : Set ℂ} {w₀ : Ω} : TopologicalSpace (UCov Ω w₀) :=
  TopologicalSpace.generateFrom (uBasis Ω w₀)

private lemma uBasis_isTopologicalBasis {Ω : Set ℂ} (hΩ : IsOpen Ω) (w₀ : Ω) :
    TopologicalSpace.IsTopologicalBasis (uBasis Ω w₀) where
  exists_subset_inter := by
    rintro _ ⟨p₁, r₁, hr₁, hsub₁, rfl⟩ _ ⟨p₂, r₂, hr₂, hsub₂, rfl⟩ q ⟨hq₁, hq₂⟩
    have hq_open : IsOpen (ball p₁.pt.1 r₁ ∩ ball p₂.pt.1 r₂) := isOpen_ball.inter isOpen_ball
    have hq_mem : q.pt.1 ∈ ball p₁.pt.1 r₁ ∩ ball p₂.pt.1 r₂ := ⟨hq₁.1, hq₂.1⟩
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hq_open q.pt.1 hq_mem
    refine ⟨uBall q hρ ((hρsub.trans inter_subset_left).trans hsub₁),
      ⟨q, ρ, hρ, (hρsub.trans inter_subset_left).trans hsub₁, rfl⟩,
      mem_uBall_self q hρ _, subset_inter ?_ ?_⟩
    · exact uBall_subset_uBall hr₁ hsub₁ hq₁ hρ (hρsub.trans inter_subset_left)
    · have hsub2 : uBall q hρ ((hρsub.trans inter_subset_right).trans hsub₂) ⊆ uBall p₂ hr₂ hsub₂ :=
        uBall_subset_uBall hr₂ hsub₂ hq₂ hρ (hρsub.trans inter_subset_right)
      exact hsub2
  sUnion_eq := by
    ext q
    simp only [mem_sUnion, mem_univ, iff_true]
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ q.pt.1 q.pt.2
    exact ⟨uBall q hr hsub, ⟨q, r, hr, hsub, rfl⟩, mem_uBall_self q hr hsub⟩
  eq_generateFrom := rfl

private lemma isOpen_uBall {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω) :
    IsOpen (uBall p hr hsub) :=
  (uBasis_isTopologicalBasis hΩ w₀).isOpen ⟨p, r, hr, hsub, rfl⟩

private lemma continuous_uProjC {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω} :
    Continuous (uProjC (Ω := Ω) (w₀ := w₀)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ p.pt.1 p.pt.2
  let ρ := min r ε
  have hρ : 0 < ρ := lt_min hr hε
  have hρsub : ball p.pt.1 ρ ⊆ Ω := (ball_subset_ball (min_le_left _ _)).trans hsub
  refine Filter.mem_of_superset ((isOpen_uBall hΩ p hρ hρsub).mem_nhds (mem_uBall_self p hρ hρsub))
    fun q hq => ?_
  exact lt_of_lt_of_le (mem_ball.mp hq.1) (min_le_right _ _)

private lemma continuous_uProj {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω} :
    Continuous (uProj (Ω := Ω) (w₀ := w₀)) :=
  (continuous_uProjC hΩ).subtype_mk _

private lemma continuousOn_uChart {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω) :
    Continuous (fun z : ball p.pt.1 r => uChart p hr hsub z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro ⟨z₀, hz₀⟩
  let q := uChart p hr hsub z₀ hz₀
  rw [ContinuousAt, (uBasis_isTopologicalBasis hΩ w₀).nhds_hasBasis.tendsto_right_iff]
  rintro S ⟨⟨p', r', hr', hsub', rfl⟩, hqS⟩
  have hopen : IsOpen (ball p.pt.1 r ∩ ball p'.pt.1 r') := isOpen_ball.inter isOpen_ball
  have hmem : z₀ ∈ ball p.pt.1 r ∩ ball p'.pt.1 r' := ⟨hz₀, hqS.1⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen z₀ hmem
  have hnhds : Subtype.val ⁻¹' ball z₀ ρ ∈ 𝓝 (⟨z₀, hz₀⟩ : ball p.pt.1 r) :=
    (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hρ)
  refine Filter.mem_of_superset hnhds fun ⟨z, hz⟩ hzρ => ?_
  change uChart p hr hsub z hz ∈ uBall p' hr' hsub'
  have h1 : uChart p hr hsub z hz = uChart q hρ ((hρsub.trans inter_subset_left).trans hsub) z hzρ :=
    (uChart_eq_uChart hr hsub hz₀ rfl hρ (hρsub.trans inter_subset_left) hzρ).symm
  rw [h1]
  exact uBall_subset_uBall hr' hsub' hqS hρ (hρsub.trans inter_subset_right)
    (uChart_mem_uBall q hρ _ hzρ)

private lemma uBall_injOn_uProjC {Ω : Set ℂ} {w₀ : Ω}
    (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω) :
    (uBall p hr hsub).InjOn uProjC := by
  rintro q₁ ⟨h₁, hq₁⟩ q₂ ⟨h₂, hq₂⟩ heq
  rw [hq₁, hq₂]
  have h1 : q₁.pt.1 = q₂.pt.1 := heq
  simp only [h1]

private lemma uBall_disjoint_same_pt {Ω : Set ℂ} {w₀ : Ω}
    {p₁ p₂ : UCov Ω w₀} (hpt : p₁.pt = p₂.pt) (hne : p₁ ≠ p₂)
    {r : ℝ} (hr : 0 < r) (hsub₁ : ball p₁.pt.1 r ⊆ Ω) (hsub₂ : ball p₂.pt.1 r ⊆ Ω) :
    Disjoint (uBall p₁ hr hsub₁) (uBall p₂ hr hsub₂) := by
  rw [Set.disjoint_left]
  rintro q ⟨h₁, hq₁⟩ ⟨h₂, hq₂⟩
  have heq : uChart p₁ hr hsub₁ q.pt.1 h₁ = uChart p₂ hr hsub₂ q.pt.1 h₂ := hq₁.symm.trans hq₂
  apply hne
  refine UCov.ext hpt ?_
  cases p₁ with | mk pt₁ γ₁ =>
  cases p₂ with | mk pt₂ γ₂ =>
  dsimp at hpt heq
  subst hpt
  have hpath_eq : γ₁.trans (Path.Homotopic.Quotient.mk (segPath hsub₁ (mem_ball_self hr) h₁)) =
      γ₂.trans (Path.Homotopic.Quotient.mk (segPath hsub₂ (mem_ball_self hr) h₂)) := by
    injection heq with _ hp
  have hcancel : γ₁ = γ₂ := by
    have h1 := congr_arg (fun u => u.trans (Path.Homotopic.Quotient.mk (segPath hsub₂ (mem_ball_self hr) h₂)).symm) hpath_eq
    simpa [path_quot_trans_symm_cancel] using h1
  exact heq_of_eq hcancel

private lemma t2Space_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω) (w₀ : Ω) : T2Space (UCov Ω w₀) := by
  constructor
  intro p₁ p₂ hne
  by_cases hpt : p₁.pt = p₂.pt
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ p₁.pt.1 p₁.pt.2
    have hsub₂ : ball p₂.pt.1 r ⊆ Ω := hpt ▸ hsub
    exact ⟨uBall p₁ hr hsub, uBall p₂ hr hsub₂, isOpen_uBall hΩ p₁ hr hsub,
      isOpen_uBall hΩ p₂ hr hsub₂, mem_uBall_self p₁ hr hsub, mem_uBall_self p₂ hr hsub₂,
      uBall_disjoint_same_pt hpt hne hr hsub hsub₂⟩
  · have hneC : p₁.pt.1 ≠ p₂.pt.1 := fun h => hpt (Subtype.ext h)
    obtain ⟨U, V, hUo, hVo, h1, h2, hdisj⟩ := t2_separation hneC
    exact ⟨uProjC ⁻¹' U, uProjC ⁻¹' V, hUo.preimage (continuous_uProjC hΩ),
      hVo.preimage (continuous_uProjC hΩ), h1, h2, hdisj.preimage uProjC⟩

private lemma locallyPathConnectedSpace_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω) (w₀ : Ω) :
    LocallyPathConnectedSpace (UCov Ω w₀) := by
  constructor
  intro p
  refine (uBasis_isTopologicalBasis hΩ w₀).nhds_hasBasis.to_hasBasis' ?_ fun s hs => hs.1
  rintro S ⟨⟨q, r, hr, hsub, rfl⟩, hpS⟩
  have hball_pc : IsPathConnected (univ : Set (ball q.pt.1 r)) := by
    have : PathConnectedSpace (ball q.pt.1 r) :=
      isPathConnected_iff_pathConnectedSpace.mp ((convex_ball q.pt.1 r).isPathConnected
        ⟨q.pt.1, mem_ball_self hr⟩)
    exact isPathConnected_univ
  have himg : (fun z : ball q.pt.1 r => uChart q hr hsub z.1 z.2) '' univ = uBall q hr hsub := by
    ext x; simp only [mem_image, mem_univ, true_and, uBall, mem_ofPred_eq]
    exact ⟨fun ⟨⟨z, hz⟩, h⟩ => ⟨h ▸ hz, by subst h; rfl⟩, fun ⟨hx, h⟩ => ⟨⟨x.pt.1, hx⟩, h.symm⟩⟩
  refine ⟨uBall q hr hsub, ⟨(isOpen_uBall hΩ q hr hsub).mem_nhds hpS, ?_⟩, subset_rfl⟩
  rw [← himg]
  exact hball_pc.image (continuousOn_uChart hΩ q hr hsub)

private lemma isCoveringMap_uProj {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω) (w₀ : Ω) :
    IsCoveringMap (uProj (Ω := Ω) (w₀ := w₀)) := by
  intro w
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ w.1 w.2
  let V : Set Ω := Subtype.val ⁻¹' ball w.1 r
  have hV_open : IsOpen V := isOpen_ball.preimage continuous_subtype_val
  have hwV : w ∈ V := mem_ball_self hr
  let ι := Path.Homotopic.Quotient w₀ w
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have hjoin : JoinedIn Ω w₀.1 w.1 := hΩc.joinedIn w₀.1 w₀.2 w.1 w.2
  have : Nonempty ι := by
    obtain ⟨γ, hγ⟩ := hjoin
    let γΩ : Path w₀ w :=
      { toFun := fun t => ⟨γ t, hγ t⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    exact ⟨Path.Homotopic.Quotient.mk γΩ⟩
  have : Nonempty (Ω → UCov Ω w₀) := ⟨fun _ => uBase w₀⟩
  let U : ι → Set (UCov Ω w₀) := fun γ => uBall ⟨w, γ⟩ hr hsub
  have hU_open : ∀ γ, IsOpen (U γ) := fun γ => isOpen_uBall hΩ ⟨w, γ⟩ hr hsub
  have hU_inj : ∀ γ, (U γ).InjOn uProj := fun γ q₁ h₁ q₂ h₂ heq =>
    uBall_injOn_uProjC ⟨w, γ⟩ hr hsub h₁ h₂ (congr_arg Subtype.val heq)
  have hU_surj : ∀ γ, (U γ).SurjOn uProj V := fun γ v hv =>
    ⟨uChart ⟨w, γ⟩ hr hsub v.1 hv, uChart_mem_uBall ⟨w, γ⟩ hr hsub hv, Subtype.ext rfl⟩
  have hU_disj : Pairwise (Disjoint on U) := fun γ₁ γ₂ hne =>
    uBall_disjoint_same_pt (p₁ := ⟨w, γ₁⟩) (p₂ := ⟨w, γ₂⟩) rfl
      (fun h => hne (by injection h with _ h')) hr hsub hsub
  have hU_exh : uProj ⁻¹' V ⊆ ⋃ γ, U γ := by
    intro q hq
    have hq_ball : q.pt.1 ∈ ball w.1 r := hq
    let γ : ι := q.path.trans (Path.Homotopic.Quotient.mk (segPath hsub hq_ball (mem_ball_self hr)))
    refine mem_iUnion.mpr ⟨γ, hq_ball, ?_⟩
    refine UCov.ext rfl ?_
    apply heq_of_eq
    change q.path = (q.path.trans (Path.Homotopic.Quotient.mk (segPath hsub hq_ball (mem_ball_self hr)))).trans
      (Path.Homotopic.Quotient.mk (segPath hsub (mem_ball_self hr) hq_ball))
    rw [path_quot_trans_assoc, segPath_trans_homotopic, segPath_refl_homotopic, path_quot_trans_refl]
  have hU_open_iff : ∀ γ {W'}, W' ⊆ V → (IsOpen W' ↔ IsOpen (uProj ⁻¹' W' ∩ U γ)) := by
    intro γ W' hW'V
    constructor
    · intro hW'
      exact (hW'.preimage (continuous_uProj hΩ)).inter (hU_open γ)
    · intro hpre
      let f : ball w.1 r → UCov Ω w₀ := fun z => uChart ⟨w, γ⟩ hr hsub z.1 z.2
      have hf_cont : Continuous f := continuousOn_uChart hΩ ⟨w, γ⟩ hr hsub
      have hopen_b : IsOpen (f ⁻¹' (uProj ⁻¹' W' ∩ U γ)) := hpre.preimage hf_cont
      have hopen_c : IsOpen (((↑) : ball w.1 r → ℂ) '' (f ⁻¹' (uProj ⁻¹' W' ∩ U γ))) :=
        isOpen_ball.isOpenMap_subtype_val _ hopen_b
      have heq_W' : Subtype.val ⁻¹' (((↑) : ball w.1 r → ℂ) '' (f ⁻¹' (uProj ⁻¹' W' ∩ U γ))) = W' := by
        ext v
        simp only [mem_preimage, mem_image, mem_inter_iff]
        constructor
        · rintro ⟨⟨z, hz⟩, ⟨hvW', -⟩, rfl⟩
          exact hvW'
        · intro hvW'
          refine ⟨⟨v.1, hW'V hvW'⟩, ⟨?_, uChart_mem_uBall ⟨w, γ⟩ hr hsub (hW'V hvW')⟩, rfl⟩
          exact hvW'
      rw [← heq_W']
      exact hopen_c.preimage continuous_subtype_val
  let triv := hV_open.trivializationDiscrete U V hU_open_iff hU_inj hU_surj hU_disj hU_exh
  exact (IsEvenlyCovered.of_trivialization (t := triv) hwV).to_isEvenlyCovered_preimage

private def truncPath {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (a b : unitInterval) (hab : a ≤ b) : Path (γ a) (γ b) :=
  (γ.truncate (a : ℝ) (b : ℝ)).cast
    (by rw [min_eq_left (Subtype.coe_le_coe.mpr hab), γ.extend_extends']) (by rw [γ.extend_extends'])

private def trunc0Path {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (b : unitInterval) : Path x₀ (γ b) :=
  (γ.truncate 0 (b : ℝ)).cast (by rw [min_eq_left b.2.1, γ.extend_zero]) (by rw [γ.extend_extends'])

private lemma truncate_trans_homotopic {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) {a b : unitInterval} (hab : a ≤ b) :
    Path.Homotopic (trunc0Path γ b) ((trunc0Path γ a).trans (truncPath γ a b hab)) := by
  let φ₀ : unitInterval → ℝ := fun s => min (s : ℝ) (b : ℝ)
  let φ₁ : unitInterval → ℝ := fun s =>
    if (s : ℝ) ≤ 1 / 2 then min (2 * (s : ℝ)) (a : ℝ)
    else min (max (2 * (s : ℝ) - 1) (a : ℝ)) (b : ℝ)
  have hφ₀_cont : Continuous φ₀ := continuous_subtype_val.min continuous_const
  have hφ₁_cont : Continuous φ₁ := by
    refine Continuous.if_le (continuous_const.mul continuous_subtype_val |>.min continuous_const)
      (((continuous_const.mul continuous_subtype_val |>.sub continuous_const).max continuous_const).min
        continuous_const) continuous_subtype_val continuous_const fun s hs => ?_
    have h2 : 2 * (s : ℝ) = 1 := by linarith
    have ha1 : (a : ℝ) ≤ 1 := a.2.2
    have ha0 : 0 ≤ (a : ℝ) := a.2.1
    have hab' : (a : ℝ) ≤ (b : ℝ) := hab
    simp [h2, min_eq_right ha1, max_eq_right ha0, min_eq_left hab']
  refine ⟨{
    toFun := fun p => γ.extend ((1 - (p.1 : ℝ)) * φ₀ p.2 + (p.1 : ℝ) * φ₁ p.2)
    continuous_toFun := γ.continuous_extend.comp (by fun_prop)
    map_zero_left := fun s => by
      simp [φ₀, trunc0Path, Path.truncate, max_eq_left s.2.1]
    map_one_left := fun s => by
      simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
      change γ.extend (φ₁ s) = ((trunc0Path γ a).trans (truncPath γ a b hab)) s
      rw [Path.trans_apply]
      dsimp only [φ₁, trunc0Path, truncPath, Path.cast_coe, Path.truncate]
      split_ifs with h
      · have h0 : (0 : ℝ) ≤ 2 * (s : ℝ) := by linarith [s.2.1]
        simp [max_eq_left h0]
      · simp
    prop' := fun t s hs => by
      rcases hs with rfl | rfl
      · have h0 : φ₀ 0 = 0 := by simp [φ₀, b.2.1]
        have h1 : φ₁ 0 = 0 := by simp [φ₁, a.2.1]
        change γ.extend ((1 - (t : ℝ)) * φ₀ 0 + (t : ℝ) * φ₁ 0) = trunc0Path γ b 0
        rw [h0, h1, (trunc0Path γ b).source]
        simp [γ.extend_zero]
      · have h0 : φ₀ 1 = (b : ℝ) := by simp [φ₀, b.2.2]
        have h1 : φ₁ 1 = (b : ℝ) := by
          dsimp only [φ₁]
          simp only [Set.Icc.coe_one]
          rw [if_neg (by norm_num : ¬((1 : ℝ) ≤ 1 / 2))]
          have ha1 : (a : ℝ) ≤ 1 := a.2.2
          have hb1 : (b : ℝ) ≤ 1 := b.2.2
          norm_num
          left; exact hb1
        change γ.extend ((1 - (t : ℝ)) * φ₀ 1 + (t : ℝ) * φ₁ 1) = trunc0Path γ b 1
        rw [h0, h1, (trunc0Path γ b).target]
        have heq : (1 - (t : ℝ)) * (b : ℝ) + (t : ℝ) * (b : ℝ) = (b : ℝ) := by ring
        rw [heq, γ.extend_extends']
  }⟩

private lemma uProj_liftPath_endpoint {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (w₀ : Ω) {w : Ω} (γ : Path w₀ w) :
    (isCoveringMap_uProj hΩ hΩc w₀).liftPath γ (uBase w₀) γ.source 1 =
      ⟨w, Path.Homotopic.Quotient.mk γ⟩ := by
  let L : unitInterval → UCov Ω w₀ := fun t => ⟨γ t, Path.Homotopic.Quotient.mk (trunc0Path γ t)⟩
  have hL_proj : uProj ∘ L = γ := by ext t; rfl
  have hL_zero : L 0 = uBase w₀ := by
    refine UCov.ext γ.source ?_
    exact Path.Homotopic.hpath_hext fun s => by
      simp [trunc0Path, Path.truncate, γ.extend_zero]
  have hL_one : L 1 = ⟨w, Path.Homotopic.Quotient.mk γ⟩ := by
    refine UCov.ext γ.target ?_
    exact Path.Homotopic.hpath_hext fun s => by
      simp [trunc0Path, Path.truncate, max_eq_left s.2.1, min_eq_left s.2.2]
  have hL_cont : Continuous L := by
    rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ (γ t₀).1 (γ t₀).2
    have hγ_cont : ContinuousAt (fun t : unitInterval => (γ t).1) t₀ :=
      (continuous_subtype_val.comp γ.continuous).continuousAt
    obtain ⟨δ, hδ, hδ_ball⟩ := Metric.continuousAt_iff.mp hγ_cont r hr
    have hstep : ∀ {a b : unitInterval} (_hab : a ≤ b)
        (ha : dist a t₀ < δ) (hb : dist b t₀ < δ),
        (L b).path = (L a).path.trans
          (Path.Homotopic.Quotient.mk (segPath hsub
            (by simpa [mem_ball] using hδ_ball ha) (by simpa [mem_ball] using hδ_ball hb))) := by
      intro a b hab ha hb
      have htr : Path.Homotopic.Quotient.mk (trunc0Path γ b) =
          (Path.Homotopic.Quotient.mk (trunc0Path γ a)).trans
            (Path.Homotopic.Quotient.mk (truncPath γ a b hab)) := by
        rw [← Path.Homotopic.Quotient.mk_trans]
        exact Quotient.sound (truncate_trans_homotopic γ hab)
      have hseg : Path.Homotopic.Quotient.mk (truncPath γ a b hab) =
          Path.Homotopic.Quotient.mk (segPath hsub
            (by simpa [mem_ball] using hδ_ball ha) (by simpa [mem_ball] using hδ_ball hb)) := by
        apply Quotient.sound
        refine homotopic_in_ball hsub _ _ (fun s => ?_) (fun s =>
          convex_ball (γ t₀).1 r (by simpa [mem_ball] using hδ_ball ha)
            (by simpa [mem_ball] using hδ_ball hb) (sub_nonneg.mpr s.2.2) s.2.1 (sub_add_cancel _ _))
        let u : ℝ := min (max (s : ℝ) (a : ℝ)) (b : ℝ)
        have hu_mem : u ∈ Icc (0 : ℝ) 1 := ⟨le_min (le_trans a.2.1 (le_max_right _ _)) b.2.1,
          min_le_of_right_le b.2.2⟩
        let uI : unitInterval := ⟨u, hu_mem⟩
        have hdist_u : dist uI t₀ < δ := by
          have ha_le : (a : ℝ) ≤ u := le_min (le_max_right _ _) hab
          have hu_le : u ≤ (b : ℝ) := min_le_right _ _
          have ha' : |(a : ℝ) - (t₀ : ℝ)| < δ := by simpa [Subtype.dist_eq, Real.dist_eq] using ha
          have hb' : |(b : ℝ) - (t₀ : ℝ)| < δ := by simpa [Subtype.dist_eq, Real.dist_eq] using hb
          rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
          rw [abs_lt] at ha' hb'
          constructor <;> linarith
        have heq_u : (truncPath γ a b hab s).1 = (γ uI).1 := by
          change (γ.extend (uI : ℝ)).1 = (γ uI).1
          rw [γ.extend_extends']
        rw [heq_u]
        simpa [mem_ball] using hδ_ball hdist_u
      rw [← hseg]
      exact htr
    have hlocal : ∀ (t : unitInterval) (ht : dist t t₀ < δ),
        L t = uChart (L t₀) hr hsub (γ t).1 (by simpa [mem_ball] using hδ_ball ht) := by
      intro t ht
      have ht_ball : (γ t).1 ∈ ball (γ t₀).1 r := by simpa [mem_ball] using hδ_ball ht
      refine UCov.ext rfl ?_
      apply heq_of_eq
      rcases le_total t₀ t with hle | hle
      · exact hstep hle (by simpa using hδ) ht
      · have h1 := hstep hle ht (by simpa using hδ)
        change (L t₀).path = (L t).path.trans
          (Path.Homotopic.Quotient.mk (segPath hsub ht_ball (mem_ball_self hr))) at h1
        change (L t).path = (L t₀).path.trans
          (Path.Homotopic.Quotient.mk (segPath hsub (mem_ball_self hr) ht_ball))
        rw [h1, path_quot_trans_assoc, segPath_trans_homotopic, segPath_refl_homotopic,
          path_quot_trans_refl]
    rw [ContinuousAt, (uBasis_isTopologicalBasis hΩ w₀).nhds_hasBasis.tendsto_right_iff]
    rintro S ⟨⟨p', r', hr', hsub', rfl⟩, ht₀S⟩
    have hopen : IsOpen (ball (γ t₀).1 r ∩ ball p'.pt.1 r') := isOpen_ball.inter isOpen_ball
    have hmem : (γ t₀).1 ∈ ball (γ t₀).1 r ∩ ball p'.pt.1 r' := ⟨mem_ball_self hr, ht₀S.1⟩
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen (γ t₀).1 hmem
    obtain ⟨δ', hδ', hδ'_ball⟩ := Metric.continuousAt_iff.mp hγ_cont ρ hρ
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t₀ (lt_min hδ hδ')) fun t ht => ?_
    change L t ∈ uBall p' hr' hsub'
    have ht1 : dist t t₀ < δ := lt_of_lt_of_le (mem_ball.mp ht) (min_le_left _ _)
    have ht2 : dist t t₀ < δ' := lt_of_lt_of_le (mem_ball.mp ht) (min_le_right _ _)
    have ht_ρ : (γ t).1 ∈ ball (γ t₀).1 ρ := by simpa [mem_ball] using hδ'_ball ht2
    rw [hlocal t ht1]
    have heq1 : uChart (L t₀) hr hsub (γ t).1 (by simpa [mem_ball] using hδ_ball ht1) =
        uChart (L t₀) hρ ((hρsub.trans inter_subset_left).trans hsub) (γ t).1 ht_ρ :=
      (uChart_eq_uChart hr hsub (mem_ball_self hr) (uChart_self (L t₀) hr hsub).symm
        hρ (hρsub.trans inter_subset_left) ht_ρ).symm
    rw [heq1]
    exact uBall_subset_uBall hr' hsub' ht₀S hρ (hρsub.trans inter_subset_right)
      (uChart_mem_uBall (L t₀) hρ _ ht_ρ)
  have hEq : L = (isCoveringMap_uProj hΩ hΩc w₀).liftPath γ (uBase w₀) γ.source :=
    ((isCoveringMap_uProj hΩ hΩc w₀).eq_liftPath_iff γ.source).mpr ⟨hL_cont, hL_proj, hL_zero⟩
  rw [← hEq]
  exact hL_one

private lemma pathConnectedSpace_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (w₀ : Ω) : PathConnectedSpace (UCov Ω w₀) := by
  have hbase : ∀ p : UCov Ω w₀, Joined (uBase w₀) p := by
    intro ⟨w, q⟩
    induction q using Quotient.ind with | _ γ =>
    let Γ := (isCoveringMap_uProj hΩ hΩc w₀).liftPath γ (uBase w₀) γ.source
    refine ⟨{
      toFun := Γ
      continuous_toFun := Γ.continuous
      source' := (isCoveringMap_uProj hΩ hΩc w₀).liftPath_zero γ (uBase w₀) γ.source
      target' := uProj_liftPath_endpoint hΩ hΩc w₀ γ
    }⟩
  exact ⟨⟨uBase w₀⟩, fun p q => (hbase p).symm.trans (hbase q)⟩

private lemma simplyConnectedSpace_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (w₀ : Ω) : SimplyConnectedSpace (UCov Ω w₀) := by
  have : PathConnectedSpace (UCov Ω w₀) := pathConnectedSpace_UCov hΩ hΩc w₀
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x Γ => ?_⟩
  have hbase_loop : ∀ (L : Path (uBase w₀) (uBase w₀)), Path.Homotopic L (Path.refl (uBase w₀)) := by
    intro L
    let γ : Path w₀ w₀ := L.map (continuous_uProj hΩ)
    have hL_eq : (L : C(unitInterval, UCov Ω w₀)) =
        (isCoveringMap_uProj hΩ hΩc w₀).liftPath γ (uBase w₀) γ.source :=
      ((isCoveringMap_uProj hΩ hΩc w₀).eq_liftPath_iff' γ.source).mpr ⟨rfl, L.source⟩
    have h1 : (⟨w₀, Path.Homotopic.Quotient.mk γ⟩ : UCov Ω w₀) = uBase w₀ := by
      rw [← uProj_liftPath_endpoint hΩ hΩc w₀ γ, ← hL_eq]
      exact L.target
    have hγ_null : Path.Homotopic γ (Path.refl w₀) := by
      injection h1 with _ hq
      exact Quotient.exact hq
    exact ((isCoveringMap_uProj hΩ hΩc w₀).homotopicRel_iff_comp
      (f₀ := (L : C(unitInterval, UCov Ω w₀)))
      (f₁ := (Path.refl (uBase w₀) : C(unitInterval, UCov Ω w₀)))
      (S := {0, 1}) ⟨0, .inl rfl, L.source⟩).mpr hγ_null
  let P : Path (uBase w₀) x := PathConnectedSpace.somePath (uBase w₀) x
  let L : Path (uBase w₀) (uBase w₀) := (P.trans Γ).trans P.symm
  have hL : Path.Homotopic.Quotient.mk L = Path.Homotopic.Quotient.refl (uBase w₀) :=
    Quotient.sound (hbase_loop L)
  have hP_symm_P : (Path.Homotopic.Quotient.mk P.symm).trans (Path.Homotopic.Quotient.mk P) =
      Path.Homotopic.Quotient.refl x := by
    rw [← Path.Homotopic.Quotient.mk_trans]
    exact Quotient.sound ⟨(Path.Homotopy.reflSymmTrans P).symm⟩
  have hΓq : Path.Homotopic.Quotient.mk Γ = Path.Homotopic.Quotient.refl x := by
    calc Path.Homotopic.Quotient.mk Γ
        = (Path.Homotopic.Quotient.refl x).trans (Path.Homotopic.Quotient.mk Γ) :=
          (path_quot_refl_trans _).symm
      _ = ((Path.Homotopic.Quotient.mk P.symm).trans (Path.Homotopic.Quotient.mk P)).trans
            (Path.Homotopic.Quotient.mk Γ) := by rw [hP_symm_P]
      _ = (Path.Homotopic.Quotient.mk P.symm).trans
            ((Path.Homotopic.Quotient.mk P).trans (Path.Homotopic.Quotient.mk Γ)) :=
          path_quot_trans_assoc _ _ _
      _ = (Path.Homotopic.Quotient.mk P.symm).trans
            (((Path.Homotopic.Quotient.mk P).trans (Path.Homotopic.Quotient.mk Γ)).trans
              ((Path.Homotopic.Quotient.mk P.symm).trans (Path.Homotopic.Quotient.mk P))) := by
          rw [hP_symm_P, path_quot_trans_refl]
      _ = (Path.Homotopic.Quotient.mk P.symm).trans
            ((Path.Homotopic.Quotient.mk L).trans (Path.Homotopic.Quotient.mk P)) := by
          congr 1
          rw [← path_quot_trans_assoc]
          rfl
      _ = (Path.Homotopic.Quotient.mk P.symm).trans (Path.Homotopic.Quotient.mk P) := by
          rw [hL, path_quot_refl_trans]
      _ = Path.Homotopic.Quotient.refl x := hP_symm_P
  exact Quotient.exact hΓq

open Classical in
private def IsHoloOnUCov {Ω : Set ℂ} {w₀ : Ω} (F : UCov Ω w₀ → ℂ) : Prop :=
  ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
    DifferentiableOn ℂ (fun z => if h : z ∈ ball p.pt.1 r then F (uChart p hr hsub z h) else 0)
      (ball p.pt.1 r)

open Classical in
private lemma exists_bounded_holo_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) :
    ∃ Φ : UCov Ω w₀ → ℂ, IsHoloOnUCov Φ ∧ (∀ p, ‖Φ p‖ < 1) ∧
      ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
        deriv (fun z => if h : z ∈ ball p.pt.1 r then Φ (uChart p hr hsub z h) else 0) p.pt.1 ≠ 0 := by
  have : SimplyConnectedSpace (UCov Ω w₀) := simplyConnectedSpace_UCov hΩ hΩc w₀
  have : LocallyPathConnectedSpace (UCov Ω w₀) := locallyPathConnectedSpace_UCov hΩ w₀
  let uProjP : C(UCov Ω w₀, PSet) := ⟨fun p => ⟨p.pt.1, hΩP p.pt.2⟩,
    (continuous_uProjC hΩ).subtype_mk _⟩
  obtain ⟨τ₀, hτ₀H', hτ₀eq⟩ := jFn_surjective_on_H' w₀.1 (hΩP w₀.2)
  obtain ⟨τLift, ⟨-, hτLift_comp⟩, -⟩ :=
    isCoveringMap_jMap.existsUnique_continuousMap_lifts uProjP (uBase w₀) ⟨τ₀, hτ₀H'⟩
      (Subtype.ext hτ₀eq)
  have hj_eq : ∀ p : UCov Ω w₀, jFn (τLift p).1 = p.pt.1 := fun p =>
    congr_arg Subtype.val (congr_fun hτLift_comp p)
  let cayley : ℂ → ℂ := fun z => (z - I) / (z + I)
  let Φ : UCov Ω w₀ → ℂ := fun p => cayley (τLift p).1.1
  have hne_I : ∀ τ : ℍ, (τ : ℂ) + I ≠ 0 := fun τ h => by
    have him := congr_arg Complex.im h
    simp only [add_im, Complex.I_im, zero_im] at him
    have hpos : 0 < (τ : ℂ).im := τ.im_pos
    linarith
  have hΦ_lt : ∀ p, ‖Φ p‖ < 1 := by
    intro p
    let τ := (τLift p).1
    have hden : 0 < ‖(τ : ℂ) + I‖ := norm_pos_iff.mpr (hne_I τ)
    change ‖((τ : ℂ) - I) / ((τ : ℂ) + I)‖ < 1
    rw [norm_div, div_lt_one hden]
    have hpos : 0 < (τ : ℂ).im := τ.im_pos
    have hsq : ‖(τ : ℂ) - I‖ ^ 2 < ‖(τ : ℂ) + I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, sub_re, add_re, sub_im, add_im, Complex.I_re, Complex.I_im]
      nlinarith
    nlinarith [norm_nonneg ((τ : ℂ) - I), norm_nonneg ((τ : ℂ) + I)]
  have hlocal_deriv : ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
      (z₀ : ℂ) (hz₀ : z₀ ∈ ball p.pt.1 r),
      ∃ d : ℂ, d ≠ 0 ∧ HasStrictDerivAt
        (fun z => if h : z ∈ ball p.pt.1 r then Φ (uChart p hr hsub z h) else 0) d z₀ := by
    intro p r hr hsub z₀ hz₀
    let q := uChart p hr hsub z₀ hz₀
    let τq := (τLift q).1
    have hτqH' : τq ∈ H' := (τLift q).2
    let fC : ℂ → ℂ := fun z => if h : z ∈ ball p.pt.1 r then (τLift (uChart p hr hsub z h)).1.1 else 0
    have hfC_cont : ContinuousAt fC z₀ := by
      have h1 : ContinuousAt (fun z : ball p.pt.1 r => (τLift (uChart p hr hsub z.1 z.2)).1.1)
          ⟨z₀, hz₀⟩ :=
        ((UpperHalfPlane.continuous_coe.comp continuous_subtype_val).comp
          (τLift.continuous.comp (continuousOn_uChart hΩ p hr hsub))).continuousAt
      rw [Metric.continuousAt_iff] at h1 ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := h1 ε hε
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball z₀ hz₀
      refine ⟨min δ ρ, lt_min hδ hρ, fun z hz => ?_⟩
      have hz_ball : z ∈ ball p.pt.1 r := hρsub (lt_of_lt_of_le hz (min_le_right _ _))
      have hz_δ : dist (⟨z, hz_ball⟩ : ball p.pt.1 r) ⟨z₀, hz₀⟩ < δ :=
        lt_of_lt_of_le hz (min_le_left _ _)
      change dist (if h : z ∈ ball p.pt.1 r then (τLift (uChart p hr hsub z h)).1.1 else 0)
        (if h : z₀ ∈ ball p.pt.1 r then (τLift (uChart p hr hsub z₀ h)).1.1 else 0) < ε
      rw [dif_pos hz_ball, dif_pos hz₀]
      exact hδ' hz_δ
    let dj : ℂ := -2 * Real.pi * I * ModularForm.E₄ τq ^ 2 * ModularForm.E₆ τq /
      ModularForm.discriminant τq
    have hj_sd : HasStrictDerivAt (jFn ∘ UpperHalfPlane.ofComplex) dj (τq : ℂ) :=
      jFn_hasStrictDerivAt τq
    have hjd_ne : dj ≠ 0 := jFn_deriv_ne_zero hτqH'
    have hleft_inv : ∀ᶠ z in 𝓝 z₀, (jFn ∘ UpperHalfPlane.ofComplex) (fC z) = z := by
      filter_upwards [isOpen_ball.mem_nhds hz₀] with z hz
      change jFn (UpperHalfPlane.ofComplex (if h : z ∈ ball p.pt.1 r then
        (τLift (uChart p hr hsub z h)).1.1 else 0)) = z
      rw [dif_pos hz, UpperHalfPlane.ofComplex_apply]
      exact hj_eq (uChart p hr hsub z hz)
    have hfC_eq_z₀ : fC z₀ = (τq : ℂ) := dif_pos hz₀
    have hj_sd' : HasStrictDerivAt (jFn ∘ UpperHalfPlane.ofComplex) dj (fC z₀) := by
      rw [hfC_eq_z₀]; exact hj_sd
    have hfC_sd : HasStrictDerivAt fC dj⁻¹ z₀ :=
      HasStrictDerivAt.of_local_left_inverse hfC_cont hj_sd' hjd_ne hleft_inv
    have hcay_sd : HasStrictDerivAt cayley (2 * I / ((τq : ℂ) + I) ^ 2) (τq : ℂ) := by
      have h1 : HasStrictDerivAt (fun w : ℂ => w - I) 1 (τq : ℂ) :=
        (hasStrictDerivAt_id (τq : ℂ)).sub_const I
      have h2 : HasStrictDerivAt (fun w : ℂ => w + I) 1 (τq : ℂ) :=
        (hasStrictDerivAt_id (τq : ℂ)).add_const I
      refine (h1.div h2 (hne_I τq)).congr_deriv ?_
      ring
    have hcay_sd' : HasStrictDerivAt cayley (2 * I / ((τq : ℂ) + I) ^ 2) (fC z₀) := by
      rw [hfC_eq_z₀]; exact hcay_sd
    have hcomp : HasStrictDerivAt (cayley ∘ fC) ((2 * I / ((τq : ℂ) + I) ^ 2) * dj⁻¹) z₀ :=
      hcay_sd'.comp z₀ hfC_sd
    have hev_Φ : (cayley ∘ fC) =ᶠ[𝓝 z₀]
        (fun z => if h : z ∈ ball p.pt.1 r then Φ (uChart p hr hsub z h) else 0) := by
      filter_upwards [isOpen_ball.mem_nhds hz₀] with z hz
      simp only [Function.comp_apply, fC, Φ, dif_pos hz]
    refine ⟨(2 * I / ((τq : ℂ) + I) ^ 2) * dj⁻¹,
      mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        (pow_ne_zero 2 (hne_I τq))) (inv_ne_zero hjd_ne),
      hcomp.congr_of_eventuallyEq hev_Φ⟩
  refine ⟨Φ, fun p r hr hsub z₀ hz₀ => ?_, hΦ_lt, fun p r hr hsub => ?_⟩
  · obtain ⟨d, -, hd⟩ := hlocal_deriv p r hr hsub z₀ hz₀
    exact hd.hasDerivAt.differentiableAt.differentiableWithinAt
  · obtain ⟨d, hdne, hd⟩ := hlocal_deriv p r hr hsub p.pt.1 (mem_ball_self hr)
    rwa [hd.hasDerivAt.deriv]

/- ### Part 4: Euclidean disk potential theory (Poisson integral, subharmonic max principle, Harnack, removable singularity) -/

open InnerProductSpace

private def poissonInt (c : ℂ) (R : ℝ) (g : ℂ → ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel c w • g) c R

private lemma poissonKernel_pos {c w z : ℂ} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ sphere c R) (hw : w ∈ ball c R) : 0 < poissonKernel c w z := by
  rw [poissonKernel_def]
  have hzn : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  have hwn : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hden : 0 < ‖(z - c) - (w - c)‖ ^ 2 := by
    apply sq_pos_of_pos
    rw [norm_pos_iff, sub_ne_zero]
    intro h; rw [h] at hzn; linarith
  have hnum : 0 < ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 := by
    rw [hzn]; nlinarith [norm_nonneg (w - c)]
  exact div_pos hnum hden

private lemma circleAverage_poissonKernel_eq_one {c w : ℂ} {R : ℝ} (_hR : 0 < R)
    (hw : w ∈ ball c R) : Real.circleAverage (poissonKernel c w) c R = 1 := by
  have h := (harmonicOnNhd_const (E := ℂ) (F := ℝ) (s := closedBall c R) (1 : ℝ)).circleAverage_poissonKernel_smul hw
  have heq : (poissonKernel c w • fun _ : ℂ => (1 : ℝ)) = poissonKernel c w := by
    ext z; simp
  rwa [heq] at h

private lemma poissonInt_const {c w : ℂ} {R a : ℝ} (hR : 0 < R) (hw : w ∈ ball c R) :
    poissonInt c R (fun _ => a) w = a := by
  simp only [poissonInt]
  have heq : (poissonKernel c w • fun _ : ℂ => a) = fun z => a • poissonKernel c w z := by
    ext z; simp [mul_comm]
  rw [heq, Real.circleAverage_fun_smul, circleAverage_poissonKernel_eq_one hR hw, smul_eq_mul, mul_one]

private lemma poissonInt_mono {c w : ℂ} {R : ℝ} {g₁ g₂ : ℂ → ℝ} (hR : 0 < R) (hw : w ∈ ball c R)
    (hg₁ : ContinuousOn g₁ (sphere c R)) (hg₂ : ContinuousOn g₂ (sphere c R))
    (hle : ∀ z ∈ sphere c R, g₁ z ≤ g₂ z) :
    poissonInt c R g₁ w ≤ poissonInt c R g₂ w := by
  have hk_cont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hci₁ : CircleIntegrable (poissonKernel c w • g₁) c R :=
    (hg₁.mono (by rw [abs_of_pos hR])).circleIntegrable' |>.continuousOn_smul hk_cont
  have hci₂ : CircleIntegrable (poissonKernel c w • g₂) c R :=
    (hg₂.mono (by rw [abs_of_pos hR])).circleIntegrable' |>.continuousOn_smul hk_cont
  refine Real.circleAverage_mono hci₁ hci₂ fun z hz => ?_
  rw [abs_of_pos hR] at hz
  exact mul_le_mul_of_nonneg_left (hle z hz) (poissonKernel_pos hR hz hw).le

private lemma poissonInt_harmonicOnNhd {c : ℂ} {R : ℝ} {g : ℂ → ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) : HarmonicOnNhd (poissonInt c R g) (ball c R) := by
  let g₀ : ℂ → ℝ := fun z => g (z + c)
  have hg₀_cont : ContinuousOn g₀ (sphere 0 R) := by
    refine hg.comp (continuous_id.add continuous_const).continuousOn fun z hz => ?_
    simpa [mem_sphere_iff_norm] using hz
  have hg₀_ci : CircleIntegrable g₀ 0 R :=
    (hg₀_cont.mono (by rw [abs_of_pos hR])).circleIntegrable'
  have hg₀C_ci : CircleIntegrable (fun ζ => (g₀ ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg₀_ci ⊢
    exact Complex.ofRealCLM.integrable_comp hg₀_ci
  let F₀ : ℂ → ℂ := fun w => Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (g₀ ζ : ℂ)) 0 R
  have hF₀_ana : AnalyticOnNhd ℂ F₀ (ball 0 R) :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul hg₀C_ci
  intro w hw
  have hwc : w - c ∈ ball 0 R := by simpa [mem_ball_iff_norm] using mem_ball_iff_norm.mp hw
  have hF_ana : AnalyticAt ℂ (fun z => F₀ (z - c)) w :=
    (hF₀_ana (w - c) hwc).comp (f := fun z => z - c) (analyticAt_id.sub analyticAt_const)
  have hharm : HarmonicAt (fun z => (F₀ (z - c)).re) w := hF_ana.harmonicAt_re
  refine (harmonicAt_congr_nhds ?_).mp hharm
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  have hzc : z - c ∈ ball 0 R := by simpa [mem_ball_iff_norm] using mem_ball_iff_norm.mp hz
  change (F₀ (z - c)).re = Real.circleAverage (poissonKernel c z • g) c R
  rw [re_circleAverage_herglotzRieszKernel_smul hg₀_ci hzc, ← poissonKernel_eq_re_herglotzRieszKernel]
  have hshift : Real.circleAverage (fun ζ => (poissonKernel c z • g) (ζ + c)) 0 R =
      Real.circleAverage (poissonKernel c z • g) c R :=
    Real.circleAverage_map_add_const (f := poissonKernel c z • g) (c := c) (R := R)
  rw [← hshift]
  refine Real.circleAverage_congr_sphere fun ζ _ => ?_
  change poissonKernel 0 (z - c) ζ * g (ζ + c) = poissonKernel c z (ζ + c) * g (ζ + c)
  simp only [poissonKernel_def, sub_zero, add_sub_cancel_right]

private lemma poissonInt_tendsto_boundary {c ζ₀ : ℂ} {R : ℝ} {g : ℂ → ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) (hζ₀ : ζ₀ ∈ sphere c R) :
    Tendsto (poissonInt c R g) (𝓝[ball c R] ζ₀) (𝓝 (g ζ₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcomp : IsCompact (sphere c R) := isCompact_sphere c R
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_bound_of_continuousOn
    (continuous_abs.comp_continuousOn (hg.sub continuousOn_const))
  let M : ℝ := max M₀ 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM_bound : ∀ ζ ∈ sphere c R, |g ζ - g ζ₀| ≤ M := fun ζ hζ =>
    le_trans (by simpa [Real.norm_eq_abs] using hM₀ ζ hζ) (le_max_left _ _)
  have hcont_at : ContinuousWithinAt g (sphere c R) ζ₀ := hg ζ₀ hζ₀
  rw [Metric.continuousWithinAt_iff] at hcont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hcont_at (ε / 2) (half_pos hε)
  let δ : ℝ := min (δ₀ / 2) (ε * δ₀ ^ 2 / (16 * R * M))
  have hδ_pos : 0 < δ := lt_min (half_pos hδ₀_pos) (by positivity)
  refine ⟨δ, hδ_pos, fun w hw_ball hw_dist => ?_⟩
  rw [Real.dist_eq]
  have hsub_eq : poissonInt c R g w - g ζ₀ =
      Real.circleAverage (fun ζ => poissonKernel c w ζ * (g ζ - g ζ₀)) c R := by
    have hk_cont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw_ball)
    have hci1 : CircleIntegrable (poissonKernel c w • g) c R :=
      (hg.mono (by rw [abs_of_pos hR])).circleIntegrable' |>.continuousOn_smul hk_cont
    have hci2 : CircleIntegrable (poissonKernel c w • fun _ => g ζ₀) c R :=
      (continuousOn_const.circleIntegrable' (c := c) (R := R)).continuousOn_smul hk_cont
    have hconst : Real.circleAverage (poissonKernel c w • fun _ => g ζ₀) c R = g ζ₀ :=
      poissonInt_const hR hw_ball
    calc poissonInt c R g w - g ζ₀
        = Real.circleAverage (poissonKernel c w • g) c R -
            Real.circleAverage (poissonKernel c w • fun _ => g ζ₀) c R := by
          rw [poissonInt, hconst]
      _ = Real.circleAverage ((poissonKernel c w • g) - (poissonKernel c w • fun _ => g ζ₀)) c R :=
          (Real.circleAverage_sub hci1 hci2).symm
      _ = Real.circleAverage (fun ζ => poissonKernel c w ζ * (g ζ - g ζ₀)) c R :=
          Real.circleAverage_congr_sphere fun ζ _ => by
            change poissonKernel c w ζ * g ζ - poissonKernel c w ζ * g ζ₀ = _
            ring
  rw [hsub_eq]
  let Cw : ℝ := (R ^ 2 - ‖w - c‖ ^ 2) / (δ₀ / 2) ^ 2 * M
  have hCw_lt : Cw < ε / 2 := by
    have hζ₀n : ‖ζ₀ - c‖ = R := mem_sphere_iff_norm.mp hζ₀
    have hwn : ‖w - c‖ < R := mem_ball_iff_norm.mp hw_ball
    have hdiff : R - ‖w - c‖ ≤ dist w ζ₀ := by
      rw [← hζ₀n, dist_eq_norm]
      have := norm_sub_norm_le (ζ₀ - c) (w - c)
      have heq : (ζ₀ - c) - (w - c) = -(w - ζ₀) := by ring
      rw [heq, norm_neg] at this
      exact this
    have hsq : R ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * R * dist w ζ₀ := by
      have : R ^ 2 - ‖w - c‖ ^ 2 = (R + ‖w - c‖) * (R - ‖w - c‖) := by ring
      rw [this]
      nlinarith [norm_nonneg (w - c)]
    have hw_lt2 : dist w ζ₀ < ε * δ₀ ^ 2 / (16 * R * M) :=
      lt_of_lt_of_le hw_dist (min_le_right _ _)
    have h1 : Cw ≤ (2 * R * dist w ζ₀) / (δ₀ / 2) ^ 2 * M := by
      dsimp only [Cw]
      gcongr
    have h2 : (2 * R * dist w ζ₀) / (δ₀ / 2) ^ 2 * M < ε / 2 := by
      have hden : (0 : ℝ) < (δ₀ / 2) ^ 2 := by positivity
      have hden2 : (0 : ℝ) < 16 * R * M := by positivity
      have hmul : 2 * R * dist w ζ₀ * M < (ε / 2) * (δ₀ / 2) ^ 2 := by
        have hlt : dist w ζ₀ * (16 * R * M) < ε * δ₀ ^ 2 := (lt_div_iff₀ hden2).mp hw_lt2
        nlinarith
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      exact hmul
    exact lt_of_le_of_lt h1 h2
  have hpt_le : ∀ ζ ∈ sphere c R,
      |poissonKernel c w ζ * (g ζ - g ζ₀)| ≤ poissonKernel c w ζ * (ε / 2) + Cw := by
    intro ζ hζ
    have hk_pos : 0 < poissonKernel c w ζ := poissonKernel_pos hR hζ hw_ball
    rw [abs_mul, abs_of_pos hk_pos]
    by_cases hnear : dist ζ ζ₀ < δ₀
    · have hgd : |g ζ - g ζ₀| < ε / 2 := by simpa [Real.dist_eq] using hδ₀ hζ hnear
      have hCw_nn : 0 ≤ Cw := by
        have hwn : ‖w - c‖ < R := mem_ball_iff_norm.mp hw_ball
        have : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by nlinarith [norm_nonneg (w - c)]
        dsimp only [Cw]; positivity
      nlinarith
    · push Not at hnear
      have hdist_w : δ₀ / 2 ≤ ‖(ζ - c) - (w - c)‖ := by
        have hw1 : dist w ζ₀ < δ₀ / 2 := lt_of_lt_of_le hw_dist (min_le_left _ _)
        have htri : dist ζ ζ₀ ≤ dist ζ w + dist w ζ₀ := dist_triangle ζ w ζ₀
        have heq : (ζ - c) - (w - c) = ζ - w := by ring
        rw [heq, ← dist_eq_norm]
        linarith
      have hzn : ‖ζ - c‖ = R := mem_sphere_iff_norm.mp hζ
      have hk_le : poissonKernel c w ζ ≤ (R ^ 2 - ‖w - c‖ ^ 2) / (δ₀ / 2) ^ 2 := by
        rw [poissonKernel_def, hzn]
        have hnum_nn : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by
          have hwn : ‖w - c‖ < R := mem_ball_iff_norm.mp hw_ball
          nlinarith [norm_nonneg (w - c)]
        exact div_le_div_of_nonneg_left hnum_nn (by positivity)
          (pow_le_pow_left₀ (by positivity) hdist_w 2)
      have h1 : poissonKernel c w ζ * |g ζ - g ζ₀| ≤ Cw := by
        dsimp only [Cw]
        exact mul_le_mul hk_le (hM_bound ζ hζ) (abs_nonneg _) (by
          have hwn : ‖w - c‖ < R := mem_ball_iff_norm.mp hw_ball
          have : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by nlinarith [norm_nonneg (w - c)]
          positivity)
      nlinarith
  have hk_cont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw_ball)
  have hci_lhs : CircleIntegrable (fun ζ => poissonKernel c w ζ * (g ζ - g ζ₀)) c R := by
    have h1 : ContinuousOn (fun ζ => poissonKernel c w ζ * (g ζ - g ζ₀)) (sphere c |R|) :=
      hk_cont.mul ((hg.mono (by rw [abs_of_pos hR])).sub continuousOn_const)
    exact h1.circleIntegrable'
  have hci_rhs : CircleIntegrable (fun ζ => poissonKernel c w ζ * (ε / 2) + Cw) c R :=
    ((hk_cont.mul continuousOn_const).add continuousOn_const).circleIntegrable'
  have havg_rhs : Real.circleAverage (fun ζ => poissonKernel c w ζ * (ε / 2) + Cw) c R =
      ε / 2 + Cw := by
    have hci_t1 : CircleIntegrable (fun ζ => poissonKernel c w ζ * (ε / 2)) c R :=
      (hk_cont.mul continuousOn_const).circleIntegrable'
    rw [Real.circleAverage_fun_add hci_t1 continuousOn_const.circleIntegrable',
      Real.circleAverage_const]
    have hsmul : (fun ζ => poissonKernel c w ζ * (ε / 2)) = fun ζ => (ε / 2) • poissonKernel c w ζ := by
      ext ζ; simp [mul_comm]
    rw [hsmul, Real.circleAverage_fun_smul, circleAverage_poissonKernel_eq_one hR hw_ball,
      smul_eq_mul, mul_one]
  have hle_pos : Real.circleAverage (fun ζ => poissonKernel c w ζ * (g ζ - g ζ₀)) c R ≤ ε / 2 + Cw := by
    rw [← havg_rhs]
    refine Real.circleAverage_mono hci_lhs hci_rhs fun ζ hζ => ?_
    rw [abs_of_pos hR] at hζ
    exact (le_abs_self _).trans (hpt_le ζ hζ)
  have hle_neg : -(ε / 2 + Cw) ≤ Real.circleAverage (fun ζ => poissonKernel c w ζ * (g ζ - g ζ₀)) c R := by
    have h1 : Real.circleAverage (fun ζ => (-1 : ℝ) • (poissonKernel c w ζ * (g ζ - g ζ₀))) c R ≤ ε / 2 + Cw := by
      rw [← havg_rhs]
      refine Real.circleAverage_mono (hci_lhs.smul (-1 : ℝ)) hci_rhs fun ζ hζ => ?_
      rw [abs_of_pos hR] at hζ
      simpa using (neg_le_abs _).trans (hpt_le ζ hζ)
    rw [Real.circleAverage_fun_smul, smul_eq_mul] at h1
    linarith
  rw [abs_lt]
  constructor <;> linarith

private def IsSubharmOnC (u : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ContinuousOn u U ∧
    ∀ z ∈ U, ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → closedBall z r ⊆ U →
      u z ≤ Real.circleAverage u z r

private lemma HarmonicOnNhd.isSubharmOnC {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) : IsSubharmOnC u U := by
  refine ⟨hu.continuousOn, fun z hz => ?_⟩
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  refine ⟨r₀, hr₀, fun r hr _ hcb => ?_⟩
  have heq := (hu.mono (by rwa [abs_of_pos hr])).circleAverage_eq
  linarith

private lemma IsSubharmOnC.add {u v : ℂ → ℝ} {U : Set ℂ}
    (hu : IsSubharmOnC u U) (hv : IsSubharmOnC v U) : IsSubharmOnC (fun z => u z + v z) U := by
  refine ⟨hu.1.add hv.1, fun z hz => ?_⟩
  obtain ⟨r₁, hr₁, h₁⟩ := hu.2 z hz
  obtain ⟨r₂, hr₂, h₂⟩ := hv.2 z hz
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun r hr hlt hcb => ?_⟩
  have hciu : CircleIntegrable u z r :=
    (hu.1.mono ((by rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hcb))).circleIntegrable'
  have hciv : CircleIntegrable v z r :=
    (hv.1.mono ((by rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hcb))).circleIntegrable'
  rw [Real.circleAverage_fun_add hciu hciv]
  exact add_le_add (h₁ r hr (lt_of_lt_of_le hlt (min_le_left _ _)) hcb)
    (h₂ r hr (lt_of_lt_of_le hlt (min_le_right _ _)) hcb)

private lemma IsSubharmOnC.sup {u v : ℂ → ℝ} {U : Set ℂ}
    (hu : IsSubharmOnC u U) (hv : IsSubharmOnC v U) :
    IsSubharmOnC (fun z => max (u z) (v z)) U := by
  refine ⟨hu.1.sup hv.1, fun z hz => ?_⟩
  obtain ⟨r₁, hr₁, h₁⟩ := hu.2 z hz
  obtain ⟨r₂, hr₂, h₂⟩ := hv.2 z hz
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun r hr hlt hcb => ?_⟩
  have hsp : sphere z |r| ⊆ U := by rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hcb
  have hciu : CircleIntegrable u z r := (hu.1.mono hsp).circleIntegrable'
  have hciv : CircleIntegrable v z r := (hv.1.mono hsp).circleIntegrable'
  have hcim : CircleIntegrable (fun w => max (u w) (v w)) z r :=
    ((hu.1.sup hv.1).mono hsp).circleIntegrable'
  exact max_le
    ((h₁ r hr (lt_of_lt_of_le hlt (min_le_left _ _)) hcb).trans
      (Real.circleAverage_mono hciu hcim fun _ _ => le_max_left _ _))
    ((h₂ r hr (lt_of_lt_of_le hlt (min_le_right _ _)) hcb).trans
      (Real.circleAverage_mono hciv hcim fun _ _ => le_max_right _ _))

private lemma IsSubharmOnC.max_principle_bounded {v : ℂ → ℝ} {V : Set ℂ} {M : ℝ}
    (hVo : IsOpen V) (hVb : Bornology.IsBounded V)
    (hvc : ContinuousOn v (closure V)) (hvs : IsSubharmOnC v V)
    (hbd : ∀ z ∈ frontier V, v z ≤ M) : ∀ z ∈ closure V, v z ≤ M := by
  by_cases hVne : V.Nonempty
  · have hcl_cpt : IsCompact (closure V) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hVb.closure
    obtain ⟨z₀, hz₀_cl, hz₀_max⟩ := hcl_cpt.exists_isMaxOn (hVne.mono subset_closure) hvc
    by_cases hM : v z₀ ≤ M
    · exact fun z hz => (hz₀_max hz).trans hM
    · exfalso
      push Not at hM
      let A : Set ℂ := {z ∈ closure V | v z = v z₀}
      have hA_sub_V : A ⊆ V := by
        intro z ⟨hz_cl, hzv⟩
        by_contra hzV
        have hfr : z ∈ frontier V := ⟨hz_cl, by rwa [hVo.interior_eq]⟩
        linarith [hbd z hfr]
      have hA_closed : IsClosed A :=
        hvc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
      have hA_cpt : IsCompact A := hcl_cpt.of_isClosed_subset hA_closed fun _ h => h.1
      have hA_ne : A.Nonempty := ⟨z₀, hz₀_cl, rfl⟩
      obtain ⟨w₀, hw₀A, hw₀_max⟩ := hA_cpt.exists_isMaxOn hA_ne continuous_norm.continuousOn
      have hw₀V : w₀ ∈ V := hA_sub_V hw₀A
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hVo w₀ hw₀V
      obtain ⟨r₂, hr₂, hr₂avg⟩ := hvs.2 w₀ hw₀V
      let r : ℝ := min (r₁ / 2) (r₂ / 2)
      have hr : 0 < r := lt_min (half_pos hr₁) (half_pos hr₂)
      have hcb : closedBall w₀ r ⊆ V :=
        (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₁))).trans hr₁sub
      have havg : v w₀ ≤ Real.circleAverage v w₀ r :=
        hr₂avg r hr (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr₂)) hcb
      -- Every point on sphere w₀ r must achieve the maximum v z₀, else the circle average < v z₀!
      have hsphere_eq : ∀ ζ ∈ sphere w₀ r, v ζ = v z₀ := by
        intro ζ hζ
        have hle : v ζ ≤ v z₀ := hz₀_max (subset_closure (hcb (sphere_subset_closedBall hζ)))
        by_contra hne
        have hlt : v ζ < v z₀ := lt_of_le_of_ne hle hne
        -- Translate circleAverage to intervalIntegral on [0, 2π] and use strict monotonicity.
        have hle_all : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
            v (circleMap w₀ r θ) ≤ v z₀ := fun θ _ =>
          hz₀_max (subset_closure (hcb (sphere_subset_closedBall
            (circleMap_mem_sphere w₀ hr.le θ))))
        have hcont_θ : ContinuousOn (fun θ => v (circleMap w₀ r θ)) (Icc 0 (2 * Real.pi)) :=
          (hvs.1.mono (sphere_subset_closedBall.trans hcb)).comp
            (continuous_circleMap w₀ r).continuousOn fun θ _ => circleMap_mem_sphere w₀ hr.le θ
        -- Find θ₀ ∈ [0, 2π] with circleMap w₀ r θ₀ = ζ.
        have hζ_norm : ‖ζ - w₀‖ = r := by simpa [mem_sphere_iff_norm] using hζ
        let θ₁ := (ζ - w₀).arg
        let θ₀ := if 0 ≤ θ₁ then θ₁ else θ₁ + 2 * Real.pi
        have hθ₀_mem : θ₀ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
          dsimp only [θ₀]
          split_ifs with h
          · exact ⟨h, (Complex.arg_le_pi _).trans (by linarith [Real.pi_pos])⟩
          · have hneg := Complex.neg_pi_lt_arg (ζ - w₀)
            exact ⟨by linarith, by linarith⟩
        have hθ₀_eq : circleMap w₀ r θ₀ = ζ := by
          simp only [circleMap, θ₀]
          have hrexp : Complex.exp (θ₀ * I) = Complex.exp (θ₁ * I) := by
            dsimp only [θ₀]
            split_ifs
            · rfl
            · push_cast
              rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
          have h2 : (r : ℂ) * Complex.exp (θ₁ * I) = ζ - w₀ := by
            rw [← hζ_norm]; exact Complex.norm_mul_exp_arg_mul_I (ζ - w₀)
          calc w₀ + (r : ℂ) * Complex.exp (θ₀ * I)
              = w₀ + (r : ℂ) * Complex.exp (θ₁ * I) := by rw [hrexp]
            _ = w₀ + (ζ - w₀) := by rw [h2]
            _ = ζ := by ring
        have hint_lt : ∫ θ in (0 : ℝ)..(2 * Real.pi), v (circleMap w₀ r θ) <
            ∫ _ in (0 : ℝ)..(2 * Real.pi), v z₀ :=
          intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
            (by positivity) hcont_θ continuousOn_const (fun θ hθ => hle_all θ ⟨hθ.1.le, hθ.2⟩)
            ⟨θ₀, hθ₀_mem, hθ₀_eq ▸ hlt⟩
        have havg_lt : Real.circleAverage v w₀ r < v z₀ := by
          rw [Real.circleAverage_def, smul_eq_mul]
          have hconst : (∫ _ in (0 : ℝ)..(2 * Real.pi), v z₀) = (2 * Real.pi) * v z₀ := by
            simp
          rw [hconst] at hint_lt
          have h2pi : 0 < 2 * Real.pi := by positivity
          calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), v (circleMap w₀ r θ)
              < (2 * Real.pi)⁻¹ * ((2 * Real.pi) * v z₀) :=
                mul_lt_mul_of_pos_left hint_lt (inv_pos.mpr h2pi)
            _ = v z₀ := by rw [← mul_assoc, inv_mul_cancel₀ h2pi.ne', one_mul]
        linarith [hw₀A.2]
      -- Pick a point on sphere w₀ r with strictly larger norm than w₀!
      let dir : ℂ := if w₀ = 0 then 1 else (w₀ / (‖w₀‖ : ℂ))
      have hdir_norm : ‖dir‖ = 1 := by
        dsimp only [dir]
        split_ifs with h0
        · simp
        · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w₀),
            div_self (norm_ne_zero_iff.mpr h0)]
      let w₁ : ℂ := w₀ + (r : ℂ) * dir
      have hw₁_sph : w₁ ∈ sphere w₀ r := by
        rw [mem_sphere_iff_norm, show w₁ - w₀ = (r : ℂ) * dir by simp [w₁], norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hr.le, hdir_norm, mul_one]
      have hw₁A : w₁ ∈ A :=
        ⟨subset_closure (hcb (sphere_subset_closedBall hw₁_sph)), hsphere_eq w₁ hw₁_sph⟩
      have hw₁_norm : ‖w₁‖ = ‖w₀‖ + r := by
        dsimp only [w₁, dir]
        split_ifs with h0
        · simp [h0, Complex.norm_real, Real.norm_of_nonneg hr.le]
        · have hne : (‖w₀‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
          have hfac : w₀ + (r : ℂ) * (w₀ / (‖w₀‖ : ℂ)) = ((‖w₀‖ + r : ℝ) : ℂ) * (w₀ / (‖w₀‖ : ℂ)) := by
            push_cast; field_simp [hne]
          rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [norm_nonneg w₀]),
            norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w₀),
            div_self (norm_ne_zero_iff.mpr h0), mul_one]
      have hle_max : ‖w₁‖ ≤ ‖w₀‖ := hw₀_max hw₁A
      linarith
  · intro z hz
    have hVemp : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hVne
    simp [hVemp] at hz

open Classical in
private lemma IsSubharmOnC.le_poissonInt {u : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (huc : ContinuousOn u (closedBall c R)) (hus : IsSubharmOnC u (ball c R)) :
    ∀ w ∈ ball c R, u w ≤ poissonInt c R u w := by
  let P : ℂ → ℝ := fun w => if w ∈ ball c R then poissonInt c R u w else u w
  have hu_sph : ContinuousOn u (sphere c R) := huc.mono sphere_subset_closedBall
  have hP_cont : ContinuousOn P (closedBall c R) := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heq
    · have hz_ball : z ∈ ball c R := hlt
      have hharm : ContinuousAt (poissonInt c R u) z :=
        ((poissonInt_harmonicOnNhd hR hu_sph z hz_ball).1.continuousAt)
      have hev : P =ᶠ[𝓝 z] poissonInt c R u := by
        filter_upwards [isOpen_ball.mem_nhds hz_ball] with w hw
        simp only [P, if_pos hw]
      exact (hharm.congr hev.symm).continuousWithinAt
    · have hz_sph : z ∈ sphere c R := heq
      have hPz : P z = u z := by
        have hnot : z ∉ ball c R := by rw [mem_ball]; linarith
        simp only [P, if_neg hnot]
      rw [ContinuousWithinAt, hPz, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      have ht_ball := poissonInt_tendsto_boundary hR hu_sph hz_sph
      rw [Metric.tendsto_nhdsWithin_nhds] at ht_ball
      obtain ⟨δ₁, hδ₁, h₁⟩ := ht_ball ε hε
      have ht_cl := huc z hz
      rw [Metric.continuousWithinAt_iff] at ht_cl
      obtain ⟨δ₂, hδ₂, h₂⟩ := ht_cl ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun w hw_cl hw_d => ?_⟩
      by_cases hwb : w ∈ ball c R
      · simp only [P, if_pos hwb]
        exact h₁ hwb (lt_of_lt_of_le hw_d (min_le_left _ _))
      · simp only [P, if_neg hwb]
        exact h₂ hw_cl (lt_of_lt_of_le hw_d (min_le_right _ _))
  have hP_harm : HarmonicOnNhd P (ball c R) := fun z hz =>
    (harmonicAt_congr_nhds (Filter.eventually_of_mem (isOpen_ball.mem_nhds hz)
      fun w hw => by simp only [P, if_pos hw])).mpr (poissonInt_harmonicOnNhd hR hu_sph z hz)
  have hdiff_sub : IsSubharmOnC (fun w => u w - P w) (ball c R) := by
    have h1 := hus.add (HarmonicOnNhd.isSubharmOnC isOpen_ball hP_harm.neg)
    simpa [sub_eq_add_neg] using h1
  have hdiff_cl : ContinuousOn (fun w => u w - P w) (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    exact huc.sub hP_cont
  have hfr : ∀ z ∈ frontier (ball c R), u z - P z ≤ 0 := by
    intro z hz
    have hz_sph : z ∈ sphere c R := frontier_ball_subset_sphere hz
    have hnot : z ∉ ball c R := by
      rw [mem_ball]; rw [mem_sphere] at hz_sph; linarith
    simp only [P, if_neg hnot, sub_self, le_refl]
  intro w hw
  have hle := IsSubharmOnC.max_principle_bounded isOpen_ball isBounded_ball hdiff_cl hdiff_sub hfr
    w (subset_closure hw)
  simp only [P, if_pos hw] at hle
  linarith

private lemma harnack_ineq {h : ℂ → ℝ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : HarmonicOnNhd h (closedBall c R)) (hnn : ∀ z ∈ closedBall c R, 0 ≤ h z)
    (hw : w ∈ ball c R) :
    ((R - ‖w - c‖) / (R + ‖w - c‖)) * h c ≤ h w ∧
      h w ≤ ((R + ‖w - c‖) / (R - ‖w - c‖)) * h c := by
  have havg_eq : Real.circleAverage h c R = h c :=
    (hh.mono (by rw [abs_of_pos hR])).circleAverage_eq
  have hpois := hh.circleAverage_poissonKernel_smul hw
  have hci_h : CircleIntegrable h c R :=
    (hh.continuousOn.mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall)).circleIntegrable'
  have hk_cont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hci_ph : CircleIntegrable (poissonKernel c w • h) c R := hci_h.continuousOn_smul hk_cont
  constructor
  · rw [← hpois, ← havg_eq, ← smul_eq_mul, ← Real.circleAverage_smul]
    refine Real.circleAverage_mono (hci_h.smul _) hci_ph fun z hz => ?_
    rw [abs_of_pos hR] at hz
    have hk : (R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z := by
      rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
      exact le_re_herglotzRieszKernel hz hw
    exact mul_le_mul_of_nonneg_right hk (hnn z (sphere_subset_closedBall hz))
  · rw [← hpois, ← havg_eq, ← smul_eq_mul, ← Real.circleAverage_smul]
    refine Real.circleAverage_mono hci_ph (hci_h.smul _) fun z hz => ?_
    rw [abs_of_pos hR] at hz
    have hk : poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
      exact re_herglotzRieszKernel_le hz hw
    exact mul_le_mul_of_nonneg_right hk (hnn z (sphere_subset_closedBall hz))

private lemma poissonInt_add_const {c w : ℂ} {R a : ℝ} {g : ℂ → ℝ} (hR : 0 < R)
    (hw : w ∈ ball c R) (hg : ContinuousOn g (sphere c R)) :
    poissonInt c R (fun z => g z + a) w = poissonInt c R g w + a := by
  have hk_cont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hci1 : CircleIntegrable (poissonKernel c w • g) c R :=
    (hg.mono (by rw [abs_of_pos hR])).circleIntegrable' |>.continuousOn_smul hk_cont
  have hci2 : CircleIntegrable (poissonKernel c w • fun _ => a) c R :=
    (continuousOn_const.circleIntegrable' (c := c) (R := R)).continuousOn_smul hk_cont
  have heq : (poissonKernel c w • fun z => g z + a) =
      (poissonKernel c w • g) + (poissonKernel c w • fun _ => a) := by
    ext z; simp [mul_add]
  have hconst : Real.circleAverage (poissonKernel c w • fun _ => a) c R = a :=
    poissonInt_const hR hw
  simp only [poissonInt, heq]
  rw [Real.circleAverage_add hci1 hci2, hconst]

private lemma harnack_monotone_limit {c : ℂ} {R : ℝ} (hR : 0 < R)
    {h : ℕ → ℂ → ℝ} (hh : ∀ n, HarmonicOnNhd (h n) (ball c R))
    (hmono : ∀ n, ∀ z ∈ ball c R, h n z ≤ h (n + 1) z)
    (hbdd : ∃ M, ∀ n, h n c ≤ M) :
    (∀ z ∈ ball c R, BddAbove (Set.range fun n => h n z)) ∧
    (∀ z ∈ ball c R, Tendsto (fun n => h n z) atTop (𝓝 (⨆ n, h n z))) ∧
    HarmonicOnNhd (fun z => ⨆ n, h n z) (ball c R) := by
  have hmono_le : ∀ {m n}, m ≤ n → ∀ z ∈ ball c R, h m z ≤ h n z := by
    intro m n hmn z hz
    induction hmn with
    | refl => exact le_rfl
    | @step k _ ih => exact ih.trans (hmono k z hz)
  obtain ⟨M, hM⟩ := hbdd
  have hmono_c : Monotone (fun n => h n c) := fun _ _ hmn => hmono_le hmn c (mem_ball_self hR)
  have hbdd_c : BddAbove (Set.range fun n => h n c) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  have hc_lim : Tendsto (fun n => h n c) atTop (𝓝 (⨆ n, h n c)) :=
    tendsto_atTop_ciSup hmono_c hbdd_c
  let H : ℂ → ℝ := fun z => ⨆ n, h n z
  have hball_r : ∀ r, 0 < r → r < R →
      (∀ w ∈ closedBall c r, BddAbove (Set.range fun n => h n w)) ∧
      (∀ w ∈ closedBall c r, Tendsto (fun n => h n w) atTop (𝓝 (H w))) ∧
      HarmonicOnNhd H (ball c r) := by
    intro r hr_pos hr_lt
    let R' : ℝ := (r + R) / 2
    have hR'_pos : 0 < R' := by dsimp only [R']; linarith
    have hr_R' : r < R' := by dsimp only [R']; linarith
    have hR'_R : R' < R := by dsimp only [R']; linarith
    have hcbR'_sub : closedBall c R' ⊆ ball c R := closedBall_subset_ball hR'_R
    have hcbr_sub : closedBall c r ⊆ ball c R' := closedBall_subset_ball hr_R'
    let C : ℝ := (R' + r) / (R' - r)
    have hC_pos : 0 < C := by dsimp only [C]; exact div_pos (by linarith) (by linarith)
    have hdiff_bound : ∀ {m n}, m ≤ n → ∀ w ∈ closedBall c r,
        h n w - h m w ≤ C * (h n c - h m c) := by
      intro m n hmn w hw
      have hg_harm : HarmonicOnNhd (fun z => h n z - h m z) (closedBall c R') :=
        ((hh n).mono hcbR'_sub).sub ((hh m).mono hcbR'_sub)
      have hg_nn : ∀ z ∈ closedBall c R', 0 ≤ h n z - h m z := fun z hz =>
        sub_nonneg.mpr (hmono_le hmn z (hcbR'_sub hz))
      have hhi := (harnack_ineq hR'_pos hg_harm hg_nn (hcbr_sub hw)).2
      have hwn : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
      have hfrac : (R' + ‖w - c‖) / (R' - ‖w - c‖) ≤ C := by
        dsimp only [C]
        exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
      have hcn : 0 ≤ h n c - h m c := sub_nonneg.mpr (hmono_c hmn)
      exact hhi.trans (mul_le_mul_of_nonneg_right hfrac hcn)
    have hbdd_r : ∀ w ∈ closedBall c r, BddAbove (Set.range fun n => h n w) := by
      intro w hw
      refine ⟨h 0 w + C * (M - h 0 c), ?_⟩
      rintro _ ⟨n, rfl⟩
      have h1 := hdiff_bound (Nat.zero_le n) w hw
      have h2 := hM n
      nlinarith
    have hlim_r : ∀ w ∈ closedBall c r, Tendsto (fun n => h n w) atTop (𝓝 (H w)) := by
      intro w hw
      have hmw : Monotone (fun n => h n w) :=
        fun _ _ hmn => hmono_le hmn w (hcbR'_sub (ball_subset_closedBall (hcbr_sub hw)))
      exact tendsto_atTop_ciSup hmw (hbdd_r w hw)
    have hunif : ∀ m, ∀ w ∈ closedBall c r, 0 ≤ H w - h m w ∧ H w - h m w ≤ C * (H c - h m c) := by
      intro m w hw
      constructor
      · exact sub_nonneg.mpr (le_ciSup (hbdd_r w hw) m)
      · have ht1 : Tendsto (fun n => h n w - h m w) atTop (𝓝 (H w - h m w)) :=
          (hlim_r w hw).sub tendsto_const_nhds
        have ht2 : Tendsto (fun n => C * (h n c - h m c)) atTop (𝓝 (C * (H c - h m c))) :=
          tendsto_const_nhds.mul (hc_lim.sub tendsto_const_nhds)
        exact le_of_tendsto_of_tendsto ht1 ht2
          (Filter.eventually_atTop.mpr ⟨m, fun n hmn => hdiff_bound hmn w hw⟩)
    have hH_cont : ContinuousOn H (closedBall c r) := by
      intro z hz
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have ht0 : Tendsto (fun m => C * (H c - h m c)) atTop (𝓝 0) := by
        simpa [H, sub_self, mul_zero] using
          (tendsto_const_nhds (x := C)).mul ((tendsto_const_nhds (x := H c)).sub hc_lim)
      obtain ⟨m, hm⟩ := (ht0.eventually (gt_mem_nhds (show 0 < ε / 3 by positivity))).exists
      have hmc : ContinuousWithinAt (h m) (closedBall c r) z :=
        ((hh m).continuousOn.mono (hcbr_sub.trans (ball_subset_closedBall.trans hcbR'_sub))) z hz
      rw [Metric.continuousWithinAt_iff] at hmc
      obtain ⟨δ, hδ, hδ_prop⟩ := hmc (ε / 3) (by positivity)
      refine ⟨δ, hδ, fun w hw hwd => ?_⟩
      rw [Real.dist_eq]
      have h1 := hunif m w hw
      have h2 := hunif m z hz
      have h3 : |h m w - h m z| < ε / 3 := by simpa [Real.dist_eq] using hδ_prop hw hwd
      rw [abs_lt] at h3 ⊢
      constructor <;> linarith
    have hH_eq_pois : ∀ w ∈ ball c r, H w = poissonInt c r H w := by
      intro w hw
      have hpois_le : ∀ m, h m w ≤ poissonInt c r H w ∧
          poissonInt c r H w ≤ h m w + C * (H c - h m c) := by
        intro m
        have hmh : HarmonicOnNhd (h m) (closedBall c r) :=
          (hh m).mono (hcbr_sub.trans (ball_subset_closedBall.trans hcbR'_sub))
        have hm_eq : poissonInt c r (h m) w = h m w := hmh.circleAverage_poissonKernel_smul hw
        have hm_cont : ContinuousOn (h m) (sphere c r) :=
          hmh.continuousOn.mono sphere_subset_closedBall
        constructor
        · rw [← hm_eq]
          exact poissonInt_mono hr_pos hw hm_cont (hH_cont.mono sphere_subset_closedBall)
            fun ζ hζ => by linarith [(hunif m ζ (sphere_subset_closedBall hζ)).1]
        · have hup := poissonInt_mono hr_pos hw (g₂ := fun ζ => h m ζ + C * (H c - h m c))
            (hH_cont.mono sphere_subset_closedBall)
            (hm_cont.add continuousOn_const)
            fun ζ hζ => by linarith [(hunif m ζ (sphere_subset_closedBall hζ)).2]
          rw [poissonInt_add_const hr_pos hw hm_cont, hm_eq] at hup
          exact hup
      have hle1 : H w ≤ poissonInt c r H w :=
        le_of_tendsto (hlim_r w (ball_subset_closedBall hw))
          (Filter.Eventually.of_forall fun m => (hpois_le m).1)
      have ht_rhs : Tendsto (fun m => h m w + C * (H c - h m c)) atTop (𝓝 (H w)) := by
        simpa [H, sub_self, mul_zero, add_zero] using
          (hlim_r w (ball_subset_closedBall hw)).add
            ((tendsto_const_nhds (x := C)).mul ((tendsto_const_nhds (x := H c)).sub hc_lim))
      have hle2 : poissonInt c r H w ≤ H w :=
        ge_of_tendsto ht_rhs (Filter.Eventually.of_forall fun m => (hpois_le m).2)
      exact le_antisymm hle1 hle2
    have hH_harm : HarmonicOnNhd H (ball c r) := by
      have hp := poissonInt_harmonicOnNhd hr_pos (hH_cont.mono sphere_subset_closedBall)
      intro w hw
      refine (harmonicAt_congr_nhds ?_).mpr (hp w hw)
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hH_eq_pois z hz
    exact ⟨hbdd_r, hlim_r, hH_harm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    let r : ℝ := (‖z - c‖ + R) / 2
    have hzn : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
    have hr_pos : 0 < r := by dsimp only [r]; linarith [norm_nonneg (z - c)]
    have hr_lt : r < R := by dsimp only [r]; linarith
    exact (hball_r r hr_pos hr_lt).1 z (mem_closedBall_iff_norm.mpr (by dsimp only [r]; linarith))
  · intro z hz
    let r : ℝ := (‖z - c‖ + R) / 2
    have hzn : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
    have hr_pos : 0 < r := by dsimp only [r]; linarith [norm_nonneg (z - c)]
    have hr_lt : r < R := by dsimp only [r]; linarith
    exact (hball_r r hr_pos hr_lt).2.1 z (mem_closedBall_iff_norm.mpr (by dsimp only [r]; linarith))
  · intro z hz
    let r : ℝ := (‖z - c‖ + R) / 2
    have hzn : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
    have hr_pos : 0 < r := by dsimp only [r]; linarith [norm_nonneg (z - c)]
    have hr_lt : r < R := by dsimp only [r]; linarith
    exact (hball_r r hr_pos hr_lt).2.2 z (mem_ball_iff_norm.mpr (by dsimp only [r]; linarith))

private lemma log_norm_harmonicAt {c z : ℂ} (h : z ≠ c) :
    HarmonicAt (fun w => Real.log ‖w - c‖) z := by
  have hzc : z - c ≠ 0 := sub_ne_zero.mpr h
  have hnorm_pos : 0 < ‖z - c‖ := norm_pos_iff.mpr hzc
  let α : ℂ := (z - c)⁻¹
  let δ : ℝ := ‖z - c‖ / 2
  have hδ : 0 < δ := half_pos hnorm_pos
  let F : ℂ → ℂ := fun w => Complex.log (α * (w - c)) + (Real.log ‖z - c‖ : ℂ)
  have hslit : ∀ w ∈ ball z δ, α * (w - c) ∈ Complex.slitPlane := by
    intro w hw
    have hdist : ‖w - z‖ < ‖z - c‖ / 2 := mem_ball_iff_norm.mp hw
    have hdiff : α * (w - c) - 1 = α * (w - z) := by
      have : α * (z - c) = 1 := inv_mul_cancel₀ hzc
      calc α * (w - c) - 1 = α * (w - c) - α * (z - c) := by rw [this]
        _ = α * (w - z) := by ring
    have hlt : ‖α * (w - c) - 1‖ < 1 / 2 := by
      rw [hdiff, norm_mul, norm_inv]
      calc ‖z - c‖⁻¹ * ‖w - z‖ < ‖z - c‖⁻¹ * (‖z - c‖ / 2) :=
            mul_lt_mul_of_pos_left hdist (inv_pos.mpr hnorm_pos)
        _ = 1 / 2 := by field_simp [hnorm_pos.ne']
    have hre_sub : 1 - (α * (w - c)).re ≤ ‖α * (w - c) - 1‖ := by
      calc 1 - (α * (w - c)).re = (-(α * (w - c) - 1)).re := by simp
        _ ≤ ‖-(α * (w - c) - 1)‖ := Complex.re_le_norm _
        _ = ‖α * (w - c) - 1‖ := norm_neg _
    exact Or.inl (by linarith)
  have hF_diff : DifferentiableOn ℂ F (ball z δ) := by
    intro w hw
    have hd1 : HasDerivAt (fun x => α * (x - c)) α w := by
      simpa using ((hasDerivAt_id w).sub_const c).const_mul α
    have hd2 : HasDerivAt (fun x => Complex.log (α * (x - c))) ((α * (w - c))⁻¹ * α) w :=
      (Complex.hasDerivAt_log (hslit w hw)).comp w hd1 |> fun h => by simpa [Function.comp_def] using h
    exact (hd2.add_const _).differentiableAt.differentiableWithinAt
  have hF_ana : AnalyticAt ℂ F z := hF_diff.analyticAt (ball_mem_nhds z hδ)
  refine (harmonicAt_congr_nhds ?_).mp hF_ana.harmonicAt_re
  filter_upwards [ball_mem_nhds z hδ] with w hw
  have hwc_ne : w - c ≠ 0 := by
    have hs := hslit w hw
    intro h0
    rw [h0, mul_zero] at hs
    simp [Complex.slitPlane] at hs
  have hwc_pos : 0 < ‖w - c‖ := norm_pos_iff.mpr hwc_ne
  simp only [F, α, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_mul, norm_inv]
  rw [Real.log_mul (inv_ne_zero hnorm_pos.ne') hwc_pos.ne', Real.log_inv]
  ring

open Classical in
private lemma harmonic_removable_singularity {c : ℂ} {R M : ℝ} (hR : 0 < R)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u (ball c R \ {c}))
    (hbdd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M) :
    ∃ u_ext : ℂ → ℝ, HarmonicOnNhd u_ext (ball c R) ∧ ∀ z ∈ ball c R \ {c}, u_ext z = u z := by
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hsph_sub : sphere c r ⊆ ball c R \ {c} := by
    intro z hz
    have hzn : ‖z - c‖ = r := mem_sphere_iff_norm.mp hz
    refine ⟨mem_ball_iff_norm.mpr (by linarith), ?_⟩
    intro heq; rw [heq, sub_self, norm_zero] at hzn; linarith
  have hu_sph : ContinuousOn u (sphere c r) := hu.continuousOn.mono hsph_sub
  let P : ℂ → ℝ := fun w => if w ∈ ball c r then poissonInt c r u w else u w
  have hP_harm : HarmonicOnNhd P (ball c r) := fun w hw =>
    (harmonicAt_congr_nhds (Filter.eventually_of_mem (isOpen_ball.mem_nhds hw)
      fun z hz => by simp only [P, if_pos hz])).mpr (poissonInt_harmonicOnNhd hr hu_sph w hw)
  have hP_cont : ContinuousOn P (closedBall c r) := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heq
    · have hharm : ContinuousAt (poissonInt c r u) z :=
        (poissonInt_harmonicOnNhd hr hu_sph z hlt).1.continuousAt
      refine (hharm.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ball.mem_nhds hlt] with w hw
      simp only [P, if_pos hw]
    · have hzs : z ∈ sphere c r := heq
      have hnot : z ∉ ball c r := by rw [mem_ball]; linarith
      rw [ContinuousWithinAt, show P z = u z by simp only [P, if_neg hnot],
        Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ₁, hδ₁, h₁⟩ := (Metric.tendsto_nhdsWithin_nhds.mp
        (poissonInt_tendsto_boundary hr hu_sph hzs)) ε hε
      obtain ⟨δ₂, hδ₂, h₂⟩ := (Metric.continuousWithinAt_iff.mp
        (hu.continuousOn z (hsph_sub hzs))) ε hε
      refine ⟨min δ₁ (min δ₂ (r / 2)), lt_min hδ₁ (lt_min hδ₂ (half_pos hr)), fun w hw hwd => ?_⟩
      by_cases hwb : w ∈ ball c r
      · simp only [P, if_pos hwb]
        exact h₁ hwb (lt_of_lt_of_le hwd (min_le_left _ _))
      · simp only [P, if_neg hwb]
        have hw_mem : w ∈ ball c R \ {c} := by
          refine ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hw) hrR), ?_⟩
          intro hwc
          have hdz : dist w z = r := by rw [hwc, dist_comm]; exact hzs
          have : dist w z < r / 2 := lt_of_lt_of_le hwd ((min_le_right _ _).trans (min_le_right _ _))
          linarith
        exact h₂ hw_mem (lt_of_lt_of_le hwd ((min_le_right _ _).trans (min_le_left _ _)))
  have hM_nn : 0 ≤ M := by
    have h0 := hbdd (c + (r : ℂ)) (hsph_sub (by
      rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]))
    exact (abs_nonneg _).trans h0
  have hP_bdd : ∀ w ∈ ball c r, |P w| ≤ M := by
    intro w hw
    simp only [P, if_pos hw]
    have h1 := poissonInt_mono hr hw (g₂ := fun _ => M) hu_sph continuousOn_const fun ζ hζ =>
      (le_abs_self _).trans (hbdd ζ (hsph_sub hζ))
    have h2 := poissonInt_mono hr hw (g₁ := fun _ => -M) continuousOn_const hu_sph fun ζ hζ =>
      (neg_le_of_abs_le (hbdd ζ (hsph_sub hζ)))
    rw [poissonInt_const hr hw] at h1 h2
    exact abs_le.mpr ⟨h2, h1⟩
  -- Show v = u - P vanishes on ball c r \ {c} via the maximum principle on annuli.
  have hv_le_zero : ∀ (s : ℝ), s = 1 ∨ s = -1 →
      ∀ w₀ ∈ ball c r \ {c}, s * (u w₀ - P w₀) ≤ 0 := by
    intro s hs w₀ ⟨hw₀b, hw₀ne⟩
    have hw₀_pos : 0 < ‖w₀ - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw₀ne)
    have hw₀_lt : ‖w₀ - c‖ < r := mem_ball_iff_norm.mp hw₀b
    by_contra hpos
    push Not at hpos
    have hlog_pos : 0 < Real.log (r / ‖w₀ - c‖) :=
      Real.log_pos ((one_lt_div hw₀_pos).mpr hw₀_lt)
    let ε : ℝ := (s * (u w₀ - P w₀)) / (2 * Real.log (r / ‖w₀ - c‖))
    have hε : 0 < ε := div_pos hpos (by positivity)
    let δ : ℝ := min (‖w₀ - c‖ / 2) (r * Real.exp (-(2 * M + 1) / ε))
    have hδ_pos : 0 < δ := lt_min (half_pos hw₀_pos) (mul_pos hr (Real.exp_pos _))
    have hδ_lt_w₀ : δ < ‖w₀ - c‖ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hw₀_pos)
    have hδ_lt_r : δ < r := hδ_lt_w₀.trans hw₀_lt
    let A : Set ℂ := ball c r \ closedBall c δ
    have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
    have hAb : Bornology.IsBounded A := isBounded_ball.subset sdiff_subset
    have hAcl_sub : closure A ⊆ closedBall c r \ ball c δ := by
      refine subset_inter ?_ ?_
      · exact (closure_mono sdiff_subset).trans (by rw [closure_ball c hr.ne'])
      · exact closure_minimal (fun z hz hzb => hz.2 (ball_subset_closedBall hzb)) isOpen_ball.isClosed_compl
    have hAfr_sub : frontier A ⊆ sphere c r ∪ sphere c δ := by
      intro z ⟨hz_cl, hz_not⟩
      rw [hAo.interior_eq] at hz_not
      have h1 := hAcl_sub hz_cl
      have hle_r : dist z c ≤ r := mem_closedBall.mp h1.1
      have hge_δ : δ ≤ dist z c := not_lt.mp h1.2
      by_cases hlt_r : dist z c < r
      · right
        have hle_δ : dist z c ≤ δ := by
          by_contra hgt; exact hz_not ⟨hlt_r, hgt⟩
        exact le_antisymm hle_δ hge_δ
      · left; exact le_antisymm hle_r (not_lt.mp hlt_r)
    let f : ℂ → ℝ := fun z => s * (u z - P z) + ε * (Real.log ‖z - c‖ - Real.log r)
    have hA_sub_punc : closedBall c r \ ball c δ ⊆ ball c R \ {c} := by
      intro z ⟨hz1, hz2⟩
      refine ⟨mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz1) hrR), ?_⟩
      intro hzc; apply hz2; rw [hzc]; exact mem_ball_self hδ_pos
    have hf_harm : HarmonicOnNhd f A := by
      intro z hz
      have hzn : z ≠ c := (hA_sub_punc (hAcl_sub (subset_closure hz))).2
      have hu_z : HarmonicAt u z := hu z (hA_sub_punc (hAcl_sub (subset_closure hz)))
      have hP_z : HarmonicAt P z := hP_harm z hz.1
      have hlog_z : HarmonicAt (fun w => Real.log ‖w - c‖) z := log_norm_harmonicAt hzn
      have h1 : HarmonicAt (s • (u - P)) z := (hu_z.sub hP_z).const_smul
      have h2 : HarmonicAt (ε • ((fun w => Real.log ‖w - c‖) - fun _ => Real.log r)) z :=
        (hlog_z.sub (harmonicAt_const (Real.log r))).const_smul
      convert h1.add h2 using 1
      ext w
      simp [f]
    have hf_cont : ContinuousOn f (closure A) := by
      have hu_cl : ContinuousOn u (closure A) := hu.continuousOn.mono (hAcl_sub.trans hA_sub_punc)
      have hP_cl : ContinuousOn P (closure A) := hP_cont.mono (hAcl_sub.trans sdiff_subset)
      have hlog_cl : ContinuousOn (fun z => Real.log ‖z - c‖) (closure A) := by
        refine Real.continuousOn_log.comp
          (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn fun z hz => ?_
        have hzn : z ≠ c := (hA_sub_punc (hAcl_sub hz)).2
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzn)
      exact (continuousOn_const.mul (hu_cl.sub hP_cl)).add
        (continuousOn_const.mul (hlog_cl.sub continuousOn_const))
    have hf_bd : ∀ z ∈ frontier A, f z ≤ 0 := by
      intro z hz
      rcases hAfr_sub hz with hzr | hzδ
      · have hnot : z ∉ ball c r := by rw [mem_ball]; rw [mem_sphere] at hzr; linarith
        have hzn : ‖z - c‖ = r := mem_sphere_iff_norm.mp hzr
        simp only [f, P, if_neg hnot, sub_self, mul_zero, hzn, add_zero, le_refl]
      · have hzn : ‖z - c‖ = δ := mem_sphere_iff_norm.mp hzδ
        have hzb : z ∈ ball c r := mem_ball_iff_norm.mpr (by linarith)
        have h1 : |u z| ≤ M := hbdd z (hA_sub_punc (hAcl_sub hz.1))
        have h2 : |P z| ≤ M := hP_bdd z hzb
        have h3 : s * (u z - P z) ≤ 2 * M := by
          rcases hs with rfl | rfl <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2,
            (abs_le.mp h2).1, (abs_le.mp h2).2]
        have hδ_le : δ ≤ r * Real.exp (-(2 * M + 1) / ε) := min_le_right _ _
        have hlog_le : Real.log δ - Real.log r ≤ -(2 * M + 1) / ε := by
          have h1' : Real.log δ ≤ Real.log (r * Real.exp (-(2 * M + 1) / ε)) :=
            Real.log_le_log hδ_pos hδ_le
          rw [Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp] at h1'
          linarith
        have h4 : ε * (Real.log δ - Real.log r) ≤ -(2 * M + 1) := by
          have := mul_le_mul_of_nonneg_left hlog_le hε.le
          rwa [mul_div_cancel₀ _ hε.ne'] at this
        dsimp only [f]
        rw [hzn]
        linarith
    have hw₀A : w₀ ∈ A := ⟨hw₀b, by rw [mem_closedBall_iff_norm]; linarith⟩
    have hle0 := IsSubharmOnC.max_principle_bounded hAo hAb hf_cont
      (HarmonicOnNhd.isSubharmOnC hAo hf_harm) hf_bd w₀ (subset_closure hw₀A)
    have hlog_diff : Real.log ‖w₀ - c‖ - Real.log r = -Real.log (r / ‖w₀ - c‖) := by
      rw [Real.log_div hr.ne' hw₀_pos.ne']; ring
    dsimp only [f] at hle0
    rw [hlog_diff] at hle0
    have hε_eq : ε * Real.log (r / ‖w₀ - c‖) = s * (u w₀ - P w₀) / 2 := by
      dsimp only [ε]
      field_simp [hlog_pos.ne']
    linarith
  have hu_eq_P : ∀ w ∈ ball c r \ {c}, u w = P w := by
    intro w hw
    have h1 := hv_le_zero 1 (Or.inl rfl) w hw
    have h2 := hv_le_zero (-1) (Or.inr rfl) w hw
    linarith
  let u_ext : ℂ → ℝ := fun w => if w = c then P c else u w
  refine ⟨u_ext, ?_, fun z hz => if_neg (show z ≠ c from hz.2)⟩
  intro z hz
  by_cases hzc : z = c
  · subst hzc
    refine (harmonicAt_congr_nhds ?_).mpr (hP_harm z (mem_ball_self hr))
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    by_cases hwc : w = z
    · simp only [u_ext, hwc]
      rfl
    · simp only [u_ext, if_neg hwc, hu_eq_P w ⟨hw, hwc⟩]
  · refine (harmonicAt_congr_nhds ?_).mpr (hu z ⟨hz, hzc⟩)
    filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, hzc⟩] with w hw
    exact if_neg (show w ≠ c from hw.2)

/- ### Part 5A: Potential theory and connectedness on `UCov Ω w₀` -/

open Classical in
private def uPull {α : Type*} [Zero α] {Ω : Set ℂ} {w₀ : Ω}
    (f : UCov Ω w₀ → α) (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω) :
    ℂ → α :=
  fun z => if h : z ∈ ball p.pt.1 r then f (uChart p hr hsub z h) else 0

open Classical in
private lemma uPull_apply {α : Type*} [Zero α] {Ω : Set ℂ} {w₀ : Ω}
    (f : UCov Ω w₀ → α) (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
    {z : ℂ} (hz : z ∈ ball p.pt.1 r) :
    uPull f p hr hsub z = f (uChart p hr hsub z hz) :=
  dif_pos hz

open Classical in
private lemma uPull_self {α : Type*} [Zero α] {Ω : Set ℂ} {w₀ : Ω}
    (f : UCov Ω w₀ → α) (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω) :
    uPull f p hr hsub p.pt.1 = f p := by
  rw [uPull_apply f p hr hsub (mem_ball_self hr), uChart_self]

open Classical in
private lemma uPull_eq_on_sub {α : Type*} [Zero α] {Ω : Set ℂ} {w₀ : Ω}
    (f : UCov Ω w₀ → α) {p : UCov Ω w₀} {r ρ : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
    {q : UCov Ω w₀} (hq : q ∈ uBall p hr hsub)
    (hρ : 0 < ρ) (hρsub : ball q.pt.1 ρ ⊆ ball p.pt.1 r)
    {z : ℂ} (hz : z ∈ ball q.pt.1 ρ) :
    uPull f q hρ (hρsub.trans hsub) z = uPull f p hr hsub z := by
  rw [uPull_apply f q hρ _ hz, uPull_apply f p hr hsub (hρsub hz)]
  exact congr_arg f (uChart_eq_uChart hr hsub hq.1 hq.2 hρ hρsub hz)

open Classical in
private lemma uChart_mem_uBall_iff {Ω : Set ℂ} {w₀ : Ω}
    (p : UCov Ω w₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsubR : ball p.pt.1 R ⊆ Ω)
    {z : ℂ} (hz : z ∈ ball p.pt.1 R) :
    uChart p (hr.trans hrR) hsubR z hz ∈ uBall p hr ((ball_subset_ball hrR.le).trans hsubR) ↔
      z ∈ ball p.pt.1 r := by
  constructor
  · intro h; exact h.1
  · intro hzr
    refine ⟨hzr, ?_⟩
    exact (uChart_eq_uChart (hr.trans hrR) hsubR (mem_ball_self (hr.trans hrR))
      (uChart_self p (hr.trans hrR) hsubR).symm hr (ball_subset_ball hrR.le) hzr).symm

private lemma continuousOn_uPull {α : Type*} [MetricSpace α] [Zero α]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω} {f : UCov Ω w₀ → α} {U : Set (UCov Ω w₀)}
    (hf : ContinuousOn f U) (p : UCov Ω w₀) {r : ℝ} (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
    (hU : uBall p hr hsub ⊆ U) : ContinuousOn (uPull f p hr hsub) (ball p.pt.1 r) := by
  intro z₀ hz₀
  have h1 : ContinuousAt (fun z : ball p.pt.1 r => f (uChart p hr hsub z.1 z.2)) ⟨z₀, hz₀⟩ := by
    have hcomp : ContinuousOn f (uBall p hr hsub) := hf.mono hU
    have hch := continuousOn_uChart hΩ p hr hsub
    have hmap : ∀ z : ball p.pt.1 r, uChart p hr hsub z.1 z.2 ∈ uBall p hr hsub :=
      fun z => uChart_mem_uBall p hr hsub z.2
    have hcont : Continuous (fun z : ball p.pt.1 r => f (uChart p hr hsub z.1 z.2)) :=
      hcomp.comp_continuous hch hmap
    exact hcont.continuousAt
  have hopen : IsOpen (ball p.pt.1 r) := isOpen_ball
  rw [ContinuousWithinAt, nhdsWithin_eq_nhds.mpr (hopen.mem_nhds hz₀)]
  have hca : ContinuousAt (uPull f p hr hsub) z₀ := by
    rw [Metric.continuousAt_iff] at h1 ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h1 ε hε
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball z₀ hz₀
    refine ⟨min δ ρ, lt_min hδ hρ, fun z hz => ?_⟩
    have hzb : z ∈ ball p.pt.1 r := hρsub (lt_of_lt_of_le hz (min_le_right _ _))
    rw [uPull_apply f p hr hsub hzb, uPull_apply f p hr hsub hz₀]
    exact hδ' (show dist (⟨z, hzb⟩ : ball p.pt.1 r) ⟨z₀, hz₀⟩ < δ from lt_of_lt_of_le hz (min_le_left _ _))
  exact hca

private lemma continuousOn_of_uPull {α : Type*} [TopologicalSpace α] [Zero α]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω} {f : UCov Ω w₀ → α} {U : Set (UCov Ω w₀)}
    (hloc : ∀ p ∈ U, ∃ (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      uBall p hr hsub ⊆ U ∧ ContinuousOn (uPull f p hr hsub) (ball p.pt.1 r)) :
    ContinuousOn f U := by
  intro p hp
  obtain ⟨r, hr, hsub, hBU, hcont⟩ := hloc p hp
  have hca : ContinuousAt (uPull f p hr hsub) p.pt.1 :=
    hcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hcomp : ContinuousAt (fun q : UCov Ω w₀ => uPull f p hr hsub (uProjC q)) p :=
    ContinuousAt.comp (g := uPull f p hr hsub) (f := uProjC) hca (continuous_uProjC hΩ).continuousAt
  have hev : (fun q : UCov Ω w₀ => uPull f p hr hsub (uProjC q)) =ᶠ[𝓝 p] f := by
    filter_upwards [(isOpen_uBall hΩ p hr hsub).mem_nhds (mem_uBall_self p hr hsub)] with q hq
    change uPull f p hr hsub q.pt.1 = f q
    rw [uPull_apply f p hr hsub hq.1, ← hq.2]
  exact (hcomp.congr hev).continuousWithinAt

private def uClosedBall {Ω : Set ℂ} {w₀ : Ω} (p : UCov Ω w₀) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hsubR : ball p.pt.1 R ⊆ Ω) : Set (UCov Ω w₀) :=
  {q ∈ uBall p (hr.trans hrR) hsubR | q.pt.1 ∈ closedBall p.pt.1 r}

private lemma isCompact_uClosedBall {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    (p : UCov Ω w₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsubR : ball p.pt.1 R ⊆ Ω) :
    IsCompact (uClosedBall p hr hrR hsubR) := by
  let g : closedBall p.pt.1 r → UCov Ω w₀ :=
    fun z => uChart p (hr.trans hrR) hsubR z.1 (closedBall_subset_ball hrR z.2)
  have hg_cont : Continuous g := by
    let ι : closedBall p.pt.1 r → ball p.pt.1 R :=
      fun z => ⟨z.1, closedBall_subset_ball hrR z.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    exact (continuousOn_uChart hΩ p (hr.trans hrR) hsubR).comp hι
  have himg : g '' univ = uClosedBall p hr hrR hsubR := by
    ext q
    simp only [mem_image, mem_univ, true_and, uClosedBall, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact ⟨uChart_mem_uBall p (hr.trans hrR) hsubR (closedBall_subset_ball hrR hz), hz⟩
    · rintro ⟨⟨hqR, hqeq⟩, hqr⟩
      exact ⟨⟨q.pt.1, hqr⟩, hqeq.symm⟩
  rw [← himg]
  have : CompactSpace (closedBall p.pt.1 r) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_univ.image hg_cont

private lemma isClosed_uClosedBall {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    (p : UCov Ω w₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsubR : ball p.pt.1 R ⊆ Ω) :
    IsClosed (uClosedBall p hr hrR hsubR) := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  exact (isCompact_uClosedBall hΩ p hr hrR hsubR).isClosed

private def IsSubharmOnUCov {Ω : Set ℂ} {w₀ : Ω} (u : UCov Ω w₀ → ℝ) (U : Set (UCov Ω w₀)) : Prop :=
  ContinuousOn u U ∧
    ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      uBall p hr hsub ⊆ U → IsSubharmOnC (uPull u p hr hsub) (ball p.pt.1 r)

private def IsHarmOnUCov {Ω : Set ℂ} {w₀ : Ω} (u : UCov Ω w₀ → ℝ) (U : Set (UCov Ω w₀)) : Prop :=
  ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
    uBall p hr hsub ⊆ U → HarmonicOnNhd (uPull u p hr hsub) (ball p.pt.1 r)

private lemma isSubharmOnUCov_of_local {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    {u : UCov Ω w₀ → ℝ} {U : Set (UCov Ω w₀)}
    (hcont : ContinuousOn u U)
    (hloc : ∀ p ∈ U, ∃ (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      uBall p hr hsub ⊆ U ∧ IsSubharmOnC (uPull u p hr hsub) (ball p.pt.1 r)) :
    IsSubharmOnUCov u U := by
  refine ⟨hcont, fun p r hr hsub hBU => ?_⟩
  refine ⟨continuousOn_uPull hΩ hcont p hr hsub hBU, fun z hz => ?_⟩
  let q := uChart p hr hsub z hz
  have hqB : q ∈ uBall p hr hsub := uChart_mem_uBall p hr hsub hz
  obtain ⟨r₁, hr₁, hsub₁, -, hs₁⟩ := hloc q (hBU hqB)
  obtain ⟨r₂, hr₂, hr₂avg⟩ := hs₁.2 z (mem_ball_self hr₁)
  obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  let r₀ : ℝ := min r₁ (min r₂ r₃)
  refine ⟨r₀, lt_min hr₁ (lt_min hr₂ hr₃), fun ρ hρ hρ_lt hcb => ?_⟩
  have hρ1 : ρ < r₁ := lt_of_lt_of_le hρ_lt (min_le_left _ _)
  have hρ2 : ρ < r₂ := lt_of_lt_of_le hρ_lt ((min_le_right _ _).trans (min_le_left _ _))
  have hρ3 : ρ < r₃ := lt_of_lt_of_le hρ_lt ((min_le_right _ _).trans (min_le_right _ _))
  have hsub_ρ : ball z r₀ ⊆ ball p.pt.1 r := (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hr₃sub
  have hsub_ρ1 : ball z r₀ ⊆ ball q.pt.1 r₁ := ball_subset_ball (min_le_left _ _)
  have havg1 := hr₂avg ρ hρ hρ2 (closedBall_subset_ball hρ1)
  have hpt_eq : uPull u q hr₁ hsub₁ z = uPull u p hr hsub z := by
    change uPull u q hr₁ hsub₁ q.pt.1 = uPull u p hr hsub z
    rw [uPull_self, uPull_apply u p hr hsub hz]
  have hsph_eq : Set.EqOn (uPull u q hr₁ hsub₁) (uPull u p hr hsub) (sphere z |ρ|) := by
    intro ζ hζ
    rw [abs_of_pos hρ] at hζ
    have hζr₀ : ζ ∈ ball z r₀ := mem_ball.mpr (by rw [mem_sphere.mp hζ]; exact hρ_lt)
    have h1 := uPull_eq_on_sub u hr hsub hqB (lt_min hr₁ (lt_min hr₂ hr₃)) hsub_ρ hζr₀
    have h2 := uPull_eq_on_sub u hr₁ hsub₁ (mem_uBall_self q hr₁ hsub₁)
      (lt_min hr₁ (lt_min hr₂ hr₃)) hsub_ρ1 hζr₀
    exact h2.symm.trans h1
  rw [hpt_eq, Real.circleAverage_congr_sphere hsph_eq] at havg1
  exact havg1

private lemma isHarmOnUCov_of_local {Ω : Set ℂ} {w₀ : Ω}
    {u : UCov Ω w₀ → ℝ} {U : Set (UCov Ω w₀)}
    (hloc : ∀ p ∈ U, ∃ (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      uBall p hr hsub ⊆ U ∧ HarmonicOnNhd (uPull u p hr hsub) (ball p.pt.1 r)) :
    IsHarmOnUCov u U := by
  intro p r hr hsub hBU z hz
  let q := uChart p hr hsub z hz
  have hqB : q ∈ uBall p hr hsub := uChart_mem_uBall p hr hsub hz
  obtain ⟨r₁, hr₁, hsub₁, -, hh₁⟩ := hloc q (hBU hqB)
  obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  let ρ : ℝ := min r₁ r₃
  have hρ : 0 < ρ := lt_min hr₁ hr₃
  have hsub_p : ball z ρ ⊆ ball p.pt.1 r := (ball_subset_ball (min_le_right _ _)).trans hr₃sub
  have hsub_q : ball z ρ ⊆ ball q.pt.1 r₁ := ball_subset_ball (min_le_left _ _)
  refine (harmonicAt_congr_nhds ?_).mp (hh₁ z (mem_ball_self hr₁))
  filter_upwards [ball_mem_nhds z hρ] with ζ hζ
  have h1 := uPull_eq_on_sub u hr hsub hqB hρ hsub_p hζ
  have h2 := uPull_eq_on_sub u hr₁ hsub₁ (mem_uBall_self q hr₁ hsub₁) hρ hsub_q hζ
  exact h2.symm.trans h1

private lemma IsHarmOnUCov.isSubharmOnUCov {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    {u : UCov Ω w₀ → ℝ} {U : Set (UCov Ω w₀)} (hu : IsHarmOnUCov u U)
    (hUo : IsOpen U) : IsSubharmOnUCov u U := by
  refine ⟨continuousOn_of_uPull hΩ fun p hp => ?_, fun p r hr hsub hBU =>
    HarmonicOnNhd.isSubharmOnC isOpen_ball (hu p r hr hsub hBU)⟩
  obtain ⟨S, ⟨q, R, hR, hsubR, rfl⟩, hpS, hSU⟩ :=
    (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hp
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
  have hBsub : uBall p hρ (hρsub.trans hsubR) ⊆ U :=
    (uBall_subset_uBall hR hsubR hpS hρ hρsub).trans hSU
  exact ⟨ρ, hρ, hρsub.trans hsubR, hBsub, (hu p ρ hρ (hρsub.trans hsubR) hBsub).continuousOn⟩

private lemma IsSubharmOnUCov.sup {Ω : Set ℂ} {w₀ : Ω}
    {u v : UCov Ω w₀ → ℝ} {U : Set (UCov Ω w₀)}
    (hu : IsSubharmOnUCov u U) (hv : IsSubharmOnUCov v U) :
    IsSubharmOnUCov (fun p => max (u p) (v p)) U := by
  refine ⟨hu.1.sup hv.1, fun p r hr hsub hBU => ?_⟩
  have hsup := IsSubharmOnC.sup (hu.2 p r hr hsub hBU) (hv.2 p r hr hsub hBU)
  have heq : Set.EqOn (fun z => max (uPull u p hr hsub z) (uPull v p hr hsub z))
      (uPull (fun q => max (u q) (v q)) p hr hsub) (ball p.pt.1 r) := fun z hz => by
    simp only [uPull_apply _ p hr hsub hz]
  refine ⟨hsup.1.congr fun z hz => (heq hz).symm, fun z hz => ?_⟩
  obtain ⟨r₀, hr₀, havg⟩ := hsup.2 z hz
  refine ⟨r₀, hr₀, fun ρ hρ hρlt hcb => ?_⟩
  have h1 := havg ρ hρ hρlt hcb
  rw [heq hz] at h1
  refine h1.trans_eq (Real.circleAverage_congr_sphere fun ζ hζ => ?_)
  rw [abs_of_pos hρ] at hζ
  exact heq (hcb (sphere_subset_closedBall hζ))

private lemma isPreconnected_ball_diff_center {c : ℂ} {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball c r \ {c}) := by
  have hpc : IsPathConnected (ball c r \ {c}) := by
    let z₀ : ℂ := c + ((r / 2 : ℝ) : ℂ)
    have hz₀_mem : z₀ ∈ ball c r \ {c} := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball_iff_norm, show z₀ - c = ((r / 2 : ℝ) : ℂ) by simp [z₀],
          Complex.norm_real, Real.norm_of_nonneg (half_pos hr).le]
        linarith
      · intro h
        have h0 : z₀ = c := h
        have h1 : ((r / 2 : ℝ) : ℂ) = 0 := by dsimp only [z₀] at h0; linear_combination h0
        have h2 : r / 2 = 0 := Complex.ofReal_eq_zero.mp h1
        linarith
    refine ⟨z₀, hz₀_mem, fun z ⟨hzb, hzne⟩ => ?_⟩
    have hzn_pos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
    have hzn_lt : ‖z - c‖ < r := mem_ball_iff_norm.mp hzb
    let θ := (z - c).arg
    refine ⟨{
      toFun := fun t => c + (((1 - (t : ℝ)) * (r / 2) + (t : ℝ) * ‖z - c‖ : ℝ) : ℂ) *
        Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I)
      continuous_toFun := by fun_prop
      source' := by simp [z₀]
      target' := by
        simp only [Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
        have := Complex.norm_mul_exp_arg_mul_I (z - c)
        rw [this]; ring
    }, fun t => ?_⟩
    let ρt : ℝ := (1 - (t : ℝ)) * (r / 2) + (t : ℝ) * ‖z - c‖
    have hρt_pos : 0 < ρt := by
      dsimp only [ρt]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
      nlinarith
    have hρt_lt : ρt < r := by
      dsimp only [ρt]
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
      nlinarith
    have hnorm : ‖((ρt : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I))‖ = ρt := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρt_pos.le,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    refine ⟨?_, ?_⟩
    · change c + (ρt : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I) ∈ ball c r
      rw [mem_ball_iff_norm, add_sub_cancel_left, hnorm]; exact hρt_lt
    · intro h
      have h0 : c + (ρt : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I) = c := h
      have h1 : (ρt : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I) = 0 := by linear_combination h0
      have h2 : ‖((ρt : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I))‖ = 0 := by
        rw [h1, norm_zero]
      linarith
  exact (hpc.isConnected).isPreconnected

private lemma isPreconnected_compl_singleton_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsPathConnected Ω) (w₀ : Ω) (a : UCov Ω w₀) :
    IsPreconnected ({a}ᶜ : Set (UCov Ω w₀)) := by
  have : PathConnectedSpace (UCov Ω w₀) := pathConnectedSpace_UCov hΩ hΩc w₀
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ a.pt.1 a.pt.2
  let B : Set (UCov Ω w₀) := uBall a hr hsub
  have hB_open : IsOpen B := isOpen_uBall hΩ a hr hsub
  have haB : a ∈ B := mem_uBall_self a hr hsub
  have hBpunc_pc : IsPreconnected (B \ {a}) := by
    let g : ball a.pt.1 r → UCov Ω w₀ := fun z => uChart a hr hsub z.1 z.2
    have hg : Continuous g := continuousOn_uChart hΩ a hr hsub
    let S0 : Set (ball a.pt.1 r) := Subtype.val ⁻¹' (ball a.pt.1 r \ {a.pt.1})
    have hS0_pc : IsPreconnected S0 := by
      have hhomeo : IsInducing ((↑) : ball a.pt.1 r → ℂ) := IsInducing.subtypeVal
      have himg : ((↑) : ball a.pt.1 r → ℂ) '' S0 = ball a.pt.1 r \ {a.pt.1} := by
        ext z; simp only [mem_image, S0, mem_preimage, Set.mem_sdiff]
        exact ⟨fun ⟨⟨w, _⟩, hw, h⟩ => h ▸ hw, fun hw => ⟨⟨z, hw.1⟩, hw, rfl⟩⟩
      exact hhomeo.isPreconnected_image.mp (by rw [himg]; exact isPreconnected_ball_diff_center hr)
    have hg_img : g '' S0 = B \ {a} := by
      ext q
      simp only [mem_image, S0, mem_preimage, Set.mem_sdiff, B, uBall]
      constructor
      · rintro ⟨⟨z, hz⟩, ⟨_, hzne⟩, rfl⟩
        exact ⟨⟨hz, rfl⟩, fun h => hzne (congr_arg uProjC h)⟩
      · rintro ⟨⟨hqz, hqeq⟩, hqne⟩
        refine ⟨⟨q.pt.1, hqz⟩, ⟨hqz, fun h => hqne ?_⟩, hqeq.symm⟩
        exact uBall_injOn_uProjC a hr hsub ⟨hqz, hqeq⟩ (mem_uBall_self a hr hsub) h
    rw [← hg_img]
    exact hS0_pc.image g hg.continuousOn
  intro U V hUo hVo hcov hUne hVne
  by_contra hdisj
  have hdisj' : Disjoint (U ∩ {a}ᶜ) (V ∩ {a}ᶜ) := by
    rw [Set.disjoint_left]
    intro p ⟨hpU, hpa⟩ ⟨hpV, _⟩
    exact hdisj ⟨p, hpa, hpU, hpV⟩
  have hBp_cov : B \ {a} ⊆ U ∪ V := fun p hp => hcov hp.2
  have hBp_disj : ¬((B \ {a}) ∩ (U ∩ V)).Nonempty := by
    rintro ⟨p, ⟨_, hpa⟩, hpU, hpV⟩
    exact hdisj ⟨p, hpa, hpU, hpV⟩
  have hsub_or : B \ {a} ⊆ U ∨ B \ {a} ⊆ V := by
    by_cases h1 : ((B \ {a}) ∩ U).Nonempty
    · by_cases h2 : ((B \ {a}) ∩ V).Nonempty
      · exact absurd (hBpunc_pc U V hUo hVo hBp_cov h1 h2) hBp_disj
      · left; intro p hp
        rcases hBp_cov hp with hpU | hpV
        · exact hpU
        · exact absurd ⟨p, hp, hpV⟩ h2
    · right; intro p hp
      rcases hBp_cov hp with hpU | hpV
      · exact absurd ⟨p, hp, hpU⟩ h1
      · exact hpV
  rcases hsub_or with hBU | hBV
  · let U' := U ∪ B
    let V' := V \ {a}
    have hU'o : IsOpen U' := hUo.union hB_open
    have hV'o : IsOpen V' := hVo.sdiff isClosed_singleton
    have hcov' : (univ : Set (UCov Ω w₀)) ⊆ U' ∪ V' := fun p _ => by
      by_cases hpa : p = a
      · left; right; exact hpa ▸ haB
      · rcases hcov hpa with hpU | hpV
        · left; left; exact hpU
        · right; exact ⟨hpV, hpa⟩
    obtain ⟨pV, hpVa, hpV⟩ := hVne
    obtain ⟨q, -, hqU', hqV'⟩ := isPreconnected_univ U' V' hU'o hV'o hcov'
      ⟨a, trivial, Or.inr haB⟩ ⟨pV, trivial, hpV, hpVa⟩
    rcases hqU' with hqU | hqB
    · exact hdisj ⟨q, hqV'.2, hqU, hqV'.1⟩
    · exact hdisj ⟨q, hqV'.2, hBU ⟨hqB, hqV'.2⟩, hqV'.1⟩
  · let U' := U \ {a}
    let V' := V ∪ B
    have hU'o : IsOpen U' := hUo.sdiff isClosed_singleton
    have hV'o : IsOpen V' := hVo.union hB_open
    have hcov' : (univ : Set (UCov Ω w₀)) ⊆ U' ∪ V' := fun p _ => by
      by_cases hpa : p = a
      · right; right; exact hpa ▸ haB
      · rcases hcov hpa with hpU | hpV
        · left; exact ⟨hpU, hpa⟩
        · right; left; exact hpV
    obtain ⟨pU, hpUa, hpU⟩ := hUne
    obtain ⟨q, -, hqU', hqV'⟩ := isPreconnected_univ U' V' hU'o hV'o hcov'
      ⟨pU, trivial, hpU, hpUa⟩ ⟨a, trivial, Or.inr haB⟩
    rcases hqV' with hqV | hqB
    · exact hdisj ⟨q, hqU'.2, hqU'.1, hqV⟩
    · exact hdisj ⟨q, hqU'.2, hqU'.1, hBV ⟨hqB, hqU'.2⟩⟩

private lemma circleAverage_eq_max_imp_eq_on_sphere {v : ℂ → ℝ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hvc : ContinuousOn v (sphere c r)) (hle : ∀ ζ ∈ sphere c r, v ζ ≤ M)
    (havg : M ≤ Real.circleAverage v c r) : ∀ ζ ∈ sphere c r, v ζ = M := by
  intro ζ hζ
  by_contra hne
  have hlt : v ζ < M := lt_of_le_of_ne (hle ζ hζ) hne
  have hle_all : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), v (circleMap c r θ) ≤ M :=
    fun θ _ => hle _ (circleMap_mem_sphere c hr.le θ)
  have hcont_θ : ContinuousOn (fun θ => v (circleMap c r θ)) (Icc 0 (2 * Real.pi)) :=
    hvc.comp (continuous_circleMap c r).continuousOn fun θ _ => circleMap_mem_sphere c hr.le θ
  have hζ_norm : ‖ζ - c‖ = r := mem_sphere_iff_norm.mp hζ
  let θ₁ := (ζ - c).arg
  let θ₀ := if 0 ≤ θ₁ then θ₁ else θ₁ + 2 * Real.pi
  have hθ₀_mem : θ₀ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    dsimp only [θ₀]
    split_ifs with h
    · exact ⟨h, (Complex.arg_le_pi _).trans (by linarith [Real.pi_pos])⟩
    · have hneg := Complex.neg_pi_lt_arg (ζ - c)
      exact ⟨by linarith, by linarith⟩
  have hθ₀_eq : circleMap c r θ₀ = ζ := by
    simp only [circleMap, θ₀]
    have hrexp : Complex.exp ((θ₀ : ℂ) * I) = Complex.exp ((θ₁ : ℂ) * I) := by
      dsimp only [θ₀]
      split_ifs
      · rfl
      · push_cast; rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have h2 : (r : ℂ) * Complex.exp ((θ₁ : ℂ) * I) = ζ - c := by
      rw [← hζ_norm]; exact Complex.norm_mul_exp_arg_mul_I (ζ - c)
    calc c + (r : ℂ) * Complex.exp ((θ₀ : ℂ) * I)
        = c + (r : ℂ) * Complex.exp ((θ₁ : ℂ) * I) := by rw [hrexp]
      _ = c + (ζ - c) := by rw [h2]
      _ = ζ := by ring
  have hint_lt : ∫ θ in (0 : ℝ)..(2 * Real.pi), v (circleMap c r θ) <
      ∫ _ in (0 : ℝ)..(2 * Real.pi), M :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by positivity) hcont_θ continuousOn_const (fun θ hθ => hle_all θ ⟨hθ.1.le, hθ.2⟩)
      ⟨θ₀, hθ₀_mem, hθ₀_eq ▸ hlt⟩
  have havg_lt : Real.circleAverage v c r < M := by
    rw [Real.circleAverage_def, smul_eq_mul]
    have hconst : (∫ _ in (0 : ℝ)..(2 * Real.pi), M) = (2 * Real.pi) * M := by simp
    rw [hconst] at hint_lt
    have h2pi : 0 < 2 * Real.pi := by positivity
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), v (circleMap c r θ)
        < (2 * Real.pi)⁻¹ * ((2 * Real.pi) * M) :=
          mul_lt_mul_of_pos_left hint_lt (inv_pos.mpr h2pi)
      _ = M := by rw [← mul_assoc, inv_mul_cancel₀ h2pi.ne', one_mul]
  linarith

private lemma strong_max_principle_UCov {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    {U : Set (UCov Ω w₀)} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {u : UCov Ω w₀ → ℝ} (hu : IsSubharmOnUCov u U) {M : ℝ} (hle : ∀ p ∈ U, u p ≤ M)
    {p₀ : UCov Ω w₀} (hp₀ : p₀ ∈ U) (hmax : u p₀ = M) :
    ∀ p ∈ U, u p = M := by
  let S : Set (UCov Ω w₀) := {p ∈ U | u p = M}
  let T : Set (UCov Ω w₀) := {p ∈ U | u p < M}
  have hTo : IsOpen T := by
    have h1 : ContinuousOn u U := hu.1
    rw [isOpen_iff_mem_nhds]
    intro p ⟨hpU, hplt⟩
    have hca : ContinuousWithinAt u U p := h1 p hpU
    have hca' : ContinuousAt u p := hca.continuousAt (hUo.mem_nhds hpU)
    exact Filter.inter_mem (hUo.mem_nhds hpU) (hca'.eventually (Iio_mem_nhds hplt))
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p ⟨hpU, hpM⟩
    obtain ⟨B, ⟨q, r, hr, hsub, rfl⟩, hpB, hBU⟩ :=
      (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hpU
    obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpB.1
    have hB₁ : uBall p hρ₁ (hρ₁sub.trans hsub) ⊆ U :=
      (uBall_subset_uBall hr hsub hpB hρ₁ hρ₁sub).trans hBU
    have hs := hu.2 p ρ₁ hρ₁ (hρ₁sub.trans hsub) hB₁
    obtain ⟨ρ₂, hρ₂, havg⟩ := hs.2 p.pt.1 (mem_ball_self hρ₁)
    let ρ := min ρ₁ ρ₂
    have hρ : 0 < ρ := lt_min hρ₁ hρ₂
    have hρ_sub : ball p.pt.1 ρ ⊆ ball p.pt.1 ρ₁ := ball_subset_ball (min_le_left _ _)
    have hBρ_sub : uBall p hρ (hρ_sub.trans (hρ₁sub.trans hsub)) ⊆ U :=
      (uBall_subset_uBall hρ₁ (hρ₁sub.trans hsub) (mem_uBall_self p hρ₁ _) hρ hρ_sub).trans hB₁
    refine Filter.mem_of_superset ((isOpen_uBall hΩ p hρ _).mem_nhds (mem_uBall_self p hρ _))
      fun x hx => ⟨hBρ_sub hx, ?_⟩
    by_cases hxp : x.pt.1 = p.pt.1
    · have hxeq : x = p := uBall_injOn_uProjC p hρ _ hx (mem_uBall_self p hρ _) hxp
      rw [hxeq]; exact hpM
    · let d : ℝ := ‖x.pt.1 - p.pt.1‖
      have hd_pos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
      have hd_lt : d < ρ := mem_ball_iff_norm.mp hx.1
      have hd_lt1 : d < ρ₁ := lt_of_lt_of_le hd_lt (min_le_left _ _)
      have hd_lt2 : d < ρ₂ := lt_of_lt_of_le hd_lt (min_le_right _ _)
      have hcb : closedBall p.pt.1 d ⊆ ball p.pt.1 ρ₁ := closedBall_subset_ball hd_lt1
      have havg_d : M ≤ Real.circleAverage (uPull u p hρ₁ (hρ₁sub.trans hsub)) p.pt.1 d := by
        have h1 := havg d hd_pos hd_lt2 hcb
        rwa [uPull_self, hpM] at h1
      have hsph_eq := circleAverage_eq_max_imp_eq_on_sphere hd_pos
        (hs.1.mono (sphere_subset_closedBall.trans hcb))
        (fun ζ hζ => by
          have hζb : ζ ∈ ball p.pt.1 ρ₁ := hcb (sphere_subset_closedBall hζ)
          rw [uPull_apply u p hρ₁ _ hζb]
          exact hle _ (hB₁ (uChart_mem_uBall p hρ₁ _ hζb)))
        havg_d x.pt.1 (mem_sphere_iff_norm.mpr rfl)
      have hxb1 : x.pt.1 ∈ ball p.pt.1 ρ₁ := hρ_sub hx.1
      rw [uPull_apply u p hρ₁ _ hxb1] at hsph_eq
      have hxeq : uChart p hρ₁ (hρ₁sub.trans hsub) x.pt.1 hxb1 = x := by
        rw [← uChart_eq_uChart hρ₁ (hρ₁sub.trans hsub) (mem_ball_self hρ₁)
          (uChart_self p hρ₁ _).symm hρ hρ_sub hx.1]
        exact hx.2.symm
      rwa [hxeq] at hsph_eq
  intro p hpU
  by_contra hne
  have hpT : p ∈ T := ⟨hpU, lt_of_le_of_ne (hle p hpU) hne⟩
  have hcov : U ⊆ S ∪ T := fun q hq => by
    rcases eq_or_lt_of_le (hle q hq) with h | h
    · exact Or.inl ⟨hq, h⟩
    · exact Or.inr ⟨hq, h⟩
  obtain ⟨q, -, hqS, hqT⟩ := hUpc S T hSo hTo hcov ⟨p₀, hp₀, hp₀, hmax⟩ ⟨p, hpU, hpT⟩
  linarith [hqS.2, hqT.2]

private lemma holo_log_norm_harmonicAt {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hne : f z ≠ 0) :
    HarmonicAt (fun w => Real.log ‖f w‖) z := by
  have hnorm_pos : 0 < ‖f z‖ := norm_pos_iff.mpr hne
  let α : ℂ := (f z)⁻¹
  have hcont : ContinuousAt (fun w => α * f w) z := continuousAt_const.mul hf.continuousAt
  have h1 : α * f z = 1 := inv_mul_cancel₀ hne
  have hslit_mem : {w : ℂ | α * f w ∈ Complex.slitPlane} ∈ 𝓝 z := by
    have hball : ball (1 : ℂ) (1 / 2) ∈ 𝓝 (α * f z) := by
      rw [h1]; exact ball_mem_nhds 1 (by norm_num)
    refine Filter.mem_of_superset (hcont hball) fun w hw => ?_
    have hlt : ‖α * f w - 1‖ < 1 / 2 := mem_ball_iff_norm.mp hw
    have hre_sub : 1 - (α * f w).re ≤ ‖α * f w - 1‖ := by
      calc 1 - (α * f w).re = (-(α * f w - 1)).re := by simp
        _ ≤ ‖-(α * f w - 1)‖ := Complex.re_le_norm _
        _ = ‖α * f w - 1‖ := norm_neg _
    exact Or.inl (by linarith)
  have hdiff_mem : {w : ℂ | DifferentiableAt ℂ f w} ∈ 𝓝 z :=
    hf.eventually_analyticAt.mono fun _ h => h.differentiableAt
  obtain ⟨δ, hδ, hδ_sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hslit_mem hdiff_mem)
  let F : ℂ → ℂ := fun w => Complex.log (α * f w) + (Real.log ‖f z‖ : ℂ)
  have hF_diff : DifferentiableOn ℂ F (ball z δ) := by
    intro w hw
    have ⟨hslit_w, hdiff_w⟩ := hδ_sub hw
    have hd1 : HasDerivAt (fun x => α * f x) (α * deriv f w) w :=
      hdiff_w.hasDerivAt.const_mul α
    have hd2 : HasDerivAt (fun x => Complex.log (α * f x)) ((α * f w)⁻¹ * (α * deriv f w)) w :=
      (Complex.hasDerivAt_log hslit_w).comp w hd1 |> fun h => by simpa [Function.comp_def] using h
    exact (hd2.add_const _).differentiableAt.differentiableWithinAt
  have hF_ana : AnalyticAt ℂ F z := hF_diff.analyticAt (ball_mem_nhds z hδ)
  refine (harmonicAt_congr_nhds ?_).mp hF_ana.harmonicAt_re
  filter_upwards [ball_mem_nhds z hδ] with w hw
  have hfw_ne : f w ≠ 0 := by
    have hs : α * f w ∈ Complex.slitPlane := (hδ_sub hw).1
    intro h0; rw [h0, mul_zero] at hs; simp [Complex.slitPlane] at hs
  have hfw_pos : 0 < ‖f w‖ := norm_pos_iff.mpr hfw_ne
  simp only [F, α, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_mul, norm_inv]
  rw [Real.log_mul (inv_ne_zero hnorm_pos.ne') hfw_pos.ne', Real.log_inv]
  ring

private lemma holo_log_max_isSubharmOnC {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (M : ℝ) :
    IsSubharmOnC (fun z => Real.log (max ‖f z‖ (Real.exp M))) U := by
  have hcont_fn : ContinuousOn (fun z => Real.log (max ‖f z‖ (Real.exp M))) U := by
    refine Real.continuousOn_log.comp
      ((continuous_norm.comp_continuousOn hf.continuousOn).sup continuousOn_const) fun z _ => ?_
    exact (lt_of_lt_of_le (Real.exp_pos M) (le_max_right _ _)).ne'
  refine ⟨hcont_fn, fun z hz => ?_⟩
  by_cases hlt : ‖f z‖ < Real.exp M
  · have hca : ContinuousAt (fun w => ‖f w‖) z :=
      continuous_norm.continuousAt.comp ((hf.differentiableAt (hU.mem_nhds hz)).continuousAt)
    obtain ⟨r₀, hr₀, hr₀_sub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hU.mem_nhds hz) (hca.eventually (Iio_mem_nhds hlt)))
    refine ⟨r₀, hr₀, fun r hr hrl _ => ?_⟩
    have hval : Real.log (max ‖f z‖ (Real.exp M)) = M := by
      rw [max_eq_right hlt.le, Real.log_exp]
    have hsph : Set.EqOn (fun w => Real.log (max ‖f w‖ (Real.exp M))) (fun _ => M) (sphere z |r|) := by
      intro w hw
      rw [abs_of_pos hr] at hw
      have hwb : w ∈ ball z r₀ := mem_ball.mpr (by rw [mem_sphere.mp hw]; exact hrl)
      have hltw : ‖f w‖ < Real.exp M := (hr₀_sub hwb).2
      change Real.log (max ‖f w‖ (Real.exp M)) = M
      rw [max_eq_right hltw.le, Real.log_exp]
    change Real.log (max ‖f z‖ (Real.exp M)) ≤ _
    rw [hval, Real.circleAverage_congr_sphere hsph, Real.circleAverage_const]
  · push Not at hlt
    have hfne : f z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos M) hlt)
    have hfana : AnalyticAt ℂ f z := hf.analyticAt (hU.mem_nhds hz)
    have hharm : HarmonicAt (fun w => Real.log ‖f w‖) z := holo_log_norm_harmonicAt hfana hfne
    have hopen_h : {w : ℂ | HarmonicAt (fun x => Real.log ‖f x‖) w} ∈ 𝓝 z :=
      (isOpen_setOfPred_harmonicAt _).mem_nhds hharm
    have hne_mem : {w : ℂ | f w ≠ 0} ∈ 𝓝 z :=
      (hfana.continuousAt.eventually (isOpen_ne.mem_nhds hfne))
    obtain ⟨r₀, hr₀, hr₀_sub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hU.mem_nhds hz) (Filter.inter_mem hopen_h hne_mem))
    have hsub_log : IsSubharmOnC (fun w => Real.log ‖f w‖) (ball z r₀) :=
      HarmonicOnNhd.isSubharmOnC isOpen_ball fun w hw => (hr₀_sub hw).2.1
    have hsub_sup : IsSubharmOnC (fun w => max (Real.log ‖f w‖) M) (ball z r₀) :=
      IsSubharmOnC.sup hsub_log (HarmonicOnNhd.isSubharmOnC isOpen_ball (harmonicOnNhd_const M))
    have heq_ball : ∀ w ∈ ball z r₀,
        Real.log (max ‖f w‖ (Real.exp M)) = max (Real.log ‖f w‖) M := by
      intro w hw
      have hwpos : 0 < ‖f w‖ := norm_pos_iff.mpr (hr₀_sub hw).2.2
      by_cases hle : ‖f w‖ ≤ Real.exp M
      · rw [max_eq_right hle, Real.log_exp,
          max_eq_right (by rw [← Real.log_exp M]; exact Real.log_le_log hwpos hle)]
      · push Not at hle
        rw [max_eq_left hle.le,
          max_eq_left (by rw [← Real.log_exp M]; exact Real.log_le_log (Real.exp_pos M) hle.le)]
    obtain ⟨r₁, hr₁, havg⟩ := hsub_sup.2 z (mem_ball_self hr₀)
    refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrl _ => ?_⟩
    have hr0 : r < r₀ := lt_of_lt_of_le hrl (min_le_left _ _)
    have hr1 : r < r₁ := lt_of_lt_of_le hrl (min_le_right _ _)
    have h1 := havg r hr hr1 (closedBall_subset_ball hr0)
    change Real.log (max ‖f z‖ (Real.exp M)) ≤ _
    rw [heq_ball z (mem_ball_self hr₀)]
    refine h1.trans_eq (Real.circleAverage_congr_sphere fun w hw => ?_)
    rw [abs_of_pos hr] at hw
    exact (heq_ball w (closedBall_subset_ball hr0 (sphere_subset_closedBall hw))).symm

open Classical in
private def poissonModUCov {Ω : Set ℂ} {w₀ : Ω}
    (u : UCov Ω w₀ → ℝ) (p : UCov Ω w₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hsubR : ball p.pt.1 R ⊆ Ω) : UCov Ω w₀ → ℝ :=
  fun q => if q ∈ uBall p hr ((ball_subset_ball hrR.le).trans hsubR)
    then poissonInt p.pt.1 r (uPull u p (hr.trans hrR) hsubR) q.pt.1
    else u q

open Classical in
private lemma poissonModUCov_spec {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    {U : Set (UCov Ω w₀)} (hUo : IsOpen U) {u : UCov Ω w₀ → ℝ} (hu : IsSubharmOnUCov u U)
    (p : UCov Ω w₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsubR : ball p.pt.1 R ⊆ Ω)
    (hBRU : uBall p (hr.trans hrR) hsubR ⊆ U) :
    let v := poissonModUCov u p hr hrR hsubR
    (∀ q ∈ U, u q ≤ v q) ∧
    IsSubharmOnUCov v U ∧
    HarmonicOnNhd (uPull v p hr ((ball_subset_ball hrR.le).trans hsubR)) (ball p.pt.1 r) ∧
    (∀ q, q ∉ uBall p hr ((ball_subset_ball hrR.le).trans hsubR) → v q = u q) ∧
    ((∀ q ∈ U, u q ≤ 0) → ∀ q ∈ U, v q ≤ 0) := by
  intro v
  have hsubr : ball p.pt.1 r ⊆ Ω := (ball_subset_ball hrR.le).trans hsubR
  have hBrR : uBall p hr hsubr ⊆ uBall p (hr.trans hrR) hsubR :=
    uBall_subset_uBall (hr.trans hrR) hsubR (mem_uBall_self p (hr.trans hrR) hsubR) hr
      (ball_subset_ball hrR.le)
  have huR_sub : IsSubharmOnC (uPull u p (hr.trans hrR) hsubR) (ball p.pt.1 R) :=
    hu.2 p R (hr.trans hrR) hsubR hBRU
  have hu_cl : ContinuousOn (uPull u p (hr.trans hrR) hsubR) (closedBall p.pt.1 r) :=
    huR_sub.1.mono (closedBall_subset_ball hrR)
  have hu_sph : ContinuousOn (uPull u p (hr.trans hrR) hsubR) (sphere p.pt.1 r) :=
    hu_cl.mono sphere_subset_closedBall
  have hu_sub_r : IsSubharmOnC (uPull u p (hr.trans hrR) hsubR) (ball p.pt.1 r) := by
    refine ⟨huR_sub.1.mono (ball_subset_ball hrR.le), fun z hz => ?_⟩
    obtain ⟨r₀, hr₀, havg⟩ := huR_sub.2 z (ball_subset_ball hrR.le hz)
    exact ⟨r₀, hr₀, fun ρ hρ hρlt hcb => havg ρ hρ hρlt (hcb.trans (ball_subset_ball hrR.le))⟩
  have hv_pullR : ∀ z ∈ ball p.pt.1 R, uPull v p (hr.trans hrR) hsubR z =
      if z ∈ ball p.pt.1 r then poissonInt p.pt.1 r (uPull u p (hr.trans hrR) hsubR) z
      else uPull u p (hr.trans hrR) hsubR z := by
    intro z hz
    rw [uPull_apply v p (hr.trans hrR) hsubR hz, uPull_apply u p (hr.trans hrR) hsubR hz]
    dsimp only [v, poissonModUCov]
    by_cases hzr : z ∈ ball p.pt.1 r
    · rw [if_pos ((uChart_mem_uBall_iff p hr hrR hsubR hz).mpr hzr), if_pos hzr]; rfl
    · rw [if_neg (mt (uChart_mem_uBall_iff p hr hrR hsubR hz).mp hzr), if_neg hzr]
  have hv_pullr : ∀ z ∈ ball p.pt.1 r, uPull v p hr hsubr z =
      poissonInt p.pt.1 r (uPull u p (hr.trans hrR) hsubR) z := by
    intro z hz
    have h1 := uPull_eq_on_sub v (hr.trans hrR) hsubR (mem_uBall_self p (hr.trans hrR) hsubR)
      hr (ball_subset_ball hrR.le) hz
    rw [h1, hv_pullR z (ball_subset_ball hrR.le hz), if_pos hz]
  have hv_ge : ∀ q ∈ U, u q ≤ v q := by
    intro q _
    dsimp only [v, poissonModUCov]
    split_ifs with hq
    · have h1 := IsSubharmOnC.le_poissonInt hr hu_cl hu_sub_r q.pt.1 hq.1
      have huq : uPull u p (hr.trans hrR) hsubR q.pt.1 = u q := by
        rw [uPull_apply u p (hr.trans hrR) hsubR (ball_subset_ball hrR.le hq.1)]
        have hqR := hBrR hq
        rw [← hqR.2]
      rwa [huq] at h1
    · exact le_rfl
  have hv_harm_r : HarmonicOnNhd (uPull v p hr hsubr) (ball p.pt.1 r) := by
    intro z hz
    refine (harmonicAt_congr_nhds ?_).mpr (poissonInt_harmonicOnNhd hr hu_sph z hz)
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hv_pullr w hw
  have hv_cont_R : ContinuousOn (uPull v p (hr.trans hrR) hsubR) (ball p.pt.1 R) := by
    intro z hz
    have hev_z : ∀ w ∈ ball p.pt.1 R, uPull v p (hr.trans hrR) hsubR w =
        if w ∈ ball p.pt.1 r then poissonInt p.pt.1 r (uPull u p (hr.trans hrR) hsubR) w
        else uPull u p (hr.trans hrR) hsubR w := hv_pullR
    rcases lt_trichotomy (dist z p.pt.1) r with hlt | heq | hgt
    · have hzb : z ∈ ball p.pt.1 r := hlt
      have hca : ContinuousAt (poissonInt p.pt.1 r (uPull u p (hr.trans hrR) hsubR)) z :=
        (poissonInt_harmonicOnNhd hr hu_sph z hzb).1.continuousAt
      refine (hca.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
      rw [hev_z w (ball_subset_ball hrR.le hw), if_pos hw]
    · have hzs : z ∈ sphere p.pt.1 r := heq
      have hnot : z ∉ ball p.pt.1 r := by rw [mem_ball]; linarith
      rw [ContinuousWithinAt, hev_z z hz, if_neg hnot, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ₁, hδ₁, h₁⟩ := (Metric.tendsto_nhdsWithin_nhds.mp
        (poissonInt_tendsto_boundary hr hu_sph hzs)) ε hε
      obtain ⟨δ₂, hδ₂, h₂⟩ := (Metric.continuousWithinAt_iff.mp (huR_sub.1 z hz)) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun w hw hwd => ?_⟩
      rw [hev_z w hw]
      by_cases hwb : w ∈ ball p.pt.1 r
      · rw [if_pos hwb]; exact h₁ hwb (lt_of_lt_of_le hwd (min_le_left _ _))
      · rw [if_neg hwb]; exact h₂ hw (lt_of_lt_of_le hwd (min_le_right _ _))
    · have hout : z ∈ ball p.pt.1 R \ closedBall p.pt.1 r := ⟨hz, by rw [mem_closedBall]; linarith⟩
      have hca : ContinuousAt (uPull u p (hr.trans hrR) hsubR) z :=
        huR_sub.1.continuousAt (isOpen_ball.mem_nhds hz)
      refine (hca.congr ?_).continuousWithinAt
      filter_upwards [(isOpen_ball.sdiff isClosed_closedBall).mem_nhds hout] with w hw
      have hnot : w ∉ ball p.pt.1 r := fun hb => hw.2 (ball_subset_closedBall hb)
      rw [hev_z w hw.1, if_neg hnot]
  have hv_sub_R : IsSubharmOnC (uPull v p (hr.trans hrR) hsubR) (ball p.pt.1 R) := by
    refine ⟨hv_cont_R, fun z hz => ?_⟩
    by_cases hzb : z ∈ ball p.pt.1 r
    · have hharm : HarmonicOnNhd (uPull v p (hr.trans hrR) hsubR) (ball p.pt.1 r) := by
        intro w hw
        refine (harmonicAt_congr_nhds ?_).mpr (poissonInt_harmonicOnNhd hr hu_sph w hw)
        filter_upwards [isOpen_ball.mem_nhds hw] with ζ hζ
        rw [hv_pullR ζ (ball_subset_ball hrR.le hζ), if_pos hζ]
      obtain ⟨r₀, hr₀, havg⟩ := (HarmonicOnNhd.isSubharmOnC isOpen_ball hharm).2 z hzb
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp isOpen_ball z hzb
      refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun ρ hρ hρlt _ => ?_⟩
      exact havg ρ hρ (lt_of_lt_of_le hρlt (min_le_left _ _))
        ((closedBall_subset_ball (lt_of_lt_of_le hρlt (min_le_right _ _))).trans hr₁sub)
    · obtain ⟨r₀, hr₀, havg⟩ := huR_sub.2 z hz
      refine ⟨r₀, hr₀, fun ρ hρ hρlt hcb => ?_⟩
      have h1 := havg ρ hρ hρlt hcb
      have hvz : uPull v p (hr.trans hrR) hsubR z = uPull u p (hr.trans hrR) hsubR z := by
        rw [hv_pullR z hz, if_neg hzb]
      rw [hvz]
      have hsp : sphere z |ρ| ⊆ ball p.pt.1 R := by
        rw [abs_of_pos hρ]; exact sphere_subset_closedBall.trans hcb
      refine h1.trans (Real.circleAverage_mono ((huR_sub.1.mono hsp).circleIntegrable')
        ((hv_cont_R.mono hsp).circleIntegrable') fun ζ hζ => ?_)
      have hζR : ζ ∈ ball p.pt.1 R := hsp hζ
      rw [uPull_apply u p (hr.trans hrR) hsubR hζR, uPull_apply v p (hr.trans hrR) hsubR hζR]
      exact hv_ge _ (hBRU (uChart_mem_uBall p (hr.trans hrR) hsubR hζR))
  have hv_sub_U : IsSubharmOnUCov v U := by
    have hcl_closed : IsClosed (uClosedBall p hr hrR hsubR) := isClosed_uClosedBall hΩ p hr hrR hsubR
    have hloc : ∀ q ∈ U, ∃ (ρ : ℝ) (hρ : 0 < ρ) (hsubρ : ball q.pt.1 ρ ⊆ Ω),
        uBall q hρ hsubρ ⊆ U ∧ IsSubharmOnC (uPull v q hρ hsubρ) (ball q.pt.1 ρ) := by
      intro q hqU
      by_cases hqB : q ∈ uBall p (hr.trans hrR) hsubR
      · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball q.pt.1 hqB.1
        have hBsub : uBall q hρ (hρsub.trans hsubR) ⊆ U :=
          (uBall_subset_uBall (hr.trans hrR) hsubR hqB hρ hρsub).trans hBRU
        have heq : Set.EqOn (uPull v q hρ (hρsub.trans hsubR))
            (uPull v p (hr.trans hrR) hsubR) (ball q.pt.1 ρ) :=
          fun z hz => uPull_eq_on_sub v (hr.trans hrR) hsubR hqB hρ hρsub hz
        refine ⟨ρ, hρ, hρsub.trans hsubR, hBsub, (hv_cont_R.mono hρsub).congr fun z hz => heq hz,
          fun z hz => ?_⟩
        obtain ⟨r₀, hr₀, havg⟩ := hv_sub_R.2 z (hρsub hz)
        refine ⟨r₀, hr₀, fun d hd hdlt hcb => ?_⟩
        have h1 := havg d hd hdlt (hcb.trans hρsub)
        rw [← heq hz] at h1
        refine h1.trans_eq (Real.circleAverage_congr_sphere fun ζ hζ => ?_)
        rw [abs_of_pos hd] at hζ
        exact (heq (hcb (sphere_subset_closedBall hζ))).symm
      · have hq_out : q ∈ U \ uClosedBall p hr hrR hsubR := ⟨hqU, fun h => hqB h.1⟩
        have hopen_out : IsOpen (U \ uClosedBall p hr hrR hsubR) := hUo.sdiff hcl_closed
        obtain ⟨S, ⟨q', r', hr', hsub', rfl⟩, hqS, hSout⟩ :=
          (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hopen_out q hq_out
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball q.pt.1 hqS.1
        have hBsub_out : uBall q hρ (hρsub.trans hsub') ⊆ U \ uClosedBall p hr hrR hsubR :=
          (uBall_subset_uBall hr' hsub' hqS hρ hρsub).trans hSout
        have hBsub_U : uBall q hρ (hρsub.trans hsub') ⊆ U := hBsub_out.trans sdiff_subset
        have hv_eq_u : ∀ x ∈ uBall q hρ (hρsub.trans hsub'), v x = u x := by
          intro x hx
          dsimp only [v, poissonModUCov]
          refine if_neg fun hxbr => (hBsub_out hx).2 ⟨hBrR hxbr, ball_subset_closedBall hxbr.1⟩
        have heq : Set.EqOn (uPull v q hρ (hρsub.trans hsub'))
            (uPull u q hρ (hρsub.trans hsub')) (ball q.pt.1 ρ) := fun z hz => by
          rw [uPull_apply v q hρ _ hz, uPull_apply u q hρ _ hz]
          exact hv_eq_u _ (uChart_mem_uBall q hρ _ hz)
        have hu_sub_q := hu.2 q ρ hρ (hρsub.trans hsub') hBsub_U
        refine ⟨ρ, hρ, hρsub.trans hsub', hBsub_U, hu_sub_q.1.congr fun z hz => heq hz,
          fun z hz => ?_⟩
        obtain ⟨r₀, hr₀, havg⟩ := hu_sub_q.2 z hz
        refine ⟨r₀, hr₀, fun d hd hdlt hcb => ?_⟩
        have h1 := havg d hd hdlt hcb
        rw [← heq hz] at h1
        refine h1.trans_eq (Real.circleAverage_congr_sphere fun ζ hζ => ?_)
        rw [abs_of_pos hd] at hζ
        exact (heq (hcb (sphere_subset_closedBall hζ))).symm
    have hv_cont_U : ContinuousOn v U := continuousOn_of_uPull hΩ fun q hq => by
      obtain ⟨ρ, hρ, hsubρ, hBU, hs⟩ := hloc q hq
      exact ⟨ρ, hρ, hsubρ, hBU, hs.1⟩
    exact isSubharmOnUCov_of_local hΩ hv_cont_U hloc
  refine ⟨hv_ge, hv_sub_U, hv_harm_r, fun q hq => by simp only [v, poissonModUCov, if_neg hq], ?_⟩
  intro hle0 q hqU
  dsimp only [v, poissonModUCov]
  split_ifs with hq
  · have h1 := poissonInt_mono hr hq.1 (g₂ := fun _ => 0) hu_sph continuousOn_const fun ζ hζ => by
      have hζR : ζ ∈ ball p.pt.1 R := closedBall_subset_ball hrR (sphere_subset_closedBall hζ)
      rw [uPull_apply u p (hr.trans hrR) hsubR hζR]
      exact hle0 _ (hBRU (uChart_mem_uBall p (hr.trans hrR) hsubR hζR))
    rwa [poissonInt_const hr hq.1] at h1
  · exact hle0 q hqU

/- ### Part 5B: Disk automorphisms, Perron family, and Green's function on `UCov Ω w₀` -/

private def diskMob (b w : ℂ) : ℂ := (w - b) / (1 - starRingEnd ℂ b * w)

private lemma diskMob_denom_ne_zero {b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    1 - starRingEnd ℂ b * w ≠ 0 := by
  intro h
  have h1 : starRingEnd ℂ b * w = 1 := by linear_combination -h
  have h2 : ‖starRingEnd ℂ b * w‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, Complex.norm_conj] at h2
  nlinarith [norm_nonneg b, norm_nonneg w]

private lemma norm_diskMob_lt_one {b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    ‖diskMob b w‖ < 1 := by
  have hden := diskMob_denom_ne_zero hb hw
  have hden_pos : 0 < ‖1 - starRingEnd ℂ b * w‖ := norm_pos_iff.mpr hden
  rw [diskMob, norm_div, div_lt_one hden_pos]
  have hsq : ‖w - b‖ ^ 2 < ‖1 - starRingEnd ℂ b * w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    have hdiff : Complex.normSq (1 - starRingEnd ℂ b * w) - Complex.normSq (w - b) =
        (1 - Complex.normSq b) * (1 - Complex.normSq w) := by
      simp only [Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, Complex.conj_re,
        Complex.conj_im, Complex.one_re, Complex.one_im]
      ring
    have hb2 : Complex.normSq b < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg b]
    have hw2 : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    nlinarith
  nlinarith [norm_nonneg (w - b), norm_nonneg (1 - starRingEnd ℂ b * w)]

private lemma diskMob_self {b : ℂ} : diskMob b b = 0 := by
  simp [diskMob]

private lemma diskMob_zero (w : ℂ) : diskMob 0 w = w := by
  simp [diskMob]

private lemma norm_diskMob_zero (b : ℂ) : ‖diskMob b 0‖ = ‖b‖ := by
  simp [diskMob]

private lemma diskMob_eq_zero_iff {b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    diskMob b w = 0 ↔ w = b := by
  rw [diskMob, div_eq_zero_iff]
  simp [diskMob_denom_ne_zero hb hw, sub_eq_zero]

private lemma hasDerivAt_diskMob {b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    HasDerivAt (diskMob b) (((1 - ‖b‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ b * w) ^ 2) w := by
  have hden := diskMob_denom_ne_zero hb hw
  have h1 : HasDerivAt (fun z : ℂ => z - b) 1 w := (hasDerivAt_id w).sub_const b
  have h2 : HasDerivAt (fun z : ℂ => 1 - starRingEnd ℂ b * z) (-starRingEnd ℂ b) w := by
    have hmul : HasDerivAt (fun z : ℂ => starRingEnd ℂ b * z) (starRingEnd ℂ b) w := by
      simpa using (hasDerivAt_id w).const_mul (starRingEnd ℂ b)
    simpa using (hasDerivAt_const w (1 : ℂ)).fun_sub hmul
  refine (h1.div h2 hden).congr_deriv ?_
  have hbb : starRingEnd ℂ b * b = ((‖b‖ : ℂ) ^ 2) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; rfl
  push_cast
  rw [← hbb]
  ring

private lemma IsHoloOnUCov.comp_diskMob {Ω : Set ℂ} {w₀ : Ω} {F : UCov Ω w₀ → ℂ}
    (hF : IsHoloOnUCov F) (hFlt : ∀ p, ‖F p‖ < 1) {b : ℂ} (hb : ‖b‖ < 1) :
    IsHoloOnUCov (fun p => diskMob b (F p)) := by
  intro p r hr hsub z hz
  have hFd : DifferentiableAt ℂ (uPull F p hr hsub) z :=
    (hF p r hr hsub).differentiableAt (isOpen_ball.mem_nhds hz)
  have hFzb : ‖uPull F p hr hsub z‖ < 1 := by
    rw [uPull_apply F p hr hsub hz]; exact hFlt _
  have hmob : DifferentiableAt ℂ (diskMob b) (uPull F p hr hsub z) :=
    (hasDerivAt_diskMob hb hFzb).differentiableAt
  have hcomp : DifferentiableAt ℂ (fun w => diskMob b (uPull F p hr hsub w)) z :=
    hmob.comp z hFd
  refine (hcomp.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  change uPull (fun q => diskMob b (F q)) p hr hsub w = diskMob b (uPull F p hr hsub w)
  rw [uPull_apply _ p hr hsub hw, uPull_apply F p hr hsub hw]

private def PerronFam {Ω : Set ℂ} {w₀ : Ω} (a : UCov Ω w₀) : Set (UCov Ω w₀ → ℝ) :=
  {u | IsSubharmOnUCov u {a}ᶜ ∧ (∀ p ≠ a, u p ≤ 0) ∧
    ∃ (r : ℝ) (hr : 0 < r) (hsub : ball a.pt.1 r ⊆ Ω) (C : ℝ),
      ∀ z (hz : z ∈ ball a.pt.1 r), z ≠ a.pt.1 →
        u (uChart a hr hsub z hz) ≤ Real.log ‖z - a.pt.1‖ + C}

private def greenFn {Ω : Set ℂ} {w₀ : Ω} (a : UCov Ω w₀) (p : UCov Ω w₀) : ℝ :=
  sSup {x : ℝ | ∃ u ∈ PerronFam a, u p = x}

private lemma perron_sup {Ω : Set ℂ} {w₀ : Ω} {a : UCov Ω w₀}
    {u v : UCov Ω w₀ → ℝ} (hu : u ∈ PerronFam a) (hv : v ∈ PerronFam a) :
    (fun p => max (u p) (v p)) ∈ PerronFam a := by
  refine ⟨IsSubharmOnUCov.sup hu.1 hv.1, fun p hp => max_le (hu.2.1 p hp) (hv.2.1 p hp), ?_⟩
  obtain ⟨r₁, hr₁, hsub₁, C₁, hC₁⟩ := hu.2.2
  obtain ⟨r₂, hr₂, hsub₂, C₂, hC₂⟩ := hv.2.2
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsub : ball a.pt.1 r ⊆ Ω := (ball_subset_ball (min_le_left _ _)).trans hsub₁
  refine ⟨r, hr, hsub, max C₁ C₂, fun z hz hzne => ?_⟩
  have hz1 : z ∈ ball a.pt.1 r₁ := ball_subset_ball (min_le_left _ _) hz
  have hz2 : z ∈ ball a.pt.1 r₂ := ball_subset_ball (min_le_right _ _) hz
  have heq1 : uChart a hr hsub z hz = uChart a hr₁ hsub₁ z hz1 :=
    uChart_eq_uChart hr₁ hsub₁ (mem_ball_self hr₁) (uChart_self a hr₁ hsub₁).symm
      hr (ball_subset_ball (min_le_left _ _)) hz
  have heq2 : uChart a hr hsub z hz = uChart a hr₂ hsub₂ z hz2 :=
    uChart_eq_uChart hr₂ hsub₂ (mem_ball_self hr₂) (uChart_self a hr₂ hsub₂).symm
      hr (ball_subset_ball (min_le_right _ _)) hz
  exact max_le
    ((heq1 ▸ hC₁ z hz1 hzne).trans (by linarith [le_max_left C₁ C₂]))
    ((heq2 ▸ hC₂ z hz2 hzne).trans (by linarith [le_max_right C₁ C₂]))

private lemma perron_poissonMod {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω} {a : UCov Ω w₀}
    {u : UCov Ω w₀ → ℝ} (hu : u ∈ PerronFam a)
    (p : UCov Ω w₀) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsubR : ball p.pt.1 R ⊆ Ω)
    (hBR_ne : uBall p (hr.trans hrR) hsubR ⊆ {a}ᶜ) :
    poissonModUCov u p hr hrR hsubR ∈ PerronFam a := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
  have hspec := poissonModUCov_spec hΩ hUo hu.1 p hr hrR hsubR hBR_ne
  refine ⟨hspec.2.1, hspec.2.2.2.2 hu.2.1, ?_⟩
  have hcl_closed : IsClosed (uClosedBall p hr hrR hsubR) := isClosed_uClosedBall hΩ p hr hrR hsubR
  have ha_not_cl : a ∉ uClosedBall p hr hrR hsubR := fun h => hBR_ne h.1 rfl
  obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, haS, hSdisj⟩ :=
    (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hcl_closed.isOpen_compl a ha_not_cl
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp isOpen_ball a.pt.1 haS.1
  have hB₀_disj : uBall a hr₀ (hr₀sub.trans hsubq) ⊆ (uClosedBall p hr hrR hsubR)ᶜ :=
    (uBall_subset_uBall hrq hsubq haS hr₀ hr₀sub).trans hSdisj
  obtain ⟨r₁, hr₁, hsub₁, C, hC⟩ := hu.2.2
  let ρ := min r₀ r₁
  have hρ : 0 < ρ := lt_min hr₀ hr₁
  have hsubρ : ball a.pt.1 ρ ⊆ Ω := (ball_subset_ball (min_le_right _ _)).trans hsub₁
  refine ⟨ρ, hρ, hsubρ, C, fun z hz hzne => ?_⟩
  have hz0 : z ∈ ball a.pt.1 r₀ := ball_subset_ball (min_le_left _ _) hz
  have hz1 : z ∈ ball a.pt.1 r₁ := ball_subset_ball (min_le_right _ _) hz
  have hmem0 : uChart a hρ hsubρ z hz ∈ uBall a hr₀ (hr₀sub.trans hsubq) := by
    have heq := uChart_eq_uChart hr₀ (hr₀sub.trans hsubq) (mem_ball_self hr₀)
      (uChart_self a hr₀ _).symm hρ (ball_subset_ball (min_le_left _ _)) hz
    rw [heq]; exact uChart_mem_uBall a hr₀ _ hz0
  have hnotB : uChart a hρ hsubρ z hz ∉ uBall p hr ((ball_subset_ball hrR.le).trans hsubR) := by
    intro hmem
    have hBrR : uBall p hr ((ball_subset_ball hrR.le).trans hsubR) ⊆ uBall p (hr.trans hrR) hsubR :=
      uBall_subset_uBall (hr.trans hrR) hsubR (mem_uBall_self p (hr.trans hrR) hsubR) hr
        (ball_subset_ball hrR.le)
    exact hB₀_disj hmem0 ⟨hBrR hmem, ball_subset_closedBall hmem.1⟩
  rw [hspec.2.2.2.1 _ hnotB]
  have heq1 : uChart a hρ hsubρ z hz = uChart a hr₁ hsub₁ z hz1 :=
    uChart_eq_uChart hr₁ hsub₁ (mem_ball_self hr₁) (uChart_self a hr₁ hsub₁).symm
      hρ (ball_subset_ball (min_le_right _ _)) hz
  rw [heq1]
  exact hC z hz1 hzne

private lemma uPull_isSubharmOnC_punctured {Ω : Set ℂ} {w₀ : Ω}
    {a : UCov Ω w₀} {R : ℝ} (hR : 0 < R) (hsubR : ball a.pt.1 R ⊆ Ω)
    {u : UCov Ω w₀ → ℝ} (hu : IsSubharmOnUCov u {a}ᶜ) :
    IsSubharmOnC (uPull u a hR hsubR) (ball a.pt.1 R \ {a.pt.1}) := by
  have hloc : ∀ z ∈ ball a.pt.1 R \ {a.pt.1},
      ∃ ρ > 0, ball z ρ ⊆ ball a.pt.1 R \ {a.pt.1} ∧
        IsSubharmOnC (uPull u a hR hsubR) (ball z ρ) := by
    intro z ⟨hzR, hzne⟩
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.sdiff isClosed_singleton) z ⟨hzR, hzne⟩
    let q := uChart a hR hsubR z hzR
    have hqB : q ∈ uBall a hR hsubR := uChart_mem_uBall a hR hsubR hzR
    have hρsubR : ball q.pt.1 ρ ⊆ ball a.pt.1 R := hρsub.trans sdiff_subset
    have hBq_ne : uBall q hρ (hρsubR.trans hsubR) ⊆ {a}ᶜ := by
      intro x hx hxa
      have h1 : a.pt.1 ∈ ball z ρ := hxa ▸ hx.1
      exact (hρsub h1).2 rfl
    have hsq := hu.2 q ρ hρ (hρsubR.trans hsubR) hBq_ne
    have heq : Set.EqOn (uPull u q hρ (hρsubR.trans hsubR)) (uPull u a hR hsubR) (ball z ρ) :=
      fun w hw => uPull_eq_on_sub u hR hsubR hqB hρ hρsubR hw
    refine ⟨ρ, hρ, hρsub, hsq.1.congr fun w hw => (heq hw).symm, fun w hw => ?_⟩
    obtain ⟨r₀, hr₀, havg⟩ := hsq.2 w hw
    refine ⟨r₀, hr₀, fun d hd hdlt hcb => ?_⟩
    have h1 := havg d hd hdlt hcb
    rw [heq hw] at h1
    refine h1.trans_eq (Real.circleAverage_congr_sphere fun ζ hζ => ?_)
    rw [abs_of_pos hd] at hζ
    exact heq (hcb (sphere_subset_closedBall hζ))
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨ρ, hρ, _, hsz⟩ := hloc z hz
    exact (hsz.1.continuousAt (ball_mem_nhds z hρ)).continuousWithinAt
  · obtain ⟨ρ, hρ, _, hsz⟩ := hloc z hz
    obtain ⟨r₀, hr₀, havg⟩ := hsz.2 z (mem_ball_self hρ)
    refine ⟨min ρ r₀, lt_min hρ hr₀, fun d hd hdlt _ => ?_⟩
    exact havg d hd (lt_of_lt_of_le hdlt (min_le_right _ _))
      (closedBall_subset_ball (lt_of_lt_of_le hdlt (min_le_left _ _)))

private lemma uPull_harmonicOnNhd_punctured {Ω : Set ℂ} {w₀ : Ω}
    {a : UCov Ω w₀} {R : ℝ} (hR : 0 < R) (hsubR : ball a.pt.1 R ⊆ Ω)
    {u : UCov Ω w₀ → ℝ} (hu : IsHarmOnUCov u {a}ᶜ) :
    HarmonicOnNhd (uPull u a hR hsubR) (ball a.pt.1 R \ {a.pt.1}) := by
  intro z ⟨hzR, hzne⟩
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.sdiff isClosed_singleton) z ⟨hzR, hzne⟩
  let q := uChart a hR hsubR z hzR
  have hqB : q ∈ uBall a hR hsubR := uChart_mem_uBall a hR hsubR hzR
  have hρsubR : ball q.pt.1 ρ ⊆ ball a.pt.1 R := hρsub.trans sdiff_subset
  have hBq_ne : uBall q hρ (hρsubR.trans hsubR) ⊆ {a}ᶜ := by
    intro x hx hxa
    have h1 : a.pt.1 ∈ ball z ρ := hxa ▸ hx.1
    exact (hρsub h1).2 rfl
  have hhq := hu q ρ hρ (hρsubR.trans hsubR) hBq_ne z (mem_ball_self hρ)
  refine (harmonicAt_congr_nhds ?_).mp hhq
  filter_upwards [ball_mem_nhds z hρ] with w hw
  exact uPull_eq_on_sub u hR hsubR hqB hρ hρsubR hw

private lemma perron_universal_bound {Ω : Set ℂ} {w₀ : Ω}
    {a : UCov Ω w₀} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsubR : ball a.pt.1 R ⊆ Ω)
    {u : UCov Ω w₀ → ℝ} (hu : u ∈ PerronFam a)
    {z : ℂ} (hz : z ∈ ball a.pt.1 r) (hzne : z ≠ a.pt.1) :
    u (uChart a (hr.trans hrR) hsubR z (ball_subset_ball hrR.le hz)) ≤
      Real.log ‖z - a.pt.1‖ - Real.log r := by
  have hz_pos : 0 < ‖z - a.pt.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  have hz_lt : ‖z - a.pt.1‖ < r := mem_ball_iff_norm.mp hz
  by_contra hgt
  push Not at hgt
  let Δ : ℝ := u (uChart a (hr.trans hrR) hsubR z (ball_subset_ball hrR.le hz)) -
    (Real.log ‖z - a.pt.1‖ - Real.log r)
  have hΔ : 0 < Δ := sub_pos.mpr hgt
  have hMz_pos : 0 < Real.log r - Real.log ‖z - a.pt.1‖ :=
    sub_pos.mpr (Real.log_lt_log hz_pos hz_lt)
  let ε : ℝ := min (1 / 2) (Δ / (2 * (Real.log r - Real.log ‖z - a.pt.1‖)))
  have hε_pos : 0 < ε := lt_min (by norm_num) (div_pos hΔ (by positivity))
  have hε_le_half : ε ≤ 1 / 2 := min_le_left _ _
  have hε_lt1 : ε < 1 := lt_of_le_of_lt hε_le_half (by norm_num)
  obtain ⟨r₁, hr₁, hsub₁, C, hC⟩ := hu.2.2
  let δ : ℝ := min (‖z - a.pt.1‖ / 2) (min (r / 2) (min (r₁ / 2)
    (Real.exp (-((|C| + |Real.log r| + 1) / ε)))))
  have hδ_pos : 0 < δ := lt_min (half_pos hz_pos)
    (lt_min (half_pos hr) (lt_min (half_pos hr₁) (Real.exp_pos _)))
  have hδ_lt_z : δ < ‖z - a.pt.1‖ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hz_pos)
  have hδ_lt_r : δ < r := hδ_lt_z.trans hz_lt
  have hδ_lt_r1 : δ < r₁ :=
    lt_of_le_of_lt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      (half_lt_self hr₁)
  let A : Set ℂ := ball a.pt.1 r \ closedBall a.pt.1 δ
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAb : Bornology.IsBounded A := isBounded_ball.subset sdiff_subset
  have hAcl_sub : closure A ⊆ closedBall a.pt.1 r \ ball a.pt.1 δ := by
    refine subset_inter ?_ ?_
    · exact (closure_mono sdiff_subset).trans (by rw [closure_ball a.pt.1 hr.ne'])
    · exact closure_minimal (fun w hw hwb => hw.2 (ball_subset_closedBall hwb))
        isOpen_ball.isClosed_compl
  have hAfr_sub : frontier A ⊆ sphere a.pt.1 r ∪ sphere a.pt.1 δ := by
    intro w ⟨hw_cl, hw_not⟩
    rw [hAo.interior_eq] at hw_not
    have h1 := hAcl_sub hw_cl
    have hle_r : dist w a.pt.1 ≤ r := mem_closedBall.mp h1.1
    have hge_δ : δ ≤ dist w a.pt.1 := not_lt.mp h1.2
    by_cases hlt_r : dist w a.pt.1 < r
    · right
      have hle_δ : dist w a.pt.1 ≤ δ := by by_contra hgt'; exact hw_not ⟨hlt_r, hgt'⟩
      exact le_antisymm hle_δ hge_δ
    · left; exact le_antisymm hle_r (not_lt.mp hlt_r)
  have hcl_sub_R : closedBall a.pt.1 r \ ball a.pt.1 δ ⊆ ball a.pt.1 R \ {a.pt.1} := by
    intro w ⟨hw1, hw2⟩
    refine ⟨closedBall_subset_ball hrR hw1, ?_⟩
    intro heq; apply hw2; rw [heq]; exact mem_ball_self hδ_pos
  have hu_punc := uPull_isSubharmOnC_punctured (hr.trans hrR) hsubR hu.1
  have hA_sub_punc : A ⊆ ball a.pt.1 R \ {a.pt.1} :=
    subset_closure.trans (hAcl_sub.trans hcl_sub_R)
  have huA_sub : IsSubharmOnC (uPull u a (hr.trans hrR) hsubR) A := by
    refine ⟨hu_punc.1.mono hA_sub_punc, fun w hw => ?_⟩
    obtain ⟨r₀, hr₀, havg⟩ := hu_punc.2 w (hA_sub_punc hw)
    exact ⟨r₀, hr₀, fun d hd hdlt hcb => havg d hd hdlt (hcb.trans hA_sub_punc)⟩
  let g : ℂ → ℝ := fun w => -(1 - ε) * (Real.log ‖w - a.pt.1‖ - Real.log r)
  have hg_harm : HarmonicOnNhd g A := by
    intro w hw
    have hwn : w ≠ a.pt.1 := (hA_sub_punc hw).2
    have h1 : HarmonicAt ((-(1 - ε)) • ((fun x => Real.log ‖x - a.pt.1‖) - fun _ => Real.log r)) w :=
      ((log_norm_harmonicAt hwn).sub (harmonicAt_const (Real.log r))).const_smul
    convert h1 using 1
    ext x; simp [g]
  let v : ℂ → ℝ := fun w => uPull u a (hr.trans hrR) hsubR w + g w
  have hv_sub : IsSubharmOnC v A := huA_sub.add (HarmonicOnNhd.isSubharmOnC hAo hg_harm)
  have hv_cont : ContinuousOn v (closure A) := by
    have hlog_cl : ContinuousOn (fun w => Real.log ‖w - a.pt.1‖) (closure A) := by
      refine Real.continuousOn_log.comp
        (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn fun w hw => ?_
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hcl_sub_R (hAcl_sub hw)).2)
    exact (hu_punc.1.mono (hAcl_sub.trans hcl_sub_R)).add
      (continuousOn_const.mul (hlog_cl.sub continuousOn_const))
  have hv_bd : ∀ w ∈ frontier A, v w ≤ 0 := by
    intro w hw
    have hwp := hcl_sub_R (hAcl_sub hw.1)
    rcases hAfr_sub hw with hwr | hwδ
    · have hwn : ‖w - a.pt.1‖ = r := mem_sphere_iff_norm.mp hwr
      dsimp only [v, g]
      rw [uPull_apply u a (hr.trans hrR) hsubR hwp.1, hwn, sub_self, mul_zero, add_zero]
      exact hu.2.1 _ fun heq => hwp.2 (congr_arg uProjC heq)
    · have hwn : ‖w - a.pt.1‖ = δ := mem_sphere_iff_norm.mp hwδ
      have hw_r1 : w ∈ ball a.pt.1 r₁ := mem_ball_iff_norm.mpr (by linarith)
      have hchart_eq : uChart a (hr.trans hrR) hsubR w hwp.1 = uChart a hr₁ hsub₁ w hw_r1 := by
        let ρm := min R r₁
        have hρm : 0 < ρm := lt_min (hr.trans hrR) hr₁
        have hw_m : w ∈ ball a.pt.1 ρm := mem_ball_iff_norm.mpr (lt_min (by linarith) (by linarith))
        have h1 := uChart_eq_uChart (hr.trans hrR) hsubR (mem_ball_self (hr.trans hrR))
          (uChart_self a (hr.trans hrR) hsubR).symm hρm (ball_subset_ball (min_le_left _ _)) hw_m
        have h2 := uChart_eq_uChart hr₁ hsub₁ (mem_ball_self hr₁)
          (uChart_self a hr₁ hsub₁).symm hρm (ball_subset_ball (min_le_right _ _)) hw_m
        exact h1.symm.trans h2
      have huw : uPull u a (hr.trans hrR) hsubR w ≤ Real.log δ + C := by
        rw [uPull_apply u a (hr.trans hrR) hsubR hwp.1, hchart_eq, ← hwn]
        exact hC w hw_r1 hwp.2
      have hδ_le : δ ≤ Real.exp (-((|C| + |Real.log r| + 1) / ε)) :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      have hlogδ : Real.log δ ≤ -((|C| + |Real.log r| + 1) / ε) := by
        have := Real.log_le_log hδ_pos hδ_le
        rwa [Real.log_exp] at this
      have hεlog : ε * Real.log δ ≤ -(|C| + |Real.log r| + 1) := by
        have := mul_le_mul_of_nonneg_left hlogδ hε_pos.le
        rwa [mul_neg, mul_div_cancel₀ _ hε_pos.ne'] at this
      have hC_le : C ≤ |C| := le_abs_self C
      have hlogr_le : (1 - ε) * Real.log r ≤ |Real.log r| := by
        have h1 : |(1 - ε) * Real.log r| = (1 - ε) * |Real.log r| := by
          rw [abs_mul, abs_of_pos (sub_pos.mpr hε_lt1)]
        have h2 : (1 - ε) * |Real.log r| ≤ |Real.log r| := by nlinarith [abs_nonneg (Real.log r)]
        exact (le_abs_self _).trans (h1 ▸ h2)
      dsimp only [v, g]
      rw [hwn]
      nlinarith
  have hzA : z ∈ A := ⟨hz, by rw [mem_closedBall_iff_norm]; linarith⟩
  have hvz := IsSubharmOnC.max_principle_bounded hAo hAb hv_cont hv_sub hv_bd z (subset_closure hzA)
  dsimp only [v, g] at hvz
  rw [uPull_apply u a (hr.trans hrR) hsubR (ball_subset_ball hrR.le hz)] at hvz
  have hεMz : ε * (Real.log r - Real.log ‖z - a.pt.1‖) ≤ Δ / 2 := by
    have hle : ε ≤ Δ / (2 * (Real.log r - Real.log ‖z - a.pt.1‖)) := min_le_right _ _
    have := mul_le_mul_of_nonneg_right hle hMz_pos.le
    have heq : Δ / (2 * (Real.log r - Real.log ‖z - a.pt.1‖)) * (Real.log r - Real.log ‖z - a.pt.1‖) =
        Δ / 2 := by field_simp [hMz_pos.ne']
    linarith
  dsimp only [Δ] at hεMz
  linarith

private lemma perron_nonempty_and_lower {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) (a : UCov Ω w₀) :
    ∃ (u₀ : UCov Ω w₀ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hsubρ : ball a.pt.1 ρ ⊆ Ω) (c₁ : ℝ),
      u₀ ∈ PerronFam a ∧
      ∀ z (hz : z ∈ ball a.pt.1 ρ), z ≠ a.pt.1 →
        Real.log ‖z - a.pt.1‖ + c₁ ≤ u₀ (uChart a hρ hsubρ z hz) := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  obtain ⟨Φ, hΦ_holo, hΦ_lt, hΦ_deriv⟩ := exists_bounded_holo_UCov hΩ hΩc hΩP w₀
  let Ψ : UCov Ω w₀ → ℂ := fun p => diskMob (Φ a) (Φ p)
  have hΨ_holo : IsHoloOnUCov Ψ := hΦ_holo.comp_diskMob hΦ_lt (hΦ_lt a)
  have hΨ_lt : ∀ p, ‖Ψ p‖ < 1 := fun p => norm_diskMob_lt_one (hΦ_lt a) (hΦ_lt p)
  have hΨ_a : Ψ a = 0 := diskMob_self
  obtain ⟨R, hR, hsubR⟩ := Metric.isOpen_iff.mp hΩ a.pt.1 a.pt.2
  let f : ℂ → ℂ := uPull Ψ a hR hsubR
  have hf_diff : DifferentiableOn ℂ f (ball a.pt.1 R) := hΨ_holo a R hR hsubR
  have hf_a : f a.pt.1 = 0 := by dsimp only [f]; rw [uPull_self, hΨ_a]
  have hf_deriv_ne : deriv f a.pt.1 ≠ 0 := by
    have hΦa_d : HasDerivAt (uPull Φ a hR hsubR) (deriv (uPull Φ a hR hsubR) a.pt.1) a.pt.1 :=
      ((hΦ_holo a R hR hsubR).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
    have hmob_d := hasDerivAt_diskMob (b := Φ a) (w := Φ a) (hΦ_lt a) (hΦ_lt a)
    have hmob_d' : HasDerivAt (diskMob (Φ a))
        (((1 - ‖Φ a‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ (Φ a) * Φ a) ^ 2)
        (uPull Φ a hR hsubR a.pt.1) := by
      rwa [uPull_self]
    have hcomp : HasDerivAt (fun w => diskMob (Φ a) (uPull Φ a hR hsubR w))
        ((((1 - ‖Φ a‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ (Φ a) * Φ a) ^ 2) *
          deriv (uPull Φ a hR hsubR) a.pt.1) a.pt.1 :=
      (hmob_d'.comp a.pt.1 hΦa_d) |> fun h => by simpa [Function.comp_def] using h
    have hev : (fun w => diskMob (Φ a) (uPull Φ a hR hsubR w)) =ᶠ[𝓝 a.pt.1] f := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with w hw
      change diskMob (Φ a) (uPull Φ a hR hsubR w) = uPull Ψ a hR hsubR w
      rw [uPull_apply Φ a hR hsubR hw, uPull_apply Ψ a hR hsubR hw]
    rw [(hcomp.congr_of_eventuallyEq hev.symm).deriv]
    have hnum_ne : ((1 - ‖Φ a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : ‖Φ a‖ < 1 := hΦ_lt a
      exact Complex.ofReal_ne_zero.mpr (by nlinarith [norm_nonneg (Φ a)])
    exact mul_ne_zero (div_ne_zero hnum_ne (pow_ne_zero 2 (diskMob_denom_ne_zero (hΦ_lt a) (hΦ_lt a))))
      (hΦ_deriv a R hR hsubR)
  let d : ℂ := deriv f a.pt.1
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hf_deriv_ne
  have hfd : HasDerivAt f d a.pt.1 :=
    (hf_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
  have hlo := hasDerivAt_iff_isLittleO.mp hfd
  have hev_lin : ∀ᶠ z in 𝓝 a.pt.1, ‖f z - f a.pt.1 - (z - a.pt.1) • d‖ ≤ (‖d‖ / 2) * ‖z - a.pt.1‖ :=
    hlo.bound (half_pos hd_pos)
  obtain ⟨ρ₀, hρ₀, hρ₀_bound⟩ := Metric.eventually_nhds_iff_ball.mp hev_lin
  let ρ : ℝ := min (R / 2) ρ₀
  have hρ : 0 < ρ := lt_min (half_pos hR) hρ₀
  have hρR : ρ < R := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hR)
  have hsubρ : ball a.pt.1 ρ ⊆ Ω := (ball_subset_ball hρR.le).trans hsubR
  have hf_bounds : ∀ z ∈ ball a.pt.1 ρ,
      (‖d‖ / 2) * ‖z - a.pt.1‖ ≤ ‖f z‖ ∧ ‖f z‖ ≤ (3 * ‖d‖ / 2) * ‖z - a.pt.1‖ := by
    intro z hz
    have h1 := hρ₀_bound z (ball_subset_ball (min_le_right _ _) hz)
    rw [hf_a, sub_zero, smul_eq_mul] at h1
    have hnorm_d : ‖(z - a.pt.1) * d‖ = ‖d‖ * ‖z - a.pt.1‖ := by rw [norm_mul, mul_comm]
    have hlow := norm_sub_norm_le ((z - a.pt.1) * d) (f z)
    rw [norm_sub_rev] at hlow
    have hup := norm_sub_norm_le (f z) ((z - a.pt.1) * d)
    constructor <;> linarith
  let M : ℝ := min (Real.log ((‖d‖ / 2) * (ρ / 2)) - 1) (-1)
  have hM_neg : M < 0 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hexpM_lt : Real.exp M < (‖d‖ / 2) * (ρ / 2) := by
    have h1 : M < Real.log ((‖d‖ / 2) * (ρ / 2)) :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    calc Real.exp M < Real.exp (Real.log ((‖d‖ / 2) * (ρ / 2))) := Real.exp_lt_exp.mpr h1
      _ = (‖d‖ / 2) * (ρ / 2) := Real.exp_log (by positivity)
  open Classical in
  let u₀ : UCov Ω w₀ → ℝ := fun p =>
    if p ∈ uBall a hρ hsubρ then Real.log ‖Ψ p‖
    else Real.log (max ‖Ψ p‖ (Real.exp M))
  have hρ2_pos : 0 < ρ / 2 := half_pos hρ
  have hρ2_lt : ρ / 2 < R := lt_trans (half_lt_self hρ) hρR
  let K : Set (UCov Ω w₀) := uClosedBall a hρ2_pos hρ2_lt hsubR
  have hK_closed : IsClosed K := isClosed_uClosedBall hΩ a hρ2_pos hρ2_lt hsubR
  have hu₀_eq_out : ∀ p ∈ ({a}ᶜ : Set (UCov Ω w₀)) \ K,
      u₀ p = Real.log (max ‖Ψ p‖ (Real.exp M)) := by
    intro p ⟨_, hpK⟩
    dsimp only [u₀]
    split_ifs with hpB
    · have hpR : p ∈ uBall a hR hsubR :=
        uBall_subset_uBall hR hsubR (mem_uBall_self a hR hsubR) hρ (ball_subset_ball hρR.le) hpB
      have hge : ρ / 2 < ‖p.pt.1 - a.pt.1‖ := by
        by_contra hle
        push Not at hle
        exact hpK ⟨hpR, mem_closedBall_iff_norm.mpr hle⟩
      have hfp : f p.pt.1 = Ψ p := by
        dsimp only [f]
        rw [uPull_apply Ψ a hR hsubR hpR.1, ← hpR.2]
      have hΨ_gt : Real.exp M < ‖Ψ p‖ := by
        rw [← hfp]
        have h1 := (hf_bounds p.pt.1 hpB.1).1
        have h2 : (‖d‖ / 2) * (ρ / 2) < (‖d‖ / 2) * ‖p.pt.1 - a.pt.1‖ :=
          mul_lt_mul_of_pos_left hge (half_pos hd_pos)
        linarith
      rw [max_eq_left hΨ_gt.le]
    · rfl
  have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
  have hu₀_sub_loc : ∀ p ∈ ({a}ᶜ : Set (UCov Ω w₀)),
      ∃ (r' : ℝ) (hr' : 0 < r') (hsub' : ball p.pt.1 r' ⊆ Ω),
        uBall p hr' hsub' ⊆ {a}ᶜ ∧ IsSubharmOnC (uPull u₀ p hr' hsub') (ball p.pt.1 r') := by
    intro p hpne
    by_cases hpK : p ∈ K
    · have hpρ : p.pt.1 ∈ ball a.pt.1 ρ :=
        mem_ball_iff_norm.mpr (lt_of_le_of_lt (mem_closedBall_iff_norm.mp hpK.2) (half_lt_self hρ))
      have hpBρ : p ∈ uBall a hρ hsubρ := by
        refine ⟨hpρ, ?_⟩
        exact (uChart_eq_uChart hR hsubR (mem_ball_self hR) (uChart_self a hR hsubR).symm
          hρ (ball_subset_ball hρR.le) hpρ).symm.trans hpK.1.2.symm |>.symm
      have hp_neC : p.pt.1 ≠ a.pt.1 := fun h =>
        hpne (uBall_injOn_uProjC a hρ hsubρ hpBρ (mem_uBall_self a hρ hsubρ) h)
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp (isOpen_ball.sdiff isClosed_singleton) p.pt.1 ⟨hpρ, hp_neC⟩
      have hr'subρ : ball p.pt.1 r' ⊆ ball a.pt.1 ρ := hr'sub.trans sdiff_subset
      have hB'_sub_Bρ : uBall p hr' (hr'subρ.trans hsubρ) ⊆ uBall a hρ hsubρ :=
        uBall_subset_uBall hρ hsubρ hpBρ hr' hr'subρ
      have hB'_ne : uBall p hr' (hr'subρ.trans hsubρ) ⊆ {a}ᶜ := fun q hq hqa =>
        (hr'sub (hqa ▸ hq.1)).2 rfl
      have hharm : HarmonicOnNhd (uPull u₀ p hr' (hr'subρ.trans hsubρ)) (ball p.pt.1 r') := by
        intro z hz
        have hzρ : z ∈ ball a.pt.1 ρ := hr'subρ hz
        have hzne : z ≠ a.pt.1 := (hr'sub hz).2
        have hfne : f z ≠ 0 := norm_pos_iff.mp
          (lt_of_lt_of_le (mul_pos (half_pos hd_pos) (norm_pos_iff.mpr (sub_ne_zero.mpr hzne)))
            (hf_bounds z hzρ).1)
        have hhf : HarmonicAt (fun w => Real.log ‖f w‖) z :=
          holo_log_norm_harmonicAt (hf_diff.analyticAt (isOpen_ball.mem_nhds (ball_subset_ball hρR.le hzρ))) hfne
        refine (harmonicAt_congr_nhds ?_).mp hhf
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        have hwρ : w ∈ ball a.pt.1 ρ := hr'subρ hw
        have hch := uChart_eq_uChart hρ hsubρ hpBρ.1 hpBρ.2 hr' hr'subρ hw
        have hchR := uChart_eq_uChart hR hsubR (mem_ball_self hR) (uChart_self a hR hsubR).symm
          hρ (ball_subset_ball hρR.le) hwρ
        rw [uPull_apply u₀ p hr' _ hw, hch]
        dsimp only [u₀, f]
        rw [if_pos (uChart_mem_uBall a hρ hsubρ hwρ),
          uPull_apply Ψ a hR hsubR (ball_subset_ball hρR.le hwρ), hchR]
      exact ⟨r', hr', hr'subρ.trans hsubρ, hB'_ne, HarmonicOnNhd.isSubharmOnC isOpen_ball hharm⟩
    · have hp_out : p ∈ ({a}ᶜ : Set (UCov Ω w₀)) \ K := ⟨hpne, hpK⟩
      have hopen_out : IsOpen (({a}ᶜ : Set (UCov Ω w₀)) \ K) := hUo.sdiff hK_closed
      obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, hpS, hSout⟩ :=
        (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hopen_out p hp_out
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
      have hB'_out : uBall p hr' (hr'sub.trans hsubq) ⊆ ({a}ᶜ : Set (UCov Ω w₀)) \ K :=
        (uBall_subset_uBall hrq hsubq hpS hr' hr'sub).trans hSout
      have hB'_ne : uBall p hr' (hr'sub.trans hsubq) ⊆ {a}ᶜ := hB'_out.trans sdiff_subset
      have hs : IsSubharmOnC (fun z => Real.log (max ‖uPull Ψ p hr' (hr'sub.trans hsubq) z‖ (Real.exp M)))
          (ball p.pt.1 r') :=
        holo_log_max_isSubharmOnC isOpen_ball (hΨ_holo p r' hr' (hr'sub.trans hsubq)) M
      have heq : Set.EqOn (fun z => Real.log (max ‖uPull Ψ p hr' (hr'sub.trans hsubq) z‖ (Real.exp M)))
          (uPull u₀ p hr' (hr'sub.trans hsubq)) (ball p.pt.1 r') := by
        intro z hz
        dsimp only
        rw [uPull_apply Ψ p hr' _ hz, uPull_apply u₀ p hr' _ hz]
        exact (hu₀_eq_out _ (hB'_out (uChart_mem_uBall p hr' _ hz))).symm
      refine ⟨r', hr', hr'sub.trans hsubq, hB'_ne, hs.1.congr fun z hz => (heq hz).symm, fun z hz => ?_⟩
      obtain ⟨r₀, hr₀, havg⟩ := hs.2 z hz
      refine ⟨r₀, hr₀, fun d' hd' hd'lt hcb => ?_⟩
      have h1 := havg d' hd' hd'lt hcb
      rw [heq hz] at h1
      refine h1.trans_eq (Real.circleAverage_congr_sphere fun ζ hζ => ?_)
      rw [abs_of_pos hd'] at hζ
      exact heq (hcb (sphere_subset_closedBall hζ))
  have hu₀_sub : IsSubharmOnUCov u₀ {a}ᶜ :=
    isSubharmOnUCov_of_local hΩ (continuousOn_of_uPull hΩ fun p hp => by
      obtain ⟨r', hr', hsub', hB, hs⟩ := hu₀_sub_loc p hp
      exact ⟨r', hr', hsub', hB, hs.1⟩) hu₀_sub_loc
  have hu₀_le0 : ∀ p ≠ a, u₀ p ≤ 0 := by
    intro p _
    dsimp only [u₀]
    split_ifs
    · by_cases h0 : ‖Ψ p‖ = 0
      · rw [h0, Real.log_zero]
      · exact (Real.log_neg (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) (hΨ_lt p)).le
    · have hmax_lt1 : max ‖Ψ p‖ (Real.exp M) < 1 :=
        max_lt (hΨ_lt p) (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hM_neg)
      have hmax_pos : 0 < max ‖Ψ p‖ (Real.exp M) := lt_of_lt_of_le (Real.exp_pos M) (le_max_right _ _)
      exact (Real.log_neg hmax_pos hmax_lt1).le
  have hu₀_mem : u₀ ∈ PerronFam a := by
    refine ⟨hu₀_sub, hu₀_le0, ρ, hρ, hsubρ, Real.log (3 * ‖d‖ / 2), fun z hz hzne => ?_⟩
    have hchR := uChart_eq_uChart hR hsubR (mem_ball_self hR) (uChart_self a hR hsubR).symm
      hρ (ball_subset_ball hρR.le) hz
    have hval : u₀ (uChart a hρ hsubρ z hz) = Real.log ‖f z‖ := by
      dsimp only [u₀, f]
      rw [if_pos (uChart_mem_uBall a hρ hsubρ hz),
        uPull_apply Ψ a hR hsubR (ball_subset_ball hρR.le hz), hchR]
    rw [hval]
    have hz_pos : 0 < ‖z - a.pt.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
    have hfz_pos : 0 < ‖f z‖ := lt_of_lt_of_le (mul_pos (half_pos hd_pos) hz_pos) (hf_bounds z hz).1
    have h1 := Real.log_le_log hfz_pos (hf_bounds z hz).2
    rw [Real.log_mul (by positivity) hz_pos.ne', add_comm] at h1
    exact h1
  refine ⟨u₀, ρ, hρ, hsubρ, Real.log (‖d‖ / 2), hu₀_mem, fun z hz hzne => ?_⟩
  have hchR := uChart_eq_uChart hR hsubR (mem_ball_self hR) (uChart_self a hR hsubR).symm
    hρ (ball_subset_ball hρR.le) hz
  have hval : u₀ (uChart a hρ hsubρ z hz) = Real.log ‖f z‖ := by
    dsimp only [u₀, f]
    rw [if_pos (uChart_mem_uBall a hρ hsubρ hz),
      uPull_apply Ψ a hR hsubR (ball_subset_ball hρR.le hz), hchR]
  rw [hval]
  have hz_pos : 0 < ‖z - a.pt.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  have h1 := Real.log_le_log (mul_pos (half_pos hd_pos) hz_pos) (hf_bounds z hz).1
  rw [Real.log_mul (by positivity) hz_pos.ne', add_comm] at h1
  exact h1

private lemma perron_bddAbove {Ω : Set ℂ} {w₀ : Ω} {a p : UCov Ω w₀} (hp : p ≠ a) :
    BddAbove {x : ℝ | ∃ u ∈ PerronFam a, u p = x} :=
  ⟨0, by rintro x ⟨u, hu, rfl⟩; exact hu.2.1 p hp⟩

private lemma le_greenFn {Ω : Set ℂ} {w₀ : Ω} {a p : UCov Ω w₀} (hp : p ≠ a)
    {u : UCov Ω w₀ → ℝ} (hu : u ∈ PerronFam a) : u p ≤ greenFn a p :=
  le_csSup (perron_bddAbove hp) ⟨u, hu, rfl⟩

private lemma greenFn_le_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) {a p : UCov Ω w₀} (hp : p ≠ a) : greenFn a p ≤ 0 := by
  obtain ⟨u₀, _, _, _, _, hu₀, _⟩ := perron_nonempty_and_lower hΩ hΩc hΩP w₀ a
  exact csSup_le ⟨u₀ p, u₀, hu₀, rfl⟩ (by rintro x ⟨u, hu, rfl⟩; exact hu.2.1 p hp)

private lemma exists_perron_close {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) {a p : UCov Ω w₀} (_hp : p ≠ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ PerronFam a, greenFn a p - ε < u p := by
  obtain ⟨u₀, _, _, _, _, hu₀, _⟩ := perron_nonempty_and_lower hΩ hΩc hΩP w₀ a
  have hne : {x : ℝ | ∃ u ∈ PerronFam a, u p = x}.Nonempty := ⟨u₀ p, u₀, hu₀, rfl⟩
  obtain ⟨x, ⟨u, hu, rfl⟩, hx⟩ :=
    exists_lt_of_lt_csSup hne (sub_lt_self (greenFn a p) hε)
  exact ⟨u, hu, hx⟩

private lemma perron_finset_sup {Ω : Set ℂ} {w₀ : Ω} {a : UCov Ω w₀}
    (n : ℕ) (v : ℕ → UCov Ω w₀ → ℝ) (hv : ∀ k ≤ n, v k ∈ PerronFam a) :
    (fun p => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => v k p)) ∈
      PerronFam a := by
  induction n with
  | zero =>
    have heq : (fun p => (Finset.range 1).sup' Finset.nonempty_range_add_one (fun k => v k p)) = v 0 := by
      ext p; simp
    rw [heq]; exact hv 0 le_rfl
  | succ m ih =>
    have hm := ih (fun k hk => hv k (hk.trans (Nat.le_succ m)))
    have hsup := perron_sup hm (hv (m + 1) le_rfl)
    have heq : (fun p => (Finset.range (m + 2)).sup' Finset.nonempty_range_add_one (fun k => v k p)) =
        fun p => max ((Finset.range (m + 1)).sup' Finset.nonempty_range_add_one (fun k => v k p))
          (v (m + 1) p) := by
      ext p
      refine le_antisymm ?_ ?_
      · refine Finset.sup'_le _ _ fun k hk => ?_
        have hlt : k < m + 2 := Finset.mem_range.mp hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hkm | rfl
        · exact (Finset.le_sup' (f := fun j => v j p) (Finset.mem_range.mpr hkm)).trans (le_max_left _ _)
        · exact le_max_right _ _
      · refine max_le (Finset.sup'_le _ _ fun k hk => ?_) ?_
        · exact Finset.le_sup' (f := fun j => v j p)
            (Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans (Nat.lt_succ_self _)))
        · exact Finset.le_sup' (f := fun j => v j p) (Finset.mem_range.mpr (Nat.lt_succ_self _))
    rw [heq]; exact hsup

private lemma greenFn_harmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) (a : UCov Ω w₀) :
    IsHarmOnUCov (greenFn a) {a}ᶜ := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
  obtain ⟨u₀, _, _, _, _, hu₀, _⟩ := perron_nonempty_and_lower hΩ hΩc hΩP w₀ a
  refine isHarmOnUCov_of_local fun p hpne => ?_
  obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, hpS, hSne⟩ :=
    (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hpne
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hsubR : ball p.pt.1 R ⊆ Ω := hRsub.trans hsubq
  have hsubr : ball p.pt.1 r ⊆ Ω := (ball_subset_ball hrR.le).trans hsubR
  have hBR_ne : uBall p (hr.trans hrR) hsubR ⊆ {a}ᶜ :=
    (uBall_subset_uBall hrq hsubq hpS (hr.trans hrR) hRsub).trans hSne
  have hBr_ne : uBall p hr hsubr ⊆ {a}ᶜ :=
    (uBall_subset_uBall (hr.trans hrR) hsubR (mem_uBall_self p (hr.trans hrR) hsubR)
      hr (ball_subset_ball hrR.le)).trans hBR_ne
  -- Helper: given any countable sequence of points in ball p.pt.1 r, produce a harmonic function
  -- H on ball p.pt.1 r with H ≤ uPull (greenFn a) everywhere and H = uPull (greenFn a) on the sequence.
  have hex_harm : ∀ pts : ℕ → ball p.pt.1 r,
      ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball p.pt.1 r) ∧
        (∀ z ∈ ball p.pt.1 r, H z ≤ uPull (greenFn a) p hr hsubr z) ∧
        ∀ k : ℕ, H (pts k).1 = uPull (greenFn a) p hr hsubr (pts k).1 := by
    intro pts
    choose v hv_mem hv_close using fun (n k : ℕ) =>
      exists_perron_close hΩ hΩc hΩP w₀
        (hBr_ne (uChart_mem_uBall p hr hsubr (pts k).2))
        (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    let recSeq : ℕ → UCov Ω w₀ → ℝ :=
      Nat.rec (poissonModUCov u₀ p hr hrR hsubR)
        (fun n prev =>
          let w := fun x => max (prev x)
            ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => v n k x))
          poissonModUCov w p hr hrR hsubR)
    have hrec_mem : ∀ n, recSeq n ∈ PerronFam a := by
      intro n
      induction n with
      | zero => exact perron_poissonMod hΩ hu₀ p hr hrR hsubR hBR_ne
      | succ m ih =>
        exact perron_poissonMod hΩ (perron_sup ih (perron_finset_sup m (v m) fun k _ => hv_mem m k))
          p hr hrR hsubR hBR_ne
    have hrec_harm : ∀ n, HarmonicOnNhd (uPull (recSeq n) p hr hsubr) (ball p.pt.1 r) := by
      intro n
      cases n with
      | zero => exact (poissonModUCov_spec hΩ hUo hu₀.1 p hr hrR hsubR hBR_ne).2.2.1
      | succ m =>
        have hw_mem := perron_sup (hrec_mem m) (perron_finset_sup m (v m) fun k _ => hv_mem m k)
        exact (poissonModUCov_spec hΩ hUo hw_mem.1 p hr hrR hsubR hBR_ne).2.2.1
    have hrec_mono : ∀ n, ∀ z ∈ ball p.pt.1 r,
        uPull (recSeq n) p hr hsubr z ≤ uPull (recSeq (n + 1)) p hr hsubr z := by
      intro n z hz
      rw [uPull_apply _ p hr hsubr hz, uPull_apply _ p hr hsubr hz]
      have hw_mem := perron_sup (hrec_mem n) (perron_finset_sup n (v n) fun k _ => hv_mem n k)
      have hge := (poissonModUCov_spec hΩ hUo hw_mem.1 p hr hrR hsubR hBR_ne).1
        _ (hBr_ne (uChart_mem_uBall p hr hsubr hz))
      exact (le_max_left _ _).trans hge
    have hrec_bdd : ∃ M, ∀ n, uPull (recSeq n) p hr hsubr p.pt.1 ≤ M := by
      refine ⟨0, fun n => ?_⟩
      rw [uPull_self]
      exact (hrec_mem n).2.1 p hpne
    have hlim := harnack_monotone_limit hr hrec_harm hrec_mono hrec_bdd
    refine ⟨fun z => ⨆ n, uPull (recSeq n) p hr hsubr z, hlim.2.2, ?_, ?_⟩
    · intro z hz
      exact ciSup_le fun n => by
        rw [uPull_apply _ p hr hsubr hz, uPull_apply _ p hr hsubr hz]
        exact le_greenFn (hBr_ne (uChart_mem_uBall p hr hsubr hz)) (hrec_mem n)
    · intro k
      have hle : (⨆ n, uPull (recSeq n) p hr hsubr (pts k).1) ≤
          uPull (greenFn a) p hr hsubr (pts k).1 :=
        ciSup_le fun n => by
          rw [uPull_apply _ p hr hsubr (pts k).2, uPull_apply _ p hr hsubr (pts k).2]
          exact le_greenFn (hBr_ne (uChart_mem_uBall p hr hsubr (pts k).2)) (hrec_mem n)
      refine le_antisymm hle ?_
      by_contra hlt
      push Not at hlt
      let ε : ℝ := uPull (greenFn a) p hr hsubr (pts k).1 -
        ⨆ n, uPull (recSeq n) p hr hsubr (pts k).1
      have hε : 0 < ε := sub_pos.mpr hlt
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      let n := max N k
      have hk_mem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _))
      have h1 : 1 / ((n : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ (by positivity)]
        have hN' : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
        have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left N k
        nlinarith
      have h2 : uPull (greenFn a) p hr hsubr (pts k).1 - 1 / ((n : ℝ) + 1) <
          v n k (uChart p hr hsubr (pts k).1 (pts k).2) := by
        rw [uPull_apply _ p hr hsubr (pts k).2]
        exact hv_close n k
      have h3 : v n k (uChart p hr hsubr (pts k).1 (pts k).2) ≤
          uPull (recSeq (n + 1)) p hr hsubr (pts k).1 := by
        rw [uPull_apply _ p hr hsubr (pts k).2]
        have hw_mem := perron_sup (hrec_mem n) (perron_finset_sup n (v n) fun j _ => hv_mem n j)
        have hge := (poissonModUCov_spec hΩ hUo hw_mem.1 p hr hrR hsubR hBR_ne).1
          _ (hBr_ne (uChart_mem_uBall p hr hsubr (pts k).2))
        have hsup_ge : v n k (uChart p hr hsubr (pts k).1 (pts k).2) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun j => v n j (uChart p hr hsubr (pts k).1 (pts k).2)) :=
          Finset.le_sup' (f := fun j => v n j (uChart p hr hsubr (pts k).1 (pts k).2)) hk_mem
        exact (hsup_ge.trans (le_max_right _ _)).trans hge
      have h4 : uPull (recSeq (n + 1)) p hr hsubr (pts k).1 ≤
          ⨆ m, uPull (recSeq m) p hr hsubr (pts k).1 :=
        le_ciSup (hlim.1 (pts k).1 (pts k).2) (n + 1)
      dsimp only [ε] at h1
      linarith
  have : Nonempty (ball p.pt.1 r) := ⟨⟨p.pt.1, mem_ball_self hr⟩⟩
  let qseq : ℕ → ball p.pt.1 r := TopologicalSpace.denseSeq (ball p.pt.1 r)
  have hqdense : DenseRange qseq := TopologicalSpace.denseRange_denseSeq (ball p.pt.1 r)
  obtain ⟨H, hH_harm, hH_le, hH_eq⟩ := hex_harm qseq
  have hG_eq_H : ∀ z ∈ ball p.pt.1 r, uPull (greenFn a) p hr hsubr z = H z := by
    intro z hz
    let pts' : ℕ → ball p.pt.1 r := fun k => match k with | 0 => ⟨z, hz⟩ | k + 1 => qseq k
    obtain ⟨H', hH'_harm, _, hH'_eq⟩ := hex_harm pts'
    have heq_sub : (fun x : ball p.pt.1 r => H' x.1) = fun x : ball p.pt.1 r => H x.1 := by
      refine Continuous.ext_on hqdense
        (hH'_harm.continuousOn.comp_continuous continuous_subtype_val fun x => x.2)
        (hH_harm.continuousOn.comp_continuous continuous_subtype_val fun x => x.2) ?_
      rintro _ ⟨k, rfl⟩
      exact (hH'_eq (k + 1)).trans (hH_eq k).symm
    have hxz : H' z = H z := congr_fun heq_sub ⟨z, hz⟩
    exact (hH'_eq 0).symm.trans hxz
  refine ⟨r, hr, hsubr, hBr_ne, fun z hz => ?_⟩
  refine (harmonicAt_congr_nhds ?_).mpr (hH_harm z hz)
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact hG_eq_H w hw

private lemma greenFn_lt_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) {a p : UCov Ω w₀} (hp : p ≠ a) : greenFn a p < 0 := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
  have hle := greenFn_le_zero hΩ hΩc hΩP w₀ hp
  by_contra hnot
  have h0 : greenFn a p = 0 := le_antisymm hle (not_lt.mp hnot)
  have hharm := greenFn_harmonic hΩ hΩc hΩP w₀ a
  have hsub := hharm.isSubharmOnUCov hΩ hUo
  have hall0 := strong_max_principle_UCov hΩ hUo
    (isPreconnected_compl_singleton_UCov hΩ hΩc w₀ a) hsub
    (fun q hq => greenFn_le_zero hΩ hΩc hΩP w₀ hq) hp h0
  obtain ⟨R, hR, hsubR⟩ := Metric.isOpen_iff.mp hΩ a.pt.1 a.pt.2
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  let z : ℂ := a.pt.1 + ((r / 2 : ℝ) : ℂ)
  have hz : z ∈ ball a.pt.1 r := by
    rw [mem_ball_iff_norm, show z - a.pt.1 = ((r / 2 : ℝ) : ℂ) by simp [z],
      Complex.norm_real, Real.norm_of_nonneg (half_pos hr).le]
    linarith
  have hzne : z ≠ a.pt.1 := by
    intro h
    have h1 : ((r / 2 : ℝ) : ℂ) = 0 := by dsimp only [z] at h; linear_combination h
    have h2 : r / 2 = 0 := Complex.ofReal_eq_zero.mp h1
    linarith
  let q := uChart a (hr.trans hrR) hsubR z (ball_subset_ball hrR.le hz)
  have hqne : q ≠ a := fun h => hzne (congr_arg uProjC h)
  obtain ⟨u₀, _, _, _, _, hu₀, _⟩ := perron_nonempty_and_lower hΩ hΩc hΩP w₀ a
  have hbound : greenFn a q ≤ Real.log ‖z - a.pt.1‖ - Real.log r :=
    csSup_le ⟨u₀ q, u₀, hu₀, rfl⟩
      (by rintro x ⟨u, hu, rfl⟩; exact perron_universal_bound hr hrR hsubR hu hz hzne)
  have hzn : ‖z - a.pt.1‖ = r / 2 := by
    rw [show z - a.pt.1 = ((r / 2 : ℝ) : ℂ) by simp [z],
      Complex.norm_real, Real.norm_of_nonneg (half_pos hr).le]
  have hneg : Real.log ‖z - a.pt.1‖ - Real.log r < 0 := by
    rw [hzn]; exact sub_neg.mpr (Real.log_lt_log (half_pos hr) (half_lt_self hr))
  linarith [hall0 q hqne]

private lemma greenFn_removable_singularity {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) (a : UCov Ω w₀) :
    ∃ (r : ℝ) (hr : 0 < r) (hsub : ball a.pt.1 r ⊆ Ω) (H_a : ℂ → ℝ),
      HarmonicOnNhd H_a (ball a.pt.1 r) ∧
      ∀ z (hz : z ∈ ball a.pt.1 r), z ≠ a.pt.1 →
        greenFn a (uChart a hr hsub z hz) = Real.log ‖z - a.pt.1‖ + H_a z := by
  obtain ⟨u₀, ρ, hρ, hsubρ, c₁, hu₀, hlower⟩ := perron_nonempty_and_lower hΩ hΩc hΩP w₀ a
  let r : ℝ := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hrρ : r < ρ := half_lt_self hρ
  have hsubr : ball a.pt.1 r ⊆ Ω := (ball_subset_ball hrρ.le).trans hsubρ
  have hharm_G := uPull_harmonicOnNhd_punctured hρ hsubρ (greenFn_harmonic hΩ hΩc hΩP w₀ a)
  let H₀ : ℂ → ℝ := fun z => uPull (greenFn a) a hρ hsubρ z - Real.log ‖z - a.pt.1‖
  have hH₀_harm : HarmonicOnNhd H₀ (ball a.pt.1 r \ {a.pt.1}) := by
    intro z ⟨hzr, hzne⟩
    exact (hharm_G z ⟨ball_subset_ball hrρ.le hzr, hzne⟩).sub (log_norm_harmonicAt hzne)
  let M : ℝ := max |c₁| |Real.log r|
  have hH₀_bdd : ∀ z ∈ ball a.pt.1 r \ {a.pt.1}, |H₀ z| ≤ M := by
    intro z ⟨hzr, hzne⟩
    have hzρ : z ∈ ball a.pt.1 ρ := ball_subset_ball hrρ.le hzr
    have hqne : uChart a hρ hsubρ z hzρ ≠ a := fun h => hzne (congr_arg uProjC h)
    have hlow : c₁ ≤ H₀ z := by
      dsimp only [H₀]
      rw [uPull_apply _ a hρ hsubρ hzρ]
      have h1 := hlower z hzρ hzne
      have h2 := le_greenFn hqne hu₀
      linarith
    have hup : H₀ z ≤ -Real.log r := by
      dsimp only [H₀]
      rw [uPull_apply _ a hρ hsubρ hzρ]
      have hbound : greenFn a (uChart a hρ hsubρ z hzρ) ≤ Real.log ‖z - a.pt.1‖ - Real.log r :=
        csSup_le ⟨u₀ _, u₀, hu₀, rfl⟩
          (by rintro x ⟨u, hu, rfl⟩; exact perron_universal_bound hr hrρ hsubρ hu hzr hzne)
      linarith
    rw [abs_le]
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le c₁).trans hlow)
    · exact hup.trans ((neg_le_abs (Real.log r)).trans (le_max_right _ _))
  obtain ⟨H_a, hHa_harm, hHa_eq⟩ := harmonic_removable_singularity hr hH₀_harm hH₀_bdd
  refine ⟨r, hr, hsubr, H_a, hHa_harm, fun z hz hzne => ?_⟩
  have hzρ : z ∈ ball a.pt.1 ρ := ball_subset_ball hrρ.le hz
  have hch := uChart_eq_uChart hρ hsubρ (mem_ball_self hρ) (uChart_self a hρ hsubρ).symm
    hr (ball_subset_ball hrρ.le) hz
  have heq := hHa_eq z ⟨hz, hzne⟩
  dsimp only [H₀] at heq
  rw [uPull_apply _ a hρ hsubρ hzρ] at heq
  rw [hch]
  linarith

/- ### Part 5C: Flat `S1`-covering construction of global holomorphic `ψ_a : UCov Ω w₀ → ball 0 1` -/

private lemma isHoloOnUCov_of_local {Ω : Set ℂ} {w₀ : Ω} {F : UCov Ω w₀ → ℂ}
    (hloc : ∀ p : UCov Ω w₀, ∃ (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      DifferentiableOn ℂ (uPull F p hr hsub) (ball p.pt.1 r)) :
    IsHoloOnUCov F := by
  intro p r hr hsub z hz
  let q := uChart p hr hsub z hz
  have hqB : q ∈ uBall p hr hsub := uChart_mem_uBall p hr hsub hz
  obtain ⟨r₁, hr₁, hsub₁, hd₁⟩ := hloc q
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  let ρ := min r₁ r₂
  have hρ : 0 < ρ := lt_min hr₁ hr₂
  have hsub_p : ball z ρ ⊆ ball p.pt.1 r := (ball_subset_ball (min_le_right _ _)).trans hr₂sub
  have hsub_q : ball z ρ ⊆ ball q.pt.1 r₁ := ball_subset_ball (min_le_left _ _)
  have hdq : DifferentiableAt ℂ (uPull F q hr₁ hsub₁) z :=
    hd₁.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr₁))
  refine (hdq.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [ball_mem_nhds z hρ] with w hw
  have h1 := uPull_eq_on_sub F hr hsub hqB hρ hsub_p hw
  have h2 := uPull_eq_on_sub F hr₁ hsub₁ (mem_uBall_self q hr₁ hsub₁) hρ hsub_q hw
  exact h1.symm.trans h2

private lemma IsHoloOnUCov.continuous {Ω : Set ℂ} (hΩ : IsOpen Ω) {w₀ : Ω}
    {F : UCov Ω w₀ → ℂ} (hF : IsHoloOnUCov F) : Continuous F := by
  refine continuousOn_univ.mp (continuousOn_of_uPull hΩ fun p _ => ?_)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ p.pt.1 p.pt.2
  exact ⟨r, hr, hsub, subset_univ _, (hF p r hr hsub).continuousOn⟩

private abbrev S1 := {u : ℂ // ‖u‖ = 1}

private def s1One : S1 := ⟨1, norm_one⟩

private def s1Mul (u v : S1) : S1 :=
  ⟨u.1 * v.1, by rw [norm_mul, u.2, v.2, mul_one]⟩

private def s1Inv (u : S1) : S1 :=
  ⟨u.1⁻¹, by rw [norm_inv, u.2, inv_one]⟩

private lemma s1Mul_assoc (u v w : S1) : s1Mul (s1Mul u v) w = s1Mul u (s1Mul v w) :=
  Subtype.ext (mul_assoc u.1 v.1 w.1)

private lemma s1Mul_one (u : S1) : s1Mul u s1One = u :=
  Subtype.ext (mul_one u.1)

private lemma s1One_mul (u : S1) : s1Mul s1One u = u :=
  Subtype.ext (one_mul u.1)

private lemma s1Mul_inv (u : S1) : s1Mul u (s1Inv u) = s1One :=
  Subtype.ext (mul_inv_cancel₀ (norm_pos_iff.mp (by rw [u.2]; exact zero_lt_one)))

private lemma s1Inv_mul (u : S1) : s1Mul (s1Inv u) u = s1One :=
  Subtype.ext (inv_mul_cancel₀ (norm_pos_iff.mp (by rw [u.2]; exact zero_lt_one)))

private lemma s1Mul_right_cancel {u v w : S1} (h : s1Mul u w = s1Mul v w) : u = v := by
  have h1 := congr_arg (fun x => s1Mul x (s1Inv w)) h
  simpa only [s1Mul_assoc, s1Mul_inv, s1Mul_one] using h1

open Classical in
private lemma exists_green_holo {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) (a : UCov Ω w₀) :
    ∃ ψ : UCov Ω w₀ → ℂ, IsHoloOnUCov ψ ∧ ψ a = 0 ∧
      (∀ p ≠ a, ‖ψ p‖ = Real.exp (greenFn a p)) ∧
      (∀ p, ‖ψ p‖ < 1) ∧
      ∀ (r : ℝ) (hr : 0 < r) (hsub : ball a.pt.1 r ⊆ Ω),
        deriv (uPull ψ a hr hsub) a.pt.1 ≠ 0 := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  have : SimplyConnectedSpace (UCov Ω w₀) := simplyConnectedSpace_UCov hΩ hΩc w₀
  have : LocallyPathConnectedSpace (UCov Ω w₀) := locallyPathConnectedSpace_UCov hΩ w₀
  have hG_harm := greenFn_harmonic hΩ hΩc hΩP w₀ a
  have hG_lt0 : ∀ p ≠ a, greenFn a p < 0 := fun p hp => greenFn_lt_zero hΩ hΩc hΩP w₀ hp
  -- Step 1: For every p ∈ UCov Ω w₀, construct a local ball and holomorphic φ_p with ‖φ_p‖ = exp(greenFn a).
  have hlocal_data : ∀ p : UCov Ω w₀,
      ∃ (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω) (φ : ℂ → ℂ),
        AnalyticOnNhd ℂ φ (ball p.pt.1 r) ∧
        (p ≠ a → a ∉ uBall p hr hsub) ∧
        (∀ z (hz : z ∈ ball p.pt.1 r),
          uChart p hr hsub z hz ≠ a → ‖φ z‖ = Real.exp (greenFn a (uChart p hr hsub z hz))) ∧
        (p = a → φ a.pt.1 = 0 ∧ deriv φ a.pt.1 ≠ 0) := by
    intro p
    by_cases hpa : p = a
    · subst hpa
      obtain ⟨r₀, hr₀, hsub₀, H_a, hHa_harm, hHa_eq⟩ :=
        greenFn_removable_singularity hΩ hΩc hΩP w₀ p
      obtain ⟨F₀, hF₀_ana, hF₀_re⟩ :=
        InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hHa_harm
      let φ : ℂ → ℂ := fun z => (z - p.pt.1) * Complex.exp (F₀ z)
      refine ⟨r₀, hr₀, hsub₀, φ, ?_, fun h => absurd rfl h, ?_, fun _ => ?_⟩
      · intro z hz
        exact (analyticAt_id.sub analyticAt_const).mul ((hF₀_ana z hz).cexp)
      · intro z hz hne
        have hzne : z ≠ p.pt.1 := fun h => hne (by
          exact uBall_injOn_uProjC p hr₀ hsub₀ (uChart_mem_uBall p hr₀ hsub₀ hz)
            (mem_uBall_self p hr₀ hsub₀) h)
        have hzn_pos : 0 < ‖z - p.pt.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
        have hre : (F₀ z).re = H_a z := hF₀_re hz
        dsimp only [φ]
        rw [norm_mul, Complex.norm_exp, hre, hHa_eq z hz hzne, Real.exp_add, Real.exp_log hzn_pos]
      · refine ⟨by simp [φ], ?_⟩
        have hF₀d : HasDerivAt (fun z => Complex.exp (F₀ z))
            (Complex.exp (F₀ p.pt.1) * deriv F₀ p.pt.1) p.pt.1 :=
          ((hF₀_ana p.pt.1 (mem_ball_self hr₀)).differentiableAt.hasDerivAt).cexp
        have hlin : HasDerivAt (fun z : ℂ => z - p.pt.1) 1 p.pt.1 :=
          (hasDerivAt_id p.pt.1).sub_const p.pt.1
        have hprod := hlin.fun_mul hF₀d
        have hderiv : deriv φ p.pt.1 = Complex.exp (F₀ p.pt.1) := by
          rw [hprod.deriv]; simp
        rw [hderiv]
        exact Complex.exp_ne_zero _
    · have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
      obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, hpS, hSne⟩ :=
        (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hpa
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
      have hB_ne : uBall p hr (hrsub.trans hsubq) ⊆ {a}ᶜ :=
        (uBall_subset_uBall hrq hsubq hpS hr hrsub).trans hSne
      have hharm : HarmonicOnNhd (uPull (greenFn a) p hr (hrsub.trans hsubq)) (ball p.pt.1 r) :=
        hG_harm p r hr (hrsub.trans hsubq) hB_ne
      obtain ⟨F, hF_ana, hF_re⟩ :=
        InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm
      let φ : ℂ → ℂ := fun z => Complex.exp (F z)
      refine ⟨r, hr, hrsub.trans hsubq, φ, fun z hz => (hF_ana z hz).cexp,
        fun _ haB => hB_ne haB rfl, ?_, fun h => absurd h hpa⟩
      intro z hz _
      have hre : (F z).re = uPull (greenFn a) p hr (hrsub.trans hsubq) z := hF_re hz
      dsimp only [φ]
      rw [Complex.norm_exp, hre, uPull_apply (greenFn a) p hr _ hz]
  choose rp hrp hsubp φp hφp_ana hφp_avoid hφp_norm hφp_zero using hlocal_data
  let B : UCov Ω w₀ → Set (UCov Ω w₀) := fun p => uBall p (hrp p) (hsubp p)
  have hB_open : ∀ p, IsOpen (B p) := fun p => isOpen_uBall hΩ p (hrp p) (hsubp p)
  have hB_self : ∀ p, p ∈ B p := fun p => mem_uBall_self p (hrp p) (hsubp p)
  have ha_only_Ba : ∀ p, a ∈ B p → p = a := by
    intro p haB; by_contra hne; exact hφp_avoid p hne haB
  have hφp_norm_at : ∀ (p x : UCov Ω w₀), x ∈ B p → x ≠ a → ‖φp p x.pt.1‖ = Real.exp (greenFn a x) := by
    intro p x hxB hxne
    have h1 := hφp_norm p x.pt.1 hxB.1 (by rwa [← hxB.2])
    rwa [← hxB.2] at h1
  have hφp_ne_zero_at : ∀ (p x : UCov Ω w₀), x ∈ B p → x ≠ a → φp p x.pt.1 ≠ 0 := fun p x hxB hxne =>
    norm_pos_iff.mp (by rw [hφp_norm_at p x hxB hxne]; exact Real.exp_pos _)
  -- Step 2: Transition constants α p q x ∈ S1 on overlaps B p ∩ B q.
  let α : UCov Ω w₀ → UCov Ω w₀ → UCov Ω w₀ → S1 := fun p q x =>
    if hx : x ∈ B p ∧ x ∈ B q ∧ x ≠ a then
      ⟨φp p x.pt.1 / φp q x.pt.1, by
        rw [norm_div, hφp_norm_at p x hx.1 hx.2.2, hφp_norm_at q x hx.2.1 hx.2.2,
          div_self (Real.exp_pos _).ne']⟩
    else s1One
  have hα_self : ∀ p x, α p p x = s1One := by
    intro p x
    dsimp only [α]
    split_ifs with hx
    · exact Subtype.ext (div_self (hφp_ne_zero_at p x hx.1 hx.2.2))
    · rfl
  have hα_cocycle : ∀ p q r x, x ∈ B p → x ∈ B q → x ∈ B r →
      s1Mul (α p q x) (α q r x) = α p r x := by
    intro p q r x hxp hxq hxr
    by_cases hxa : x = a
    · have hp : p = a := ha_only_Ba p (hxa ▸ hxp)
      have hq : q = a := ha_only_Ba q (hxa ▸ hxq)
      have hr : r = a := ha_only_Ba r (hxa ▸ hxr)
      subst hp; subst hq; subst hr
      simp [hα_self, s1Mul_one]
    · have h1 : x ∈ B p ∧ x ∈ B q ∧ x ≠ a := ⟨hxp, hxq, hxa⟩
      have h2 : x ∈ B q ∧ x ∈ B r ∧ x ≠ a := ⟨hxq, hxr, hxa⟩
      have h3 : x ∈ B p ∧ x ∈ B r ∧ x ≠ a := ⟨hxp, hxr, hxa⟩
      dsimp only [α, s1Mul]
      rw [dif_pos h1, dif_pos h2, dif_pos h3]
      exact Subtype.ext (div_mul_div_cancel₀ (hφp_ne_zero_at q x hxq hxa))
  have hα_rel : ∀ p q x, x ∈ B p → x ∈ B q → φp p x.pt.1 = (α p q x).1 * φp q x.pt.1 := by
    intro p q x hxp hxq
    by_cases hxa : x = a
    · have hp : p = a := ha_only_Ba p (hxa ▸ hxp)
      have hq : q = a := ha_only_Ba q (hxa ▸ hxq)
      subst hp; subst hq
      rw [hα_self]; simp [s1One]
    · have h1 : x ∈ B p ∧ x ∈ B q ∧ x ≠ a := ⟨hxp, hxq, hxa⟩
      dsimp only [α]
      rw [dif_pos h1]
      exact (div_mul_cancel₀ _ (hφp_ne_zero_at q x hxq hxa)).symm
  have hα_loc_const : ∀ p q x, x ∈ B p → x ∈ B q →
      ∃ (ρ : ℝ) (hρ : 0 < ρ) (hsubρ : ball x.pt.1 ρ ⊆ Ω),
        uBall x hρ hsubρ ⊆ B p ∩ B q ∧ ∀ y ∈ uBall x hρ hsubρ, α p q y = α p q x := by
    intro p q x hxp hxq
    by_cases hxa : x = a
    · have hp : p = x := (ha_only_Ba p (hxa ▸ hxp)).trans hxa.symm
      have hq : q = x := (ha_only_Ba q (hxa ▸ hxq)).trans hxa.symm
      rw [hp, hq]
      exact ⟨rp x, hrp x, hsubp x, subset_inter subset_rfl subset_rfl,
        fun y _ => by rw [hα_self, hα_self]⟩
    · have hopen : IsOpen (B p ∩ B q ∩ {a}ᶜ) :=
        ((hB_open p).inter (hB_open q)).inter isClosed_singleton.isOpen_compl
      obtain ⟨S, ⟨s, rs, hrs, hsubs, rfl⟩, hxS, hSsub⟩ :=
        (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hopen x ⟨⟨hxp, hxq⟩, hxa⟩
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball x.pt.1 hxS.1
      have hBx_sub : uBall x hρ (hρsub.trans hsubs) ⊆ B p ∩ B q ∩ {a}ᶜ :=
        (uBall_subset_uBall hrs hsubs hxS hρ hρsub).trans hSsub
      have hball_p : ball x.pt.1 ρ ⊆ ball p.pt.1 (hrp p |> fun _ => rp p) := fun z hz =>
        (hBx_sub (uChart_mem_uBall x hρ (hρsub.trans hsubs) hz)).1.1.1
      have hball_q : ball x.pt.1 ρ ⊆ ball q.pt.1 (rp q) := fun z hz =>
        (hBx_sub (uChart_mem_uBall x hρ (hρsub.trans hsubs) hz)).1.2.1
      let Q : ℂ → ℂ := fun z => φp p z / φp q z
      have hQ_diff : DifferentiableOn ℂ Q (ball x.pt.1 ρ) := by
        intro z hz
        have hy := hBx_sub (uChart_mem_uBall x hρ (hρsub.trans hsubs) hz)
        have hqne : φp q z ≠ 0 := hφp_ne_zero_at q (uChart x hρ _ z hz) hy.1.2 hy.2
        exact ((hφp_ana p z (hball_p hz)).differentiableAt.div
          (hφp_ana q z (hball_q hz)).differentiableAt hqne).differentiableWithinAt
      have hQ_norm : ∀ z ∈ ball x.pt.1 ρ, ‖Q z‖ = 1 := by
        intro z hz
        have hy := hBx_sub (uChart_mem_uBall x hρ (hρsub.trans hsubs) hz)
        dsimp only [Q]
        rw [norm_div,
          show ‖φp p z‖ = Real.exp (greenFn a (uChart x hρ _ z hz)) from
            hφp_norm_at p (uChart x hρ _ z hz) hy.1.1 hy.2,
          show ‖φp q z‖ = Real.exp (greenFn a (uChart x hρ _ z hz)) from
            hφp_norm_at q (uChart x hρ _ z hz) hy.1.2 hy.2,
          div_self (Real.exp_pos _).ne']
      have hQ_const := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (convex_ball x.pt.1 ρ).isPreconnected isOpen_ball hQ_diff (mem_ball_self hρ)
        (fun z hz => by
          change ‖Q z‖ ≤ ‖Q x.pt.1‖
          rw [hQ_norm z hz, hQ_norm x.pt.1 (mem_ball_self hρ)])
      refine ⟨ρ, hρ, hρsub.trans hsubs, hBx_sub.trans inter_subset_left, fun y hy => ?_⟩
      have hy_all := hBx_sub hy
      dsimp only [α]
      rw [dif_pos ⟨hy_all.1.1, hy_all.1.2, hy_all.2⟩, dif_pos ⟨hxp, hxq, hxa⟩]
      exact Subtype.ext (hQ_const hy.1)
  -- Step 3: Étale topology on E = UCov Ω w₀ × S1 and covering map Prod.fst : E → UCov Ω w₀.
  let eSheet : ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      uBall p hr hsub ⊆ B p → S1 → Set (UCov Ω w₀ × S1) :=
    fun p r hr hsub _ u => {xv | xv.1 ∈ uBall p hr hsub ∧ xv.2 = s1Mul u (α p xv.1 xv.1)}
  let eBasis : Set (Set (UCov Ω w₀ × S1)) :=
    {S | ∃ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω)
      (hB : uBall p hr hsub ⊆ B p) (u : S1), S = eSheet p r hr hsub hB u}
  let instTopE : TopologicalSpace (UCov Ω w₀ × S1) := TopologicalSpace.generateFrom eBasis
  have heBasis : TopologicalSpace.IsTopologicalBasis eBasis := by
    refine ⟨?_, ?_, rfl⟩
    · rintro _ ⟨p₁, r₁, hr₁, hsub₁, hB₁, u₁, rfl⟩ _ ⟨p₂, r₂, hr₂, hsub₂, hB₂, u₂, rfl⟩ ⟨x, v⟩ ⟨h₁, h₂⟩
      have hxB₁ : x ∈ B p₁ := hB₁ h₁.1
      have hxB₂ : x ∈ B p₂ := hB₂ h₂.1
      obtain ⟨ρ₁, hρ₁, hsubρ₁, hsub_p₁x, hc₁⟩ := hα_loc_const p₁ x x hxB₁ (hB_self x)
      obtain ⟨ρ₂, hρ₂, hsubρ₂, hsub_p₂x, hc₂⟩ := hα_loc_const p₂ x x hxB₂ (hB_self x)
      have hopen_int : IsOpen (ball p₁.pt.1 r₁ ∩ ball p₂.pt.1 r₂ ∩ ball x.pt.1 ρ₁ ∩ ball x.pt.1 ρ₂) :=
        ((isOpen_ball.inter isOpen_ball).inter isOpen_ball).inter isOpen_ball
      have hx_int : x.pt.1 ∈ ball p₁.pt.1 r₁ ∩ ball p₂.pt.1 r₂ ∩ ball x.pt.1 ρ₁ ∩ ball x.pt.1 ρ₂ :=
        ⟨⟨⟨h₁.1.1, h₂.1.1⟩, mem_ball_self hρ₁⟩, mem_ball_self hρ₂⟩
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen_int x.pt.1 hx_int
      have hρ_p₁ : ball x.pt.1 ρ ⊆ ball p₁.pt.1 r₁ := fun z hz => (hρsub hz).1.1.1
      have hρ_p₂ : ball x.pt.1 ρ ⊆ ball p₂.pt.1 r₂ := fun z hz => (hρsub hz).1.1.2
      have hρ_1 : ball x.pt.1 ρ ⊆ ball x.pt.1 ρ₁ := fun z hz => (hρsub hz).1.2
      have hρ_2 : ball x.pt.1 ρ ⊆ ball x.pt.1 ρ₂ := fun z hz => (hρsub hz).2
      have hBx_1 : uBall x hρ (hρ_p₁.trans hsub₁) ⊆ uBall x hρ₁ hsubρ₁ :=
        uBall_subset_uBall hρ₁ hsubρ₁ (mem_uBall_self x hρ₁ hsubρ₁) hρ hρ_1
      have hBx_2 : uBall x hρ (hρ_p₁.trans hsub₁) ⊆ uBall x hρ₂ hsubρ₂ :=
        uBall_subset_uBall hρ₂ hsubρ₂ (mem_uBall_self x hρ₂ hsubρ₂) hρ hρ_2
      have hBx_B : uBall x hρ (hρ_p₁.trans hsub₁) ⊆ B x :=
        hBx_1.trans (hsub_p₁x.trans inter_subset_right)
      have hBx_u₁ : uBall x hρ (hρ_p₁.trans hsub₁) ⊆ uBall p₁ hr₁ hsub₁ :=
        uBall_subset_uBall hr₁ hsub₁ h₁.1 hρ hρ_p₁
      have hBx_u₂ : uBall x hρ (hρ_p₁.trans hsub₁) ⊆ uBall p₂ hr₂ hsub₂ :=
        uBall_subset_uBall hr₂ hsub₂ h₂.1 hρ hρ_p₂
      refine ⟨eSheet x ρ hρ (hρ_p₁.trans hsub₁) hBx_B v,
        ⟨x, ρ, hρ, hρ_p₁.trans hsub₁, hBx_B, v, rfl⟩,
        ⟨mem_uBall_self x hρ _, by rw [hα_self, s1Mul_one]⟩, ?_⟩
      rintro ⟨y, w⟩ ⟨hyB, hw⟩
      dsimp only at hyB hw
      refine ⟨⟨hBx_u₁ hyB, ?_⟩, ⟨hBx_u₂ hyB, ?_⟩⟩
      · have hv₁ : v = s1Mul u₁ (α p₁ x x) := h₁.2
        have hcy₁ : α p₁ x y = α p₁ x x := hc₁ y (hBx_1 hyB)
        change w = s1Mul u₁ (α p₁ y y)
        rw [hw, hv₁, ← hcy₁, s1Mul_assoc,
          hα_cocycle p₁ x y y (hB₁ (hBx_u₁ hyB)) (hBx_B hyB) (hB_self y)]
      · have hv₂ : v = s1Mul u₂ (α p₂ x x) := h₂.2
        have hcy₂ : α p₂ x y = α p₂ x x := hc₂ y (hBx_2 hyB)
        change w = s1Mul u₂ (α p₂ y y)
        rw [hw, hv₂, ← hcy₂, s1Mul_assoc,
          hα_cocycle p₂ x y y (hB₂ (hBx_u₂ hyB)) (hBx_B hyB) (hB_self y)]
    · ext ⟨x, v⟩
      simp only [mem_sUnion, mem_univ, iff_true]
      exact ⟨eSheet x (rp x) (hrp x) (hsubp x) subset_rfl v,
        ⟨x, rp x, hrp x, hsubp x, subset_rfl, v, rfl⟩,
        hB_self x, by rw [hα_self, s1Mul_one]⟩
  have hfst_cont : Continuous (Prod.fst : UCov Ω w₀ × S1 → UCov Ω w₀) := by
    rw [continuous_iff_continuousAt]
    intro ⟨x, v⟩
    rw [ContinuousAt, (uBasis_isTopologicalBasis hΩ w₀).nhds_hasBasis.tendsto_right_iff]
    rintro S ⟨⟨p, r, hr, hsub, rfl⟩, hxS⟩
    have hopen_int : IsOpen (ball p.pt.1 r ∩ ball x.pt.1 (rp x)) := isOpen_ball.inter isOpen_ball
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen_int x.pt.1 ⟨hxS.1, mem_ball_self (hrp x)⟩
    have hBx_B : uBall x hρ ((hρsub.trans inter_subset_right).trans (hsubp x)) ⊆ B x :=
      uBall_subset_uBall (hrp x) (hsubp x) (hB_self x) hρ (hρsub.trans inter_subset_right)
    have hBx_S : uBall x hρ ((hρsub.trans inter_subset_right).trans (hsubp x)) ⊆ uBall p hr hsub :=
      uBall_subset_uBall hr hsub hxS hρ (hρsub.trans inter_subset_left)
    have hopen_sh : IsOpen (eSheet x ρ hρ _ hBx_B v) :=
      heBasis.isOpen ⟨x, ρ, hρ, _, hBx_B, v, rfl⟩
    refine Filter.mem_of_superset (hopen_sh.mem_nhds ⟨mem_uBall_self x hρ _, by rw [hα_self, s1Mul_one]⟩)
      fun yw hyw => hBx_S hyw.1
  have hcov : IsCoveringMap (Prod.fst : UCov Ω w₀ × S1 → UCov Ω w₀) := by
    intro p
    let V : Set (UCov Ω w₀) := B p
    have hV_open : IsOpen V := hB_open p
    have hpV : p ∈ V := hB_self p
    let : TopologicalSpace S1 := ⊥
    have : DiscreteTopology S1 := ⟨rfl⟩
    have : Nonempty S1 := ⟨s1One⟩
    have : Nonempty (UCov Ω w₀ → UCov Ω w₀ × S1) := ⟨fun q => (q, s1One)⟩
    let U : S1 → Set (UCov Ω w₀ × S1) := fun u => eSheet p (rp p) (hrp p) (hsubp p) subset_rfl u
    have hU_open : ∀ u, IsOpen (U u) := fun u =>
      heBasis.isOpen ⟨p, rp p, hrp p, hsubp p, subset_rfl, u, rfl⟩
    have hU_inj : ∀ u, (U u).InjOn Prod.fst := by
      rintro u ⟨q₁, v₁⟩ ⟨_, h1⟩ ⟨q₂, v₂⟩ ⟨_, h2⟩ heq
      dsimp only at h1 h2 heq; subst heq
      exact Prod.ext rfl (h1.trans h2.symm)
    have hU_surj : ∀ u, (U u).SurjOn Prod.fst V := fun u q hq =>
      ⟨(q, s1Mul u (α p q q)), ⟨hq, rfl⟩, rfl⟩
    have hU_disj : Pairwise (Disjoint on U) := by
      intro u₁ u₂ hne
      change Disjoint (U u₁) (U u₂)
      rw [Set.disjoint_left]
      rintro ⟨q, v⟩ ⟨_, h1⟩ ⟨_, h2⟩
      exact hne (s1Mul_right_cancel (h1.symm.trans h2))
    have hU_exh : Prod.fst ⁻¹' V ⊆ ⋃ u, U u := by
      rintro ⟨q, v⟩ hq
      refine mem_iUnion.mpr ⟨s1Mul v (s1Inv (α p q q)), hq, ?_⟩
      rw [s1Mul_assoc, s1Inv_mul, s1Mul_one]
    have hU_open_iff : ∀ u {W'}, W' ⊆ V → (IsOpen W' ↔ IsOpen (Prod.fst ⁻¹' W' ∩ U u)) := by
      intro u W' hW'V
      constructor
      · intro hW'; exact (hW'.preimage hfst_cont).inter (hU_open u)
      · intro hpre
        rw [isOpen_iff_mem_nhds]
        intro q hqW'
        have hmem : (q, s1Mul u (α p q q)) ∈ Prod.fst ⁻¹' W' ∩ U u := ⟨hqW', hW'V hqW', rfl⟩
        obtain ⟨S, ⟨q', r', hr', hsub', hB', u', rfl⟩, hqS, hSsub⟩ :=
          heBasis.isOpen_iff.mp hpre _ hmem
        have hsubW' : uBall q' hr' hsub' ⊆ W' := fun x hx =>
          (hSsub (show (x, s1Mul u' (α q' x x)) ∈ eSheet q' r' hr' hsub' hB' u' from ⟨hx, rfl⟩)).1
        exact Filter.mem_of_superset ((isOpen_uBall hΩ q' hr' hsub').mem_nhds hqS.1) hsubW'
    let triv := hV_open.trivializationDiscrete U V hU_open_iff hU_inj hU_surj hU_disj hU_exh
    exact (IsEvenlyCovered.of_trivialization (t := triv) hpV).to_isEvenlyCovered_preimage
  -- Step 4: Lift ContinuousMap.id to a global continuous section s : C(UCov Ω w₀, E) and build ψ!
  obtain ⟨s, ⟨hs_a, hs_comp⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id (UCov Ω w₀)) a (a, s1One) rfl
  have hs_fst : ∀ q, (s q).1 = q := fun q => congr_fun hs_comp q
  let ψ : UCov Ω w₀ → ℂ := fun q => (s q).2.1 * φp q q.pt.1
  have hψ_local : ∀ p : UCov Ω w₀, ∃ (ρ : ℝ) (hρ : 0 < ρ) (hsubρ : ball p.pt.1 ρ ⊆ Ω),
      ball p.pt.1 ρ ⊆ ball p.pt.1 (rp p) ∧
      ∀ z (hz : z ∈ ball p.pt.1 ρ),
        ψ (uChart p hρ hsubρ z hz) = (s p).2.1 * φp p z := by
    intro p
    let Usp : Set (UCov Ω w₀ × S1) := eSheet p (rp p) (hrp p) (hsubp p) subset_rfl (s p).2
    have hUsp_open : IsOpen Usp :=
      heBasis.isOpen ⟨p, rp p, hrp p, hsubp p, subset_rfl, (s p).2, rfl⟩
    have hsp_mem : s p ∈ Usp := by
      refine ⟨?_, ?_⟩
      · rw [hs_fst p]; exact hB_self p
      · rw [hs_fst p, hα_self, s1Mul_one]
    have hpre_open : IsOpen (s ⁻¹' Usp ∩ B p) := (hUsp_open.preimage s.continuous).inter (hB_open p)
    obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, hpS, hSsub⟩ :=
      (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hpre_open p ⟨hsp_mem, hB_self p⟩
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
    have hBp_sub : uBall p hρ (hρsub.trans hsubq) ⊆ s ⁻¹' Usp ∩ B p :=
      (uBall_subset_uBall hrq hsubq hpS hρ hρsub).trans hSsub
    refine ⟨ρ, hρ, hρsub.trans hsubq, fun z hz => (hBp_sub (uChart_mem_uBall p hρ _ hz)).2.1,
      fun z hz => ?_⟩
    let y := uChart p hρ (hρsub.trans hsubq) z hz
    have hy_all := hBp_sub (uChart_mem_uBall p hρ _ hz)
    have hsy_snd : (s y).2 = s1Mul (s p).2 (α p y y) := by
      have h1 := hy_all.1.2
      rwa [hs_fst y] at h1
    dsimp only [ψ]
    rw [hsy_snd]
    have hrel_y : φp p z = (α p y y).1 * φp y z := hα_rel p y y hy_all.2 (hB_self y)
    change (s p).2.1 * (α p y y).1 * φp y z = (s p).2.1 * φp p z
    rw [mul_assoc, ← hrel_y]
  have hψ_holo : IsHoloOnUCov ψ := by
    refine isHoloOnUCov_of_local fun p => ?_
    obtain ⟨ρ, hρ, hsubρ, hρrp, hψeq⟩ := hψ_local p
    refine ⟨ρ, hρ, hsubρ, ?_⟩
    have hd : DifferentiableOn ℂ (fun z => (s p).2.1 * φp p z) (ball p.pt.1 ρ) := fun z hz =>
      ((hφp_ana p z (hρrp hz)).differentiableAt.const_mul (s p).2.1).differentiableWithinAt
    refine hd.congr fun z hz => ?_
    rw [uPull_apply ψ p hρ hsubρ hz, hψeq z hz]
  have hψ_a : ψ a = 0 := by
    dsimp only [ψ]; rw [(hφp_zero a rfl).1, mul_zero]
  have hψ_norm : ∀ p ≠ a, ‖ψ p‖ = Real.exp (greenFn a p) := by
    intro p hpne
    dsimp only [ψ]
    rw [norm_mul, (s p).2.2, one_mul, hφp_norm_at p p (hB_self p) hpne]
  have hψ_lt1 : ∀ p, ‖ψ p‖ < 1 := by
    intro p
    by_cases hpa : p = a
    · subst hpa; rw [hψ_a, norm_zero]; exact zero_lt_one
    · rw [hψ_norm p hpa, ← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (hG_lt0 p hpa)
  refine ⟨ψ, hψ_holo, hψ_a, hψ_norm, hψ_lt1, fun r hr hsub => ?_⟩
  obtain ⟨ρ, hρ, hsubρ, hρra, hψeq⟩ := hψ_local a
  let ρ' := min r ρ
  have hρ' : 0 < ρ' := lt_min hr hρ
  have hev : uPull ψ a hr hsub =ᶠ[𝓝 a.pt.1] fun z => (s a).2.1 * φp a z := by
    filter_upwards [ball_mem_nhds a.pt.1 hρ'] with z hz
    have hzr : z ∈ ball a.pt.1 r := ball_subset_ball (min_le_left _ _) hz
    have hzρ : z ∈ ball a.pt.1 ρ := ball_subset_ball (min_le_right _ _) hz
    have hch1 := uChart_eq_uChart hr hsub (mem_ball_self hr) (uChart_self a hr hsub).symm
      hρ' (ball_subset_ball (min_le_left _ _)) hz
    have hch2 := uChart_eq_uChart hρ hsubρ (mem_ball_self hρ) (uChart_self a hρ hsubρ).symm
      hρ' (ball_subset_ball (min_le_right _ _)) hz
    rw [uPull_apply ψ a hr hsub hzr, ← hch1, hch2, hψeq z hzρ]
  rw [hev.deriv_eq]
  have hda : HasDerivAt (fun z => (s a).2.1 * φp a z) ((s a).2.1 * deriv (φp a) a.pt.1) a.pt.1 :=
    ((hφp_ana a a.pt.1 (mem_ball_self (hrp a))).differentiableAt.hasDerivAt).const_mul (s a).2.1
  rw [hda.deriv]
  exact mul_ne_zero (norm_pos_iff.mp (by rw [(s a).2.2]; exact zero_lt_one)) (hφp_zero a rfl).2

/- ### Part 5D: Comparison lemma, injectivity, and Koebe surjectivity -/

private lemma comparison_green_holo {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) {a : UCov Ω w₀}
    {ψ_a f : UCov Ω w₀ → ℂ}
    (hψ_holo : IsHoloOnUCov ψ_a) (hψ_a : ψ_a a = 0)
    (hψ_norm : ∀ p ≠ a, ‖ψ_a p‖ = Real.exp (greenFn a p)) (hψ_lt1 : ∀ p, ‖ψ_a p‖ < 1)
    (hf_holo : IsHoloOnUCov f) (hf_lt1 : ∀ p, ‖f p‖ < 1) (hf_a : f a = 0) :
    (∀ p : UCov Ω w₀, ‖f p‖ ≤ ‖ψ_a p‖) ∧
    ∀ (r : ℝ) (hr : 0 < r) (hsub : ball a.pt.1 r ⊆ Ω),
      ‖deriv (uPull f a hr hsub) a.pt.1‖ ≤ ‖deriv (uPull ψ_a a hr hsub) a.pt.1‖ := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  have hG_harm := greenFn_harmonic hΩ hΩc hΩP w₀ a
  let v : UCov Ω w₀ → ℝ := fun q => Real.log (max ‖f q‖ ((1 / 2 : ℝ) * ‖ψ_a q‖))
  have hv_mem : v ∈ PerronFam a := by
    have hv_loc : ∀ p ∈ ({a}ᶜ : Set (UCov Ω w₀)),
        ∃ (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
          uBall p hr hsub ⊆ {a}ᶜ ∧ IsSubharmOnC (uPull v p hr hsub) (ball p.pt.1 r) := by
      intro p hpne
      have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
      obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, hpS, hSne⟩ :=
        (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hpne
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
      have hB_ne : uBall p hr (hrsub.trans hsubq) ⊆ {a}ᶜ :=
        (uBall_subset_uBall hrq hsubq hpS hr hrsub).trans hSne
      let fp : ℂ → ℂ := uPull f p hr (hrsub.trans hsubq)
      let gp : ℂ → ℂ := uPull ψ_a p hr (hrsub.trans hsubq)
      have hfp_diff : DifferentiableOn ℂ fp (ball p.pt.1 r) := hf_holo p r hr (hrsub.trans hsubq)
      have hgp_diff : DifferentiableOn ℂ gp (ball p.pt.1 r) := hψ_holo p r hr (hrsub.trans hsubq)
      have hgp_pos : ∀ z ∈ ball p.pt.1 r, 0 < (1 / 2 : ℝ) * ‖gp z‖ := by
        intro z hz
        dsimp only [gp]
        rw [uPull_apply ψ_a p hr _ hz, hψ_norm _ (hB_ne (uChart_mem_uBall p hr _ hz))]
        positivity
      have hvp_eq : ∀ z ∈ ball p.pt.1 r,
          uPull v p hr (hrsub.trans hsubq) z = Real.log (max ‖fp z‖ ((1 / 2 : ℝ) * ‖gp z‖)) := by
        intro z hz
        dsimp only [v, fp, gp]
        rw [uPull_apply _ p hr _ hz, uPull_apply f p hr _ hz, uPull_apply ψ_a p hr _ hz]
      have hg1_harm : HarmonicOnNhd (fun z => Real.log ((1 / 2 : ℝ) * ‖gp z‖)) (ball p.pt.1 r) := by
        have hG_p := hG_harm p r hr (hrsub.trans hsubq) hB_ne
        intro z hz
        have h1 : HarmonicAt (fun w => Real.log (1 / 2) + uPull (greenFn a) p hr (hrsub.trans hsubq) w) z :=
          (harmonicAt_const (Real.log (1 / 2))).add (hG_p z hz)
        refine (harmonicAt_congr_nhds ?_).mp h1
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        dsimp only [gp]
        rw [uPull_apply ψ_a p hr _ hw, uPull_apply (greenFn a) p hr _ hw,
          hψ_norm _ (hB_ne (uChart_mem_uBall p hr _ hw)),
          Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      have hcont : ContinuousOn (uPull v p hr (hrsub.trans hsubq)) (ball p.pt.1 r) := by
        have hc0 : ContinuousOn (fun z => Real.log (max ‖fp z‖ ((1 / 2 : ℝ) * ‖gp z‖))) (ball p.pt.1 r) := by
          refine Real.continuousOn_log.comp
            ((continuous_norm.comp_continuousOn hfp_diff.continuousOn).sup
              (continuousOn_const.mul (continuous_norm.comp_continuousOn hgp_diff.continuousOn)))
            fun z hz => (lt_of_lt_of_le (hgp_pos z hz) (le_max_right _ _)).ne'
        exact hc0.congr fun z hz => hvp_eq z hz
      refine ⟨r, hr, hrsub.trans hsubq, hB_ne, hcont, fun z hz => ?_⟩
      by_cases hlt : ‖fp z‖ < (1 / 2 : ℝ) * ‖gp z‖
      · have hca1 : ContinuousAt (fun w => ‖fp w‖) z :=
          continuous_norm.continuousAt.comp (hfp_diff.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
        have hca2 : ContinuousAt (fun w => (1 / 2 : ℝ) * ‖gp w‖) z :=
          continuousAt_const.mul (continuous_norm.continuousAt.comp
            (hgp_diff.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt)
        have hev_lt : ∀ᶠ w in 𝓝 z, ‖fp w‖ < (1 / 2 : ℝ) * ‖gp w‖ :=
          (hca2.sub hca1).eventually (Ioi_mem_nhds (sub_pos.mpr hlt)) |>.mono fun _ h => sub_pos.mp h
        obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.mem_nhds_iff.mp
          (Filter.inter_mem (isOpen_ball.mem_nhds hz) hev_lt)
        have hharm_r₀ : HarmonicOnNhd (uPull v p hr (hrsub.trans hsubq)) (ball z r₀) := by
          intro w hw
          refine (harmonicAt_congr_nhds ?_).mp (hg1_harm w (hr₀sub hw).1)
          filter_upwards [isOpen_ball.mem_nhds hw] with ζ hζ
          rw [hvp_eq ζ (hr₀sub hζ).1, max_eq_right (hr₀sub hζ).2.le]
        obtain ⟨r₁, hr₁, havg⟩ := (HarmonicOnNhd.isSubharmOnC isOpen_ball hharm_r₀).2 z (mem_ball_self hr₀)
        refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun d hd hdlt _ => ?_⟩
        exact havg d hd (lt_of_lt_of_le hdlt (min_le_right _ _))
          (closedBall_subset_ball (lt_of_lt_of_le hdlt (min_le_left _ _)))
      · push Not at hlt
        have hfne : fp z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (hgp_pos z hz) hlt)
        have hfana : AnalyticAt ℂ fp z := hfp_diff.analyticAt (isOpen_ball.mem_nhds hz)
        have hharm_f : HarmonicAt (fun w => Real.log ‖fp w‖) z := holo_log_norm_harmonicAt hfana hfne
        obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.mem_nhds_iff.mp
          (Filter.inter_mem (isOpen_ball.mem_nhds hz)
            (Filter.inter_mem ((isOpen_setOfPred_harmonicAt _).mem_nhds hharm_f)
              (hfana.continuousAt.eventually (isOpen_ne.mem_nhds hfne))))
        have hs1 : IsSubharmOnC (fun w => Real.log ‖fp w‖) (ball z r₀) :=
          HarmonicOnNhd.isSubharmOnC isOpen_ball fun w hw => (hr₀sub hw).2.1
        have hs2 : IsSubharmOnC (fun w => Real.log ((1 / 2 : ℝ) * ‖gp w‖)) (ball z r₀) :=
          HarmonicOnNhd.isSubharmOnC isOpen_ball fun w hw => hg1_harm w (hr₀sub hw).1
        have hsup := IsSubharmOnC.sup hs1 hs2
        have heq_r₀ : ∀ w ∈ ball z r₀,
            uPull v p hr (hrsub.trans hsubq) w = max (Real.log ‖fp w‖) (Real.log ((1 / 2 : ℝ) * ‖gp w‖)) := by
          intro w hw
          rw [hvp_eq w (hr₀sub hw).1]
          have hfp_pos : 0 < ‖fp w‖ := norm_pos_iff.mpr (hr₀sub hw).2.2
          have hgp_p : 0 < (1 / 2 : ℝ) * ‖gp w‖ := hgp_pos w (hr₀sub hw).1
          by_cases hle : ‖fp w‖ ≤ (1 / 2 : ℝ) * ‖gp w‖
          · rw [max_eq_right hle, max_eq_right (Real.log_le_log hfp_pos hle)]
          · push Not at hle
            rw [max_eq_left hle.le, max_eq_left (Real.log_le_log hgp_p hle.le)]
        obtain ⟨r₁, hr₁, havg⟩ := hsup.2 z (mem_ball_self hr₀)
        refine ⟨min r₀ r₁, lt_min hr₀ hr₁, fun d hd hdlt _ => ?_⟩
        have h1 := havg d hd (lt_of_lt_of_le hdlt (min_le_right _ _))
          (closedBall_subset_ball (lt_of_lt_of_le hdlt (min_le_left _ _)))
        dsimp only at h1
        rw [← heq_r₀ z (mem_ball_self hr₀)] at h1
        refine h1.trans_eq (Real.circleAverage_congr_sphere fun ζ hζ => ?_)
        rw [abs_of_pos hd] at hζ
        exact (heq_r₀ ζ (closedBall_subset_ball (lt_of_lt_of_le hdlt (min_le_left _ _))
          (sphere_subset_closedBall hζ))).symm
    have hv_sub : IsSubharmOnUCov v {a}ᶜ :=
      isSubharmOnUCov_of_local hΩ (continuousOn_of_uPull hΩ fun p hp => by
        obtain ⟨r, hr, hsub, hB, hs⟩ := hv_loc p hp
        exact ⟨r, hr, hsub, hB, hs.1⟩) hv_loc
    have hv_le0 : ∀ p ≠ a, v p ≤ 0 := by
      intro p hp
      have hpos : 0 < max ‖f p‖ ((1 / 2 : ℝ) * ‖ψ_a p‖) :=
        lt_of_lt_of_le (by rw [hψ_norm p hp]; positivity) (le_max_right _ _)
      have hlt1 : max ‖f p‖ ((1 / 2 : ℝ) * ‖ψ_a p‖) < 1 :=
        max_lt (hf_lt1 p) (by linarith [hψ_lt1 p])
      exact (Real.log_neg hpos hlt1).le
    obtain ⟨R, hR, hsubR⟩ := Metric.isOpen_iff.mp hΩ a.pt.1 a.pt.2
    let r : ℝ := R / 2
    have hr : 0 < r := half_pos hR
    have hrR : r < R := half_lt_self hR
    have hsubr : ball a.pt.1 r ⊆ Ω := (ball_subset_ball hrR.le).trans hsubR
    have hlip : ∀ (h : UCov Ω w₀ → ℂ), IsHoloOnUCov h → h a = 0 →
        ∃ C > 0, ∀ z ∈ ball a.pt.1 r, ‖uPull h a hR hsubR z‖ ≤ C * ‖z - a.pt.1‖ := by
      intro h hh hha
      have hds : DifferentiableOn ℂ (dslope (uPull h a hR hsubR) a.pt.1) (ball a.pt.1 R) :=
        (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr (hh a R hR hsubR)
      obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall a.pt.1 r).exists_bound_of_continuousOn
        (hds.continuousOn.mono (closedBall_subset_ball hrR))
      refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz => ?_⟩
      have h1 : uPull h a hR hsubR z = (z - a.pt.1) * dslope (uPull h a hR hsubR) a.pt.1 z := by
        have h0 := sub_smul_dslope (uPull h a hR hsubR) a.pt.1 z
        rw [uPull_self, hha, sub_zero, smul_eq_mul] at h0
        exact h0.symm
      rw [h1, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hC₀ z (ball_subset_closedBall hz)).trans (le_max_left _ _))
        (norm_nonneg _)
    obtain ⟨C₁, hC₁, hlip_f⟩ := hlip f hf_holo hf_a
    obtain ⟨C₂, hC₂, hlip_ψ⟩ := hlip ψ_a hψ_holo hψ_a
    let C : ℝ := max C₁ C₂
    have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
    refine ⟨hv_sub, hv_le0, r, hr, hsubr, Real.log C, fun z hz hzne => ?_⟩
    have hzR : z ∈ ball a.pt.1 R := ball_subset_ball hrR.le hz
    have hch := uChart_eq_uChart hR hsubR (mem_ball_self hR) (uChart_self a hR hsubR).symm
      hr (ball_subset_ball hrR.le) hz
    have hqne : uChart a hr hsubr z hz ≠ a := fun h => hzne (congr_arg uProjC h)
    have hpos : 0 < max ‖f (uChart a hr hsubr z hz)‖ ((1 / 2 : ℝ) * ‖ψ_a (uChart a hr hsubr z hz)‖) :=
      lt_of_lt_of_le (by rw [hψ_norm _ hqne]; positivity) (le_max_right _ _)
    have hle_C : max ‖f (uChart a hr hsubr z hz)‖ ((1 / 2 : ℝ) * ‖ψ_a (uChart a hr hsubr z hz)‖) ≤
        C * ‖z - a.pt.1‖ := by
      rw [hch]
      have hf_b : ‖f (uChart a hR hsubR z hzR)‖ ≤ C₁ * ‖z - a.pt.1‖ := by
        simpa [uPull_apply f a hR hsubR hzR] using hlip_f z hz
      have hψ_b : ‖ψ_a (uChart a hR hsubR z hzR)‖ ≤ C₂ * ‖z - a.pt.1‖ := by
        simpa [uPull_apply ψ_a a hR hsubR hzR] using hlip_ψ z hz
      refine max_le (hf_b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) ?_
      have : (1 / 2 : ℝ) * ‖ψ_a (uChart a hR hsubR z hzR)‖ ≤ ‖ψ_a (uChart a hR hsubR z hzR)‖ := by
        linarith [norm_nonneg (ψ_a (uChart a hR hsubR z hzR))]
      exact this.trans (hψ_b.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
    have hlog := Real.log_le_log hpos hle_C
    rw [Real.log_mul hC.ne' (norm_pos_iff.mpr (sub_ne_zero.mpr hzne)).ne', add_comm] at hlog
    exact hlog
  have hnorm_le : ∀ p : UCov Ω w₀, ‖f p‖ ≤ ‖ψ_a p‖ := by
    intro p
    by_cases hpa : p = a
    · subst hpa; rw [hf_a, hψ_a]
    · by_cases hf0 : f p = 0
      · rw [hf0, norm_zero]; exact norm_nonneg _
      · have hfp_pos : 0 < ‖f p‖ := norm_pos_iff.mpr hf0
        have h1 : Real.log ‖f p‖ ≤ v p :=
          Real.log_le_log hfp_pos (le_max_left _ _)
        have h2 : v p ≤ greenFn a p := le_greenFn hpa hv_mem
        have h3 : ‖f p‖ ≤ Real.exp (greenFn a p) := by
          rw [← Real.exp_log hfp_pos]
          exact Real.exp_le_exp.mpr (h1.trans h2)
        rwa [← hψ_norm p hpa] at h3
  refine ⟨hnorm_le, fun r hr hsub => ?_⟩
  have hdf : HasDerivAt (uPull f a hr hsub) (deriv (uPull f a hr hsub) a.pt.1) a.pt.1 :=
    ((hf_holo a r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have hdψ : HasDerivAt (uPull ψ_a a hr hsub) (deriv (uPull ψ_a a hr hsub) a.pt.1) a.pt.1 :=
    ((hψ_holo a r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have htf := (hasDerivAt_iff_tendsto_slope.mp hdf).norm
  have htψ := (hasDerivAt_iff_tendsto_slope.mp hdψ).norm
  refine le_of_tendsto_of_tendsto htf htψ ?_
  filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)), self_mem_nhdsWithin]
    with z hzr hzne
  simp only [slope_def_field, uPull_self, hf_a, hψ_a, sub_zero, norm_div]
  rw [uPull_apply f a hr hsub hzr, uPull_apply ψ_a a hr hsub hzr]
  exact div_le_div_of_nonneg_right (hnorm_le _) (norm_nonneg _)

open Classical in
private lemma exists_biholo_UCov_ball {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPathConnected Ω)
    (hΩP : Ω ⊆ PSet) (w₀ : Ω) :
    ∃ ψ : UCov Ω w₀ → ℂ, IsHoloOnUCov ψ ∧ ψ (uBase w₀) = 0 ∧
      (∀ p, ‖ψ p‖ < 1) ∧ Function.Injective ψ ∧
      (∀ w ∈ ball (0 : ℂ) 1, ∃ p, ψ p = w) ∧
      ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
        deriv (uPull ψ p hr hsub) p.pt.1 ≠ 0 := by
  have : T2Space (UCov Ω w₀) := t2Space_UCov hΩ w₀
  have : SimplyConnectedSpace (UCov Ω w₀) := simplyConnectedSpace_UCov hΩ hΩc w₀
  have : LocallyPathConnectedSpace (UCov Ω w₀) := locallyPathConnectedSpace_UCov hΩ w₀
  let o : UCov Ω w₀ := uBase w₀
  obtain ⟨ψ, hψ_holo, hψ_o, hψ_norm, hψ_lt1, hψ_deriv_o⟩ :=
    exists_green_holo hΩ hΩc hΩP w₀ o
  -- Step 1: For every a ≠ o, show diskMob (ψ a) ∘ ψ = c₀ * ψ_a with ‖c₀‖ = 1!
  have hsym : ∀ a : UCov Ω w₀, a ≠ o →
      ∃ (ψ_a : UCov Ω w₀ → ℂ) (c₀ : ℂ), IsHoloOnUCov ψ_a ∧ ‖c₀‖ = 1 ∧
        (∀ p ≠ a, ψ_a p ≠ 0) ∧
        (∀ (r : ℝ) (hr : 0 < r) (hsub : ball a.pt.1 r ⊆ Ω), deriv (uPull ψ_a a hr hsub) a.pt.1 ≠ 0) ∧
        ∀ p, diskMob (ψ a) (ψ p) = c₀ * ψ_a p := by
    intro a hao
    obtain ⟨ψ_a, hψa_holo, hψa_a, hψa_norm, hψa_lt1, hψa_deriv⟩ :=
      exists_green_holo hΩ hΩc hΩP w₀ a
    let fa : UCov Ω w₀ → ℂ := fun p => diskMob (ψ a) (ψ p)
    have hfa_holo : IsHoloOnUCov fa := hψ_holo.comp_diskMob hψ_lt1 (hψ_lt1 a)
    have hfa_lt1 : ∀ p, ‖fa p‖ < 1 := fun p => norm_diskMob_lt_one (hψ_lt1 a) (hψ_lt1 p)
    have hfa_a : fa a = 0 := diskMob_self
    have hle1 : ∀ p, ‖fa p‖ ≤ ‖ψ_a p‖ :=
      (comparison_green_holo hΩ hΩc hΩP w₀ hψa_holo hψa_a hψa_norm hψa_lt1 hfa_holo hfa_lt1 hfa_a).1
    let ga : UCov Ω w₀ → ℂ := fun p => diskMob (ψ_a o) (ψ_a p)
    have hga_holo : IsHoloOnUCov ga := hψa_holo.comp_diskMob hψa_lt1 (hψa_lt1 o)
    have hga_lt1 : ∀ p, ‖ga p‖ < 1 := fun p => norm_diskMob_lt_one (hψa_lt1 o) (hψa_lt1 p)
    have hga_o : ga o = 0 := diskMob_self
    have hle2 : ∀ p, ‖ga p‖ ≤ ‖ψ p‖ :=
      (comparison_green_holo hΩ hΩc hΩP w₀ hψ_holo hψ_o hψ_norm hψ_lt1 hga_holo hga_lt1 hga_o).1
    have hfa_o_norm : ‖fa o‖ = ‖ψ a‖ := by dsimp only [fa]; rw [hψ_o, norm_diskMob_zero]
    have hga_a_norm : ‖ga a‖ = ‖ψ_a o‖ := by dsimp only [ga]; rw [hψa_a, norm_diskMob_zero]
    have heq_norm : ‖fa o‖ = ‖ψ_a o‖ := le_antisymm (hle1 o) (by rw [hfa_o_norm, ← hga_a_norm]; exact hle2 a)
    have hψa_ne : ∀ p ≠ a, ψ_a p ≠ 0 := fun p hp =>
      norm_pos_iff.mp (by rw [hψa_norm p hp]; exact Real.exp_pos _)
    let Q : UCov Ω w₀ → ℂ := fun p => fa p / ψ_a p
    let c₀ : ℂ := Q o
    have hc₀_norm : ‖c₀‖ = 1 := by
      dsimp only [c₀, Q]
      rw [norm_div, heq_norm, div_self (norm_pos_iff.mpr (hψa_ne o hao.symm)).ne']
    have hQ_le1 : ∀ p ≠ a, ‖Q p‖ ≤ 1 := fun p hp => by
      dsimp only [Q]
      rw [norm_div, div_le_one (norm_pos_iff.mpr (hψa_ne p hp))]
      exact hle1 p
    have hQ_cont : ContinuousOn Q {a}ᶜ := by
      refine continuousOn_of_uPull hΩ fun p hp => ?_
      have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
      obtain ⟨S, ⟨q, rq, hrq, hsubq, rfl⟩, hpS, hSne⟩ :=
        (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hp
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpS.1
      have hB_ne : uBall p hr (hrsub.trans hsubq) ⊆ {a}ᶜ :=
        (uBall_subset_uBall hrq hsubq hpS hr hrsub).trans hSne
      refine ⟨r, hr, hrsub.trans hsubq, hB_ne, ?_⟩
      have hd : DifferentiableOn ℂ (uPull Q p hr (hrsub.trans hsubq)) (ball p.pt.1 r) := by
        intro z hz
        have h1 := ((hfa_holo p r hr (hrsub.trans hsubq)).differentiableAt (isOpen_ball.mem_nhds hz)).div
          ((hψa_holo p r hr (hrsub.trans hsubq)).differentiableAt (isOpen_ball.mem_nhds hz))
          (by rw [dif_pos hz]; exact hψa_ne _ (hB_ne (uChart_mem_uBall p hr _ hz)))
        refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        dsimp only [Q]
        rw [uPull_apply _ p hr _ hw, Pi.div_apply, dif_pos hw, dif_pos hw]
      exact hd.continuousOn
    -- Clopen argument on preconnected {a}ᶜ: S = {p ≠ a | Q p = c₀} is open and closed in {a}ᶜ.
    let S : Set (UCov Ω w₀) := {p ∈ ({a}ᶜ : Set (UCov Ω w₀)) | Q p = c₀}
    let T : Set (UCov Ω w₀) := {p ∈ ({a}ᶜ : Set (UCov Ω w₀)) | Q p ≠ c₀}
    have hUo : IsOpen ({a}ᶜ : Set (UCov Ω w₀)) := isClosed_singleton.isOpen_compl
    have hTo : IsOpen T := by
      rw [isOpen_iff_mem_nhds]
      intro p ⟨hpne, hpQ⟩
      have hca : ContinuousAt Q p := (hQ_cont p hpne).continuousAt (hUo.mem_nhds hpne)
      exact Filter.inter_mem (hUo.mem_nhds hpne) (hca.eventually (isOpen_ne.mem_nhds hpQ))
    have hSo : IsOpen S := by
      rw [isOpen_iff_mem_nhds]
      intro p ⟨hpne, hpQ⟩
      obtain ⟨U0, ⟨q, rq, hrq, hsubq, rfl⟩, hpU, hUne⟩ :=
        (uBasis_isTopologicalBasis hΩ w₀).isOpen_iff.mp hUo p hpne
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball p.pt.1 hpU.1
      have hB_ne : uBall p hr (hrsub.trans hsubq) ⊆ {a}ᶜ :=
        (uBall_subset_uBall hrq hsubq hpU hr hrsub).trans hUne
      have hQd : DifferentiableOn ℂ (uPull Q p hr (hrsub.trans hsubq)) (ball p.pt.1 r) := by
        intro z hz
        have h1 := ((hfa_holo p r hr (hrsub.trans hsubq)).differentiableAt (isOpen_ball.mem_nhds hz)).div
          ((hψa_holo p r hr (hrsub.trans hsubq)).differentiableAt (isOpen_ball.mem_nhds hz))
          (by rw [dif_pos hz]; exact hψa_ne _ (hB_ne (uChart_mem_uBall p hr _ hz)))
        refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        dsimp only [Q]
        rw [uPull_apply _ p hr _ hw, Pi.div_apply, dif_pos hw, dif_pos hw]
      have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (convex_ball p.pt.1 r).isPreconnected isOpen_ball hQd (mem_ball_self hr)
        (fun z hz => by
          change ‖uPull Q p hr (hrsub.trans hsubq) z‖ ≤ ‖uPull Q p hr (hrsub.trans hsubq) p.pt.1‖
          rw [uPull_apply Q p hr _ hz, uPull_self, hpQ, hc₀_norm]
          exact hQ_le1 _ (hB_ne (uChart_mem_uBall p hr _ hz)))
      refine Filter.mem_of_superset ((isOpen_uBall hΩ p hr _).mem_nhds (mem_uBall_self p hr _))
        fun x hx => ⟨hB_ne hx, ?_⟩
      have h1 := hconst hx.1
      rw [uPull_apply Q p hr _ hx.1, ← hx.2, uPull_self, hpQ] at h1
      exact h1
    have hQ_all : ∀ p ≠ a, Q p = c₀ := by
      intro p hpne
      by_contra hne
      have hcov : ({a}ᶜ : Set (UCov Ω w₀)) ⊆ S ∪ T := fun q hq => by
        by_cases h : Q q = c₀
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
      obtain ⟨q, -, hqS, hqT⟩ := (isPreconnected_compl_singleton_UCov hΩ hΩc w₀ a)
        S T hSo hTo hcov ⟨o, hao.symm, hao.symm, rfl⟩ ⟨p, hpne, hpne, hne⟩
      exact hqT.2 hqS.2
    refine ⟨ψ_a, c₀, hψa_holo, hc₀_norm, hψa_ne, hψa_deriv, fun p => ?_⟩
    by_cases hpa : p = a
    · subst hpa; rw [hψa_a, mul_zero]; exact diskMob_self
    · have h1 : fa p / ψ_a p = c₀ := hQ_all p hpa
      exact (div_eq_iff (hψa_ne p hpa)).mp h1
  -- Step 2: Deduce injectivity and non-vanishing derivative everywhere!
  have hψ_inj : Function.Injective ψ := by
    intro p a hpa
    by_contra hne
    by_cases hao : a = o
    · subst hao
      rw [hψ_o] at hpa
      have h0 : ‖ψ p‖ = 0 := by rw [hpa, norm_zero]
      rw [hψ_norm p hne] at h0
      linarith [Real.exp_pos (greenFn o p)]
    · obtain ⟨ψ_a, c₀, -, hc₀, hψa_ne, -, hrel⟩ := hsym a hao
      have h1 := hrel p
      rw [hpa, diskMob_self] at h1
      have hc₀_ne : c₀ ≠ 0 := norm_pos_iff.mp (by rw [hc₀]; exact zero_lt_one)
      exact mul_ne_zero hc₀_ne (hψa_ne p hne) h1.symm
  have hψ_deriv : ∀ (p : UCov Ω w₀) (r : ℝ) (hr : 0 < r) (hsub : ball p.pt.1 r ⊆ Ω),
      deriv (uPull ψ p hr hsub) p.pt.1 ≠ 0 := by
    intro a r hr hsub
    by_cases hao : a = o
    · subst hao; exact hψ_deriv_o r hr hsub
    · obtain ⟨ψ_a, c₀, hψa_holo, hc₀, -, hψa_deriv, hrel⟩ := hsym a hao
      have hdψ : HasDerivAt (uPull ψ a hr hsub) (deriv (uPull ψ a hr hsub) a.pt.1) a.pt.1 :=
        ((hψ_holo a r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
      have hmob := hasDerivAt_diskMob (b := ψ a) (w := ψ a) (hψ_lt1 a) (hψ_lt1 a)
      have hmob' : HasDerivAt (diskMob (ψ a))
          (((1 - ‖ψ a‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ (ψ a) * ψ a) ^ 2)
          (uPull ψ a hr hsub a.pt.1) := by rwa [uPull_self]
      have hcomp : HasDerivAt (fun w => diskMob (ψ a) (uPull ψ a hr hsub w))
          ((((1 - ‖ψ a‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ (ψ a) * ψ a) ^ 2) *
            deriv (uPull ψ a hr hsub) a.pt.1) a.pt.1 :=
        hmob'.comp a.pt.1 hdψ
      have hev : (fun w => c₀ * uPull ψ_a a hr hsub w) =ᶠ[𝓝 a.pt.1]
          fun w => diskMob (ψ a) (uPull ψ a hr hsub w) := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
        rw [uPull_apply ψ a hr hsub hw, uPull_apply ψ_a a hr hsub hw]
        exact (hrel (uChart a hr hsub w hw)).symm
      have hd_rhs : HasDerivAt (fun w => c₀ * uPull ψ_a a hr hsub w)
          (c₀ * deriv (uPull ψ_a a hr hsub) a.pt.1) a.pt.1 :=
        ((hψa_holo a r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt.const_mul c₀
      have heq_d := (hcomp.congr_of_eventuallyEq hev).unique hd_rhs
      intro h0
      rw [h0, mul_zero] at heq_d
      have hc₀_ne : c₀ ≠ 0 := norm_pos_iff.mp (by rw [hc₀]; exact zero_lt_one)
      exact mul_ne_zero hc₀_ne (hψa_deriv r hr hsub) heq_d.symm
  -- Step 3: Surjectivity onto ball 0 1 via Koebe square-root trick!
  have hψ_surj : ∀ w₁ ∈ ball (0 : ℂ) 1, ∃ p, ψ p = w₁ := by
    intro w₁ hw₁
    by_contra hnot
    push Not at hnot
    have hw₁_lt : ‖w₁‖ < 1 := by simpa [mem_ball_iff_norm] using hw₁
    have hw₁_ne : w₁ ≠ 0 := fun h => hnot o (hψ_o.trans h.symm)
    let g : UCov Ω w₀ → ℂ := fun p => diskMob w₁ (ψ p)
    have hg_holo : IsHoloOnUCov g := hψ_holo.comp_diskMob hψ_lt1 hw₁_lt
    have hg_lt1 : ∀ p, ‖g p‖ < 1 := fun p => norm_diskMob_lt_one hw₁_lt (hψ_lt1 p)
    have hg_ne : ∀ p, g p ≠ 0 := fun p h => hnot p ((diskMob_eq_zero_iff hw₁_lt (hψ_lt1 p)).mp h)
    have hg_cont : Continuous g := hg_holo.continuous hΩ
    obtain ⟨L, ⟨-, hL_comp⟩, -⟩ :=
      Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
        ⟨g, hg_cont⟩ (Complex.exp_log (hg_ne o)) (fun p => hg_ne p)
    have hL_exp : ∀ p, Complex.exp (L p) = g p := fun p => congr_fun hL_comp p
    let S : UCov Ω w₀ → ℂ := fun p => Complex.exp (L p / 2)
    have hS_cont : Continuous S := Complex.continuous_exp.comp (L.continuous.div_const 2)
    have hS_sq : ∀ p, S p ^ 2 = g p := fun p => by
      dsimp only [S]
      rw [sq, ← Complex.exp_add, add_halves, hL_exp p]
    have hS_ne : ∀ p, S p ≠ 0 := fun p => Complex.exp_ne_zero _
    have hS_lt1 : ∀ p, ‖S p‖ < 1 := by
      intro p
      have hsq : ‖S p‖ ^ 2 < 1 := by rw [← norm_pow, hS_sq p]; exact hg_lt1 p
      nlinarith [norm_nonneg (S p)]
    have hS_holo : IsHoloOnUCov S := by
      refine isHoloOnUCov_of_local fun p => ?_
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ p.pt.1 p.pt.2
      refine ⟨r, hr, hsub, fun z hz => ?_⟩
      have hsd_sq : HasStrictDerivAt (fun w : ℂ => w ^ 2) (2 * uPull S p hr hsub z) (uPull S p hr hsub z) := by
        simpa using hasStrictDerivAt_pow 2 (uPull S p hr hsub z)
      have h2ne : 2 * uPull S p hr hsub z ≠ 0 := by
        rw [uPull_apply S p hr hsub hz]
        exact mul_ne_zero (by norm_num) (hS_ne _)
      let φ := (hsd_sq.hasStrictFDerivAt_equiv h2ne).toOpenPartialHomeomorph (fun w : ℂ => w ^ 2)
      have hSz_src : uPull S p hr hsub z ∈ φ.source :=
        (hsd_sq.hasStrictFDerivAt_equiv h2ne).mem_toOpenPartialHomeomorph_source
      have hS_ca : ContinuousAt (uPull S p hr hsub) z :=
        (continuousOn_uPull hΩ hS_cont.continuousOn p hr hsub (subset_univ _)).continuousAt
          (isOpen_ball.mem_nhds hz)
      have hφ_symm_sd : HasStrictDerivAt φ.symm (2 * uPull S p hr hsub z)⁻¹ (φ (uPull S p hr hsub z)) := by
        have h1 := HasStrictDerivAt.of_local_left_inverse
          (φ.symm.continuousAt (φ.map_source hSz_src))
          (by rwa [φ.left_inv hSz_src])
          h2ne
          (φ.eventually_right_inverse (φ.map_source hSz_src))
        exact h1
      have hφ_eq_g : φ (uPull S p hr hsub z) = uPull g p hr hsub z := by
        change (uPull S p hr hsub z) ^ 2 = uPull g p hr hsub z
        rw [uPull_apply S p hr hsub hz, uPull_apply g p hr hsub hz, hS_sq]
      rw [hφ_eq_g] at hφ_symm_sd
      have hgd := ((hg_holo p r hr hsub).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      have hcomp := (hφ_symm_sd.hasDerivAt.comp z hgd)
      refine (hcomp.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ball.mem_nhds hz, hS_ca (φ.open_source.mem_nhds hSz_src)] with w hw hws
      have hsq_w : φ (uPull S p hr hsub w) = uPull g p hr hsub w := by
        change (uPull S p hr hsub w) ^ 2 = uPull g p hr hsub w
        rw [uPull_apply S p hr hsub hw, uPull_apply g p hr hsub hw, hS_sq]
      change uPull S p hr hsub w = φ.symm (uPull g p hr hsub w)
      rw [← hsq_w, φ.left_inv hws]
    let b : ℂ := S o
    have hb_lt1 : ‖b‖ < 1 := hS_lt1 o
    have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr (hS_ne o)
    have hb_sq : ‖b‖ ^ 2 = ‖w₁‖ := by
      rw [← norm_pow, hS_sq o]
      dsimp only [g]; rw [hψ_o, norm_diskMob_zero]
    let F : UCov Ω w₀ → ℂ := fun p => diskMob b (S p)
    have hF_holo : IsHoloOnUCov F := hS_holo.comp_diskMob hS_lt1 hb_lt1
    have hF_lt1 : ∀ p, ‖F p‖ < 1 := fun p => norm_diskMob_lt_one hb_lt1 (hS_lt1 p)
    have hF_o : F o = 0 := diskMob_self
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ o.pt.1 o.pt.2
    have hcomp_deriv := (comparison_green_holo hΩ hΩc hΩP w₀ hψ_holo hψ_o hψ_norm hψ_lt1
      hF_holo hF_lt1 hF_o).2 r hr hsub
    -- Compute ‖deriv (uPull F o) o.pt.1‖ in terms of ‖deriv (uPull ψ o) o.pt.1‖!
    have hdψ : HasDerivAt (uPull ψ o hr hsub) (deriv (uPull ψ o hr hsub) o.pt.1) o.pt.1 :=
      ((hψ_holo o r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hdS : HasDerivAt (uPull S o hr hsub) (deriv (uPull S o hr hsub) o.pt.1) o.pt.1 :=
      ((hS_holo o r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hdg_from_ψ : HasDerivAt (uPull g o hr hsub)
        (((1 - ‖w₁‖ ^ 2 : ℝ) : ℂ) * deriv (uPull ψ o hr hsub) o.pt.1) o.pt.1 := by
      have hm := hasDerivAt_diskMob (b := w₁) (w := 0) hw₁_lt (by simp)
      simp only [mul_zero, sub_zero, one_pow, div_one] at hm
      have hm' : HasDerivAt (diskMob w₁) ((1 - ‖w₁‖ ^ 2 : ℝ) : ℂ) (uPull ψ o hr hsub o.pt.1) := by
        rwa [uPull_self, hψ_o]
      have hc : HasDerivAt (fun z => diskMob w₁ (uPull ψ o hr hsub z))
          (((1 - ‖w₁‖ ^ 2 : ℝ) : ℂ) * deriv (uPull ψ o hr hsub) o.pt.1) o.pt.1 :=
        hm'.comp o.pt.1 hdψ
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
      rw [uPull_apply g o hr hsub hz, uPull_apply ψ o hr hsub hz]
    have hdg_from_S : HasDerivAt (uPull g o hr hsub)
        (2 * b * deriv (uPull S o hr hsub) o.pt.1) o.pt.1 := by
      have hsq0 := hdS.fun_pow 2
      have hsq : HasDerivAt (fun z => (uPull S o hr hsub z) ^ 2)
          (2 * b * deriv (uPull S o hr hsub) o.pt.1) o.pt.1 := by
        refine hsq0.congr_deriv ?_
        rw [uPull_self]
        dsimp only [b]
        norm_num
      refine hsq.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
      rw [uPull_apply g o hr hsub hz, uPull_apply S o hr hsub hz, hS_sq]
    have hdF_from_S : HasDerivAt (uPull F o hr hsub)
        ((((1 - ‖b‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ b * b) ^ 2) *
          deriv (uPull S o hr hsub) o.pt.1) o.pt.1 := by
      have hm := hasDerivAt_diskMob (b := b) (w := b) hb_lt1 hb_lt1
      have hm' : HasDerivAt (diskMob b)
          (((1 - ‖b‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ b * b) ^ 2)
          (uPull S o hr hsub o.pt.1) := by rwa [uPull_self]
      have hc : HasDerivAt (fun z => diskMob b (uPull S o hr hsub z))
          ((((1 - ‖b‖ ^ 2 : ℝ) : ℂ) / (1 - starRingEnd ℂ b * b) ^ 2) *
            deriv (uPull S o hr hsub) o.pt.1) o.pt.1 :=
        hm'.comp o.pt.1 hdS
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
      rw [uPull_apply F o hr hsub hz, uPull_apply S o hr hsub hz]
    have hdg_eq : 2 * b * deriv (uPull S o hr hsub) o.pt.1 =
        ((1 - ‖w₁‖ ^ 2 : ℝ) : ℂ) * deriv (uPull ψ o hr hsub) o.pt.1 :=
      hdg_from_S.unique hdg_from_ψ
    have hnorm_g : 2 * ‖b‖ * ‖deriv (uPull S o hr hsub) o.pt.1‖ =
        (1 - ‖b‖ ^ 4) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ := by
      have h1 := congr_arg norm hdg_eq
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real] at h1
      have hw1_le : 0 ≤ 1 - ‖w₁‖ ^ 2 := by nlinarith [norm_nonneg w₁]
      rw [Real.norm_of_nonneg hw1_le, ← hb_sq] at h1
      have hpow : (‖b‖ ^ 2) ^ 2 = ‖b‖ ^ 4 := by ring
      rwa [hpow] at h1
    have hnorm_F : (1 - ‖b‖ ^ 2) * ‖deriv (uPull F o hr hsub) o.pt.1‖ =
        ‖deriv (uPull S o hr hsub) o.pt.1‖ := by
      have h1 := hdF_from_S.deriv
      have hbb : 1 - starRingEnd ℂ b * b = ((1 - ‖b‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [hbb] at h1
      have h1b_pos : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
      have h1b_ne : ((1 - ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1b_pos.ne'
      have hsimp : ((1 - ‖b‖ ^ 2 : ℝ) : ℂ) / ((1 - ‖b‖ ^ 2 : ℝ) : ℂ) ^ 2 =
          ((1 - ‖b‖ ^ 2 : ℝ) : ℂ)⁻¹ := by field_simp [h1b_ne]
      rw [hsimp] at h1
      have h2 := congr_arg norm h1
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg h1b_pos.le] at h2
      rw [h2, ← mul_assoc, mul_inv_cancel₀ h1b_pos.ne', one_mul]
    have h1b_pos : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have hψd_pos : 0 < ‖deriv (uPull ψ o hr hsub) o.pt.1‖ :=
      norm_pos_iff.mpr (hψ_deriv_o r hr hsub)
    have hfinal : 2 * ‖b‖ * (1 - ‖b‖ ^ 2) * ‖deriv (uPull F o hr hsub) o.pt.1‖ =
        (1 + ‖b‖ ^ 2) * (1 - ‖b‖ ^ 2) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ := by
      calc 2 * ‖b‖ * (1 - ‖b‖ ^ 2) * ‖deriv (uPull F o hr hsub) o.pt.1‖
          = 2 * ‖b‖ * ((1 - ‖b‖ ^ 2) * ‖deriv (uPull F o hr hsub) o.pt.1‖) := by ring
        _ = 2 * ‖b‖ * ‖deriv (uPull S o hr hsub) o.pt.1‖ := by rw [hnorm_F]
        _ = (1 - ‖b‖ ^ 4) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ := hnorm_g
        _ = (1 + ‖b‖ ^ 2) * (1 - ‖b‖ ^ 2) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ := by ring
    have hstrict : 2 * ‖b‖ < 1 + ‖b‖ ^ 2 := by nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hb_lt1.ne)]
    have hle_mul : 2 * ‖b‖ * (1 - ‖b‖ ^ 2) * ‖deriv (uPull F o hr hsub) o.pt.1‖ ≤
        2 * ‖b‖ * (1 - ‖b‖ ^ 2) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ :=
      mul_le_mul_of_nonneg_left hcomp_deriv (by positivity)
    have hlt_mul : 2 * ‖b‖ * (1 - ‖b‖ ^ 2) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ <
        (1 + ‖b‖ ^ 2) * (1 - ‖b‖ ^ 2) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ := by
      have hpos_rhs : 0 < (1 - ‖b‖ ^ 2) * ‖deriv (uPull ψ o hr hsub) o.pt.1‖ :=
        mul_pos h1b_pos hψd_pos
      nlinarith
    linarith
  exact ⟨ψ, hψ_holo, hψ_o, hψ_lt1, hψ_inj, hψ_surj, hψ_deriv⟩

end

end LandauH1

open Metric Complex Topology in
open Classical in
theorem OMA.solution : OMA.R_Bloch_landauConstant_lower_bound_R1.H1 := by
  intro f hf hf0 ⟨x, y, hx, hy, hxy⟩
  have hyx_ne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have h1728_ne : (1728 : ℂ) ≠ 0 := by norm_num
  let c : ℂ := (1728 : ℂ) / (y - x)
  have hc_ne : c ≠ 0 := div_ne_zero h1728_ne hyx_ne
  let A : ℂ → ℂ := fun w => c * (w - x)
  let Ainv : ℂ → ℂ := fun w => x + c⁻¹ * w
  have hA_inv : ∀ w, Ainv (A w) = w := fun w => by
    dsimp only [A, Ainv]
    rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul, add_sub_cancel]
  have hA_x : A x = 0 := by simp [A]
  have hA_y : A y = 1728 := by
    dsimp only [A, c]
    exact div_mul_cancel₀ (1728 : ℂ) hyx_ne
  let f₁ : ℂ → ℂ := fun z => A (f z)
  have hf₁_diff : DifferentiableOn ℂ f₁ (ball 0 1) := fun z hz =>
    (((hf z hz).sub_const x).const_mul c)
  have hf₁_deriv0 : deriv f₁ 0 = c := by
    have hdf0 : HasDerivAt f 1 0 := by
      rw [← hf0]; exact (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).hasDerivAt
    have hd : HasDerivAt f₁ (c * 1) 0 := by
      simpa [f₁, A] using (hdf0.sub_const x).const_mul c
    rw [hd.deriv, mul_one]
  let Ω : Set ℂ := f₁ '' ball 0 1
  have hΩ_open : IsOpen Ω := by
    have hana : AnalyticOnNhd ℂ f₁ (ball 0 1) := hf₁_diff.analyticOnNhd isOpen_ball
    rcases hana.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | hopen
    · exfalso
      have hev : f₁ =ᶠ[𝓝 (0 : ℂ)] fun _ => w :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)) hw
      have hd0 : deriv f₁ 0 = 0 := by rw [hev.deriv_eq, deriv_const]
      exact hc_ne (hf₁_deriv0.symm.trans hd0)
    · exact hopen (ball 0 1) subset_rfl isOpen_ball
  have hΩ_pc : IsPathConnected Ω :=
    ((convex_ball (0 : ℂ) 1).isPathConnected ⟨0, mem_ball_self zero_lt_one⟩).image' hf₁_diff.continuousOn
  have hΩ_PSet : Ω ⊆ LandauH1.PSet := by
    rintro w ⟨z, hz, rfl⟩ hmem
    rcases hmem with h0 | h1728
    · have hfx : f z = x := by
        have h1 := congr_arg Ainv h0
        rw [hA_inv, show Ainv 0 = x by simp [Ainv]] at h1
        exact h1
      exact hx ⟨z, hz, hfx⟩
    · have hfy : f z = y := by
        have h1 := congr_arg Ainv h1728
        rw [hA_inv] at h1
        have h2 : Ainv 1728 = y := by rw [← hA_y, hA_inv]
        exact h1.trans h2
      exact hy ⟨z, hz, hfy⟩
  let w₀ : Ω := ⟨f₁ 0, Set.mem_image_of_mem f₁ (mem_ball_self zero_lt_one)⟩
  obtain ⟨ψ, hψ_holo, hψ_o, hψ_lt1, hψ_inj, hψ_surj, hψ_deriv⟩ :=
    LandauH1.exists_biholo_UCov_ball hΩ_open hΩ_pc hΩ_PSet w₀
  -- Define inverse ψInv : ball 0 1 → UCov Ω w₀ and g₁ = uProjC ∘ ψInv.
  choose ψInv hψInv using fun w : ball (0 : ℂ) 1 => hψ_surj w.1 w.2
  have hψInv_left : ∀ p, ψInv ⟨ψ p, mem_ball_zero_iff.mpr (hψ_lt1 p)⟩ = p := fun p =>
    hψ_inj (hψInv ⟨ψ p, mem_ball_zero_iff.mpr (hψ_lt1 p)⟩)
  let g₁ : ℂ → ℂ := fun z => if hz : z ∈ ball (0 : ℂ) 1 then LandauH1.uProjC (ψInv ⟨z, hz⟩) else 0
  have hg₁_local : ∀ z₀ ∈ ball (0 : ℂ) 1,
      ∃ d : ℂ, d ≠ 0 ∧ HasStrictDerivAt g₁ d z₀ := by
    intro z₀ hz₀
    let p₀ := ψInv ⟨z₀, hz₀⟩
    have hp₀_ψ : ψ p₀ = z₀ := hψInv ⟨z₀, hz₀⟩
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ_open p₀.pt.1 p₀.pt.2
    have hψ_ana : AnalyticAt ℂ (LandauH1.uPull ψ p₀ hr hsub) p₀.pt.1 :=
      (hψ_holo p₀ r hr hsub).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    let dψ := deriv (LandauH1.uPull ψ p₀ hr hsub) p₀.pt.1
    have hdψ_ne : dψ ≠ 0 := hψ_deriv p₀ r hr hsub
    have hsd : HasStrictDerivAt (LandauH1.uPull ψ p₀ hr hsub) dψ p₀.pt.1 :=
      hψ_ana.hasStrictDerivAt
    let φ := (hsd.hasStrictFDerivAt_equiv hdψ_ne).toOpenPartialHomeomorph (LandauH1.uPull ψ p₀ hr hsub)
    have hp₀_src : p₀.pt.1 ∈ φ.source :=
      (hsd.hasStrictFDerivAt_equiv hdψ_ne).mem_toOpenPartialHomeomorph_source
    have hφ_p₀ : φ p₀.pt.1 = z₀ := by
      change LandauH1.uPull ψ p₀ hr hsub p₀.pt.1 = z₀
      rw [LandauH1.uPull_self, hp₀_ψ]
    have hz₀_tgt : z₀ ∈ φ.target := hφ_p₀ ▸ φ.map_source hp₀_src
    have hφ_symm_sd : HasStrictDerivAt φ.symm dψ⁻¹ z₀ := by
      have h1 := HasStrictDerivAt.of_local_left_inverse
        (φ.symm.continuousAt hz₀_tgt)
        (by rw [← hφ_p₀, φ.left_inv hp₀_src]; exact hsd)
        hdψ_ne
        (φ.eventually_right_inverse hz₀_tgt)
      exact h1
    have hev_g₁ : φ.symm =ᶠ[𝓝 z₀] g₁ := by
      have hsymm_z₀ : φ.symm z₀ = p₀.pt.1 := by rw [← hφ_p₀, φ.left_inv hp₀_src]
      have hopen_mem : φ.symm ⁻¹' ball p₀.pt.1 r ∈ 𝓝 z₀ :=
        (φ.symm.continuousAt hz₀_tgt) (isOpen_ball.mem_nhds (by rw [hsymm_z₀]; exact mem_ball_self hr))
      filter_upwards [isOpen_ball.mem_nhds hz₀, φ.open_target.mem_nhds hz₀_tgt, hopen_mem]
        with z hz hzt hzb
      have hψ_eq : ψ (LandauH1.uChart p₀ hr hsub (φ.symm z) hzb) = z := by
        rw [← LandauH1.uPull_apply ψ p₀ hr hsub hzb]
        exact φ.right_inv hzt
      have hinv_eq : ψInv ⟨z, hz⟩ = LandauH1.uChart p₀ hr hsub (φ.symm z) hzb :=
        hψ_inj ((hψInv ⟨z, hz⟩).trans hψ_eq.symm)
      dsimp only [g₁]
      rw [dif_pos hz, hinv_eq]
      rfl
    exact ⟨dψ⁻¹, inv_ne_zero hdψ_ne, hφ_symm_sd.congr_of_eventuallyEq hev_g₁⟩
  have hg₁_diff : DifferentiableOn ℂ g₁ (ball 0 1) := fun z hz => by
    obtain ⟨_, _, hd⟩ := hg₁_local z hz
    exact hd.hasDerivAt.differentiableAt.differentiableWithinAt
  have hg₁_deriv_ne : ∀ z ∈ ball (0 : ℂ) 1, deriv g₁ z ≠ 0 := fun z hz => by
    obtain ⟨d, hdne, hd⟩ := hg₁_local z hz
    rwa [hd.hasDerivAt.deriv]
  have hg₁_img : g₁ '' ball (0 : ℂ) 1 = Ω := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      dsimp only [g₁]
      rw [dif_pos hz]
      exact (ψInv ⟨z, hz⟩).pt.2
    · intro hw
      obtain ⟨γ, hγ⟩ := hΩ_pc.joinedIn w₀.1 w₀.2 w hw
      let γΩ : Path w₀ ⟨w, hw⟩ :=
        { toFun := fun t => ⟨γ t, hγ t⟩
          continuous_toFun := γ.continuous.subtype_mk _
          source' := Subtype.ext γ.source
          target' := Subtype.ext γ.target }
      let p : LandauH1.UCov Ω w₀ := ⟨⟨w, hw⟩, Path.Homotopic.Quotient.mk γΩ⟩
      have hψp : ψ p ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hψ_lt1 p)
      refine ⟨ψ p, hψp, ?_⟩
      dsimp only [g₁]
      rw [dif_pos hψp, hψInv_left p]
      rfl
  -- Lift f₁ : ball 0 1 → Ω to f̃₁ : C(ball 0 1, UCov Ω w₀) and apply Schwarz's lemma to h = ψ ∘ f̃₁.
  have : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self zero_lt_one⟩
  have : SimplyConnectedSpace (ball (0 : ℂ) 1) := SimplyConnectedSpace.ofContractible (ball (0 : ℂ) 1)
  have : LocallyPathConnectedSpace (ball (0 : ℂ) 1) := isOpen_ball.locallyPathConnectedSpace
  let f₁C : C(ball (0 : ℂ) 1, Ω) :=
    ⟨fun z => ⟨f₁ z.1, Set.mem_image_of_mem f₁ z.2⟩,
      (hf₁_diff.continuousOn.comp_continuous continuous_subtype_val fun z => z.2).subtype_mk _⟩
  let z₀B : ball (0 : ℂ) 1 := ⟨0, mem_ball_self zero_lt_one⟩
  obtain ⟨f₁Lift, ⟨hf₁Lift_0, hf₁Lift_comp⟩, -⟩ :=
    (LandauH1.isCoveringMap_uProj hΩ_open hΩ_pc w₀).existsUnique_continuousMap_lifts
      f₁C z₀B (LandauH1.uBase w₀) rfl
  have hf₁Lift_pt : ∀ z : ball (0 : ℂ) 1, (f₁Lift z).pt.1 = f₁ z.1 := fun z =>
    congr_arg Subtype.val (congr_fun hf₁Lift_comp z)
  let h : ℂ → ℂ := fun z => if hz : z ∈ ball (0 : ℂ) 1 then ψ (f₁Lift ⟨z, hz⟩) else 0
  have hh_0 : h 0 = 0 := by
    dsimp only [h]
    rw [dif_pos (mem_ball_self zero_lt_one)]
    change ψ (f₁Lift z₀B) = 0
    rw [hf₁Lift_0, hψ_o]
  have hh_maps : Set.MapsTo h (ball 0 1) (closedBall (h 0) 1) := by
    intro z hz
    rw [hh_0, mem_closedBall_zero_iff]
    dsimp only [h]
    rw [dif_pos hz]
    exact (hψ_lt1 _).le
  have hh_diff : DifferentiableOn ℂ h (ball 0 1) := by
    intro z hz
    let pz := f₁Lift ⟨z, hz⟩
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ_open pz.pt.1 pz.pt.2
    have hpre : f₁Lift ⁻¹' LandauH1.uBall pz hr hsub ∈ 𝓝 (⟨z, hz⟩ : ball (0 : ℂ) 1) :=
      ((LandauH1.isOpen_uBall hΩ_open pz hr hsub).preimage f₁Lift.continuous).mem_nhds
        (LandauH1.mem_uBall_self pz hr hsub)
    obtain ⟨δ, hδ, hδ_sub⟩ := Metric.mem_nhds_iff.mp hpre
    obtain ⟨ρ, hρ, hρ_sub⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
    let ε := min δ ρ
    have hε : 0 < ε := lt_min hδ hρ
    have hev : h =ᶠ[𝓝 z] fun w => LandauH1.uPull ψ pz hr hsub (f₁ w) := by
      filter_upwards [ball_mem_nhds z hε] with w hw
      have hwb : w ∈ ball (0 : ℂ) 1 := hρ_sub (lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _))
      have hwB : f₁Lift ⟨w, hwb⟩ ∈ LandauH1.uBall pz hr hsub :=
        hδ_sub (show dist (⟨w, hwb⟩ : ball (0 : ℂ) 1) ⟨z, hz⟩ < δ from
          lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _))
      have hf₁w : f₁ w ∈ ball pz.pt.1 r := by
        rw [← hf₁Lift_pt ⟨w, hwb⟩]; exact hwB.1
      dsimp only [h]
      rw [dif_pos hwb, LandauH1.uPull_apply ψ pz hr hsub hf₁w]
      have heq_chart : LandauH1.uChart pz hr hsub (f₁ w) hf₁w = f₁Lift ⟨w, hwb⟩ := by
        have h1 := hwB.2
        have h2 : (f₁Lift ⟨w, hwb⟩).pt.1 = f₁ w := hf₁Lift_pt ⟨w, hwb⟩
        exact LandauH1.uBall_injOn_uProjC pz hr hsub (LandauH1.uChart_mem_uBall pz hr hsub hf₁w) hwB h2.symm
      rw [heq_chart]
    have hcomp : DifferentiableAt ℂ (fun w => LandauH1.uPull ψ pz hr hsub (f₁ w)) z := by
      have hf₁_d : DifferentiableAt ℂ f₁ z := hf₁_diff.differentiableAt (isOpen_ball.mem_nhds hz)
      have hψ_d : DifferentiableAt ℂ (LandauH1.uPull ψ pz hr hsub) (f₁ z) := by
        rw [← hf₁Lift_pt ⟨z, hz⟩]
        exact (hψ_holo pz r hr hsub).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
      exact hψ_d.comp z hf₁_d
    exact (hcomp.congr_of_eventuallyEq hev).differentiableWithinAt
  have hh_deriv_le1 : ‖deriv h 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hh_diff hh_maps zero_lt_one
  have hg₁_comp_h : ∀ z ∈ ball (0 : ℂ) 1, g₁ (h z) = f₁ z := by
    intro z hz
    dsimp only [h, g₁]
    rw [dif_pos hz]
    have hmem : ψ (f₁Lift ⟨z, hz⟩) ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hψ_lt1 _)
    rw [dif_pos hmem, hψInv_left]
    exact hf₁Lift_pt ⟨z, hz⟩
  have hderiv_chain : deriv f₁ 0 = deriv g₁ 0 * deriv h 0 := by
    have hhd : HasDerivAt h (deriv h 0) 0 :=
      (hh_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).hasDerivAt
    have hg₁d : HasDerivAt g₁ (deriv g₁ 0) (h 0) := by
      rw [hh_0]
      exact (hg₁_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).hasDerivAt
    have hc : HasDerivAt (fun z => g₁ (h z)) (deriv g₁ 0 * deriv h 0) 0 :=
      (hg₁d.comp 0 hhd) |> fun h' => by simpa [Function.comp_def] using h'
    have hev : (fun z => g₁ (h z)) =ᶠ[𝓝 (0 : ℂ)] f₁ :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)) hg₁_comp_h
    exact (hc.congr_of_eventuallyEq hev.symm).deriv
  have hnorm_g₁_ge : ‖c‖ ≤ ‖deriv g₁ 0‖ := by
    rw [← hf₁_deriv0, hderiv_chain, norm_mul]
    nlinarith [norm_nonneg (deriv g₁ 0)]
  -- Undo affine normalization A to obtain g!
  let g : ℂ → ℂ := fun z => Ainv (g₁ z)
  have hg_deriv : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt g (c⁻¹ * deriv g₁ z) z := by
    intro z hz
    have hd1 : HasDerivAt g₁ (deriv g₁ z) z :=
      (hg₁_diff.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    simpa [g, Ainv] using (hd1.const_mul c⁻¹).const_add x
  refine ⟨g, fun z hz => (hg_deriv z hz).differentiableAt.differentiableWithinAt,
    fun z hz => by
      rw [(hg_deriv z hz).deriv]
      exact mul_ne_zero (inv_ne_zero hc_ne) (hg₁_deriv_ne z hz),
    ?_, ?_⟩
  · rw [(hg_deriv 0 (mem_ball_self zero_lt_one)).deriv, norm_mul, norm_inv]
    have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    calc (1 : ℝ) = ‖c‖⁻¹ * ‖c‖ := (inv_mul_cancel₀ hc_pos.ne').symm
      _ ≤ ‖c‖⁻¹ * ‖deriv g₁ 0‖ := mul_le_mul_of_nonneg_left hnorm_g₁_ge (inv_nonneg.mpr hc_pos.le)
  · rintro w ⟨z, hz, rfl⟩
    have hg₁z : g₁ z ∈ Ω := hg₁_img ▸ Set.mem_image_of_mem g₁ hz
    obtain ⟨u, hu, hfu⟩ := hg₁z
    refine ⟨u, hu, ?_⟩
    dsimp only [g]
    rw [← hfu]
    exact (hA_inv (f u)).symm
