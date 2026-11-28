import OMAStatements.S_mo_100119

-- Problem: smooth families of analytic functions (MathOverflow 100119)
-- Upstream: formal-conjectures statements/mo-100119.lean (declaration OMA.S_mo_100119.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Counterexample with m = n = 1: f(x, y) = x (1 - exp(-(1 + y^2) / x^2)) / (1 + y^2), f(0, y) = 0.

namespace OMA.P100119

open OMA.S_mo_100119

noncomputable def A (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) : ℝ := p.1 0

noncomputable def B (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) : ℝ :=
  (1 - expNegInvGlue ((p.1 0) ^ 2 / (1 + (p.2 0) ^ 2))) / (1 + (p.2 0) ^ 2)

noncomputable def fC (p : (Fin 1 → ℝ) × (Fin 1 → ℝ)) : ℝ := A p * B p

theorem den_ne (t : ℝ) : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity

theorem smoothA : ContDiff ℝ (⊤ : ℕ∞) A := by
  unfold A; fun_prop

theorem smoothB : ContDiff ℝ (⊤ : ℕ∞) B := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => p.1 0) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => 1 + (p.2 0) ^ 2) := by
    fun_prop
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (p.1 0) ^ 2 / (1 + (p.2 0) ^ 2)) :=
    (h1.pow 2).div h2 (fun p => den_ne _)
  have h4 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        expNegInvGlue ((p.1 0) ^ 2 / (1 + (p.2 0) ^ 2))) :=
    expNegInvGlue.contDiff.comp h3
  exact (contDiff_const.sub h4).div h2 (fun p => den_ne _)

theorem smooth : ContDiff ℝ (⊤ : ℕ∞) fC := smoothA.mul smoothB

noncomputable def E : ℂ → ℂ := dslope (fun u : ℂ => -Complex.exp (-u)) 0

theorem diffE : Differentiable ℂ E := by
  have h : DifferentiableOn ℂ (fun u : ℂ => -Complex.exp (-u)) Set.univ := by
    apply Differentiable.differentiableOn; fun_prop
  have := (Complex.differentiableOn_dslope (c := 0) Filter.univ_mem).2 h
  exact differentiableOn_univ.1 this

theorem E_ofReal (w : ℝ) (hw : w ≠ 0) : E (w : ℂ) = ((w⁻¹ * (1 - Real.exp (-w)) : ℝ) : ℂ) := by
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  unfold E
  rw [dslope_of_ne _ hw', slope]
  simp only [vsub_eq_sub, sub_zero, neg_zero, Complex.exp_zero, smul_eq_mul]
  push_cast
  ring

theorem analytic (x : Fin 1 → ℝ) : IsGloballyAnalyticAtZero (fun y => fC (x, y)) := by
  by_cases ha : x 0 = 0
  · have : (fun y : Fin 1 → ℝ => fC (x, y)) = fun _ => (0 : ℝ) := by
      funext y; simp [fC, A, ha]
    rw [this]
    exact ⟨_, hasFPowerSeriesOnBall_const⟩
  · set a : ℝ := x 0 with ha'
    let Φ : ℂ → ℂ := fun z => E ((1 + z ^ 2) / (a : ℂ) ^ 2) / (a : ℂ)
    have hΦd : Differentiable ℂ Φ := by
      have h1 : Differentiable ℂ (fun z : ℂ => (1 + z ^ 2) / (a : ℂ) ^ 2) := by fun_prop
      exact (diffE.comp h1).div_const _
    have hΦ := (hΦd.hasFPowerSeriesOnBall 0 (R := 1) one_pos).restrictScalars (𝕜 := ℝ)
    let u : (Fin 1 → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0)
    have hu0 : u 0 = 0 := map_zero u
    rw [← hu0] at hΦ
    have h2 := hΦ.compContinuousLinearMap
    rw [ENNReal.top_div_of_ne_top enorm_ne_top] at h2
    have h3 := Complex.reCLM.comp_hasFPowerSeriesOnBall h2
    have hfun : (fun y : Fin 1 → ℝ => fC (x, y)) = Complex.reCLM ∘ (Φ ∘ u) := by
     funext y
     have hw : ((1 + (y 0) ^ 2) / a ^ 2 : ℝ) ≠ 0 := by
       have := den_ne (y 0); positivity
     have hpos : 0 < a ^ 2 / (1 + (y 0) ^ 2) := by
       have := den_ne (y 0); positivity
     have hΦy : Φ (u y) = ((((1 + (y 0) ^ 2) / a ^ 2)⁻¹ *
         (1 - Real.exp (-((1 + (y 0) ^ 2) / a ^ 2))) / a : ℝ) : ℂ) := by
       have : (1 + (u y) ^ 2) / (a : ℂ) ^ 2 = (((1 + (y 0) ^ 2) / a ^ 2 : ℝ) : ℂ) := by
         simp [u]
       simp only [Φ]
       rw [this, E_ofReal _ hw]
       push_cast
       ring
     simp only [Function.comp_apply, hΦy, Complex.reCLM_apply, Complex.ofReal_re]
     simp only [fC, A, B, ← ha']
     rw [expNegInvGlue, if_neg (not_le.2 hpos)]
     have hd := den_ne (y 0)
     rw [inv_div]
     field_simp
    rw [hfun]
    exact ⟨_, h3⟩

noncomputable def cf (n : ℕ) : ℝ := if Even n then (-1) ^ (n / 2) else 0

theorem cf_even (k : ℕ) : cf (2 * k) = (-1) ^ k := by simp [cf]

theorem cf_odd (k : ℕ) : cf (2 * k + 1) = 0 := by simp [cf]

theorem cf_abs_le (n : ℕ) : |cf n| ≤ 1 := by
  unfold cf; split_ifs <;> simp

theorem hasSum_cf (y : ℝ) (hy : |y| < 1) :
    HasSum (fun n => cf n * y ^ n) (1 / (1 + y ^ 2)) := by
  have h1 : |(-y ^ 2)| < 1 := by
    rw [abs_neg, abs_pow]; exact pow_lt_one₀ (abs_nonneg y) hy two_ne_zero
  have hg := hasSum_geometric_of_abs_lt_one h1
  have he : HasSum (fun k => cf (2 * k) * y ^ (2 * k)) (1 / (1 + y ^ 2)) := by
    have e1 : (fun k => cf (2 * k) * y ^ (2 * k)) = fun k => (-y ^ 2) ^ k := by
      funext k
      rw [cf_even, pow_mul, ← mul_pow, neg_one_mul]
    have e2 : (1 / (1 + y ^ 2) : ℝ) = (1 - (-y ^ 2))⁻¹ := by
      rw [one_div, sub_neg_eq_add]
    rw [e1, e2]
    exact hg
  have ho : HasSum (fun k => cf (2 * k + 1) * y ^ (2 * k + 1)) 0 := by
    have e : (fun k => cf (2 * k + 1) * y ^ (2 * k + 1)) = fun _ => (0 : ℝ) := by
      funext k
      rw [cf_odd, zero_mul]
    rw [e]
    exact hasSum_zero
  have h3 := HasSum.even_add_odd (f := fun n => cf n * y ^ n) he ho
  rwa [add_zero] at h3

theorem notGlobal :
    ¬ IsGloballyAnalyticAtZero (fun y : Fin 1 → ℝ => 1 / (1 + (y 0) ^ 2)) := by
  rintro ⟨p, hp⟩
  let v : ℝ →L[ℝ] (Fin 1 → ℝ) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)
  have hv0 : v 0 = 0 := map_zero v
  rw [← hv0] at hp
  have h2 := hp.compContinuousLinearMap
  rw [ENNReal.top_div_of_ne_top enorm_ne_top] at h2
  have hG : ((fun y : Fin 1 → ℝ => 1 / (1 + (y 0) ^ 2)) ∘ v) = fun t : ℝ => 1 / (1 + t ^ 2) := by
    funext t; simp [v]
  rw [hG] at h2
  set P := p.compContinuousLinearMap v with hP
  let q : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ cf
  have hq : HasFPowerSeriesOnBall (fun t : ℝ => 1 / (1 + t ^ 2)) q 0 1 := by
    refine ⟨?_, one_pos, ?_⟩
    · have := FormalMultilinearSeries.le_radius_of_bound q 1 (r := 1) (fun n => by
        rw [FormalMultilinearSeries.ofScalars_norm]
        simpa using cf_abs_le n)
      simpa using this
    · intro y hy
      have hy1 : ‖y‖₊ < 1 := by
        simpa [Metric.eball, edist_zero_right, enorm_eq_nnnorm] using hy
      have hy2 : ‖y‖ < 1 := by exact_mod_cast hy1
      have hy' : |y| < 1 := by rwa [Real.norm_eq_abs] at hy2
      simp only [zero_add]
      have := hasSum_cf y hy'
      have hfe : (fun n => q n fun _ => y) = fun n => cf n * y ^ n := by
        funext n
        simp [q, mul_comm]
      rw [hfe]
      exact this
  have hPq : P = q := h2.hasFPowerSeriesAt.eq_formalMultilinearSeries hq.hasFPowerSeriesAt
  have hs := h2.hasSum (y := 2) (by simp)
  rw [hPq] at hs
  have hsum : Summable (fun n => cf n * (2 : ℝ) ^ n) := by
    have h5 := hs.summable
    have hfe : (fun n => q n fun _ => (2 : ℝ)) = fun n => cf n * (2 : ℝ) ^ n := by
      funext n
      simp [q, mul_comm]
    rw [hfe] at h5
    exact h5
  have ht := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht 1 one_pos
  have := hN (2 * N) (by omega)
  rw [Real.dist_eq, sub_zero, cf_even, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity)] at this
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * N) := one_le_pow₀ (by norm_num)
  linarith

theorem partial_eq (y : Fin 1 → ℝ) : partialX fC 0 0 y = 1 / (1 + (y 0) ^ 2) := by
  unfold partialX
  have hA : DifferentiableAt ℝ A ((0 : Fin 1 → ℝ), y) :=
    (smoothA.differentiable (by simp)).differentiableAt
  have hB : DifferentiableAt ℝ B ((0 : Fin 1 → ℝ), y) :=
    (smoothB.differentiable (by simp)).differentiableAt
  have hf : fC = fun p => A p * B p := rfl
  rw [hf, fderiv_fun_mul hA hB]
  have hAl : A = ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (Fin 1 → ℝ))) := by
    funext p; simp [A]
  have hA0 : A ((0 : Fin 1 → ℝ), y) = 0 := by simp [A]
  have hB0 : B ((0 : Fin 1 → ℝ), y) = 1 / (1 + (y 0) ^ 2) := by
    simp [B, expNegInvGlue.zero]
  rw [hA0, hB0, hAl, ContinuousLinearMap.fderiv]
  simp

end OMA.P100119

open OMA.P100119 OMA.S_mo_100119 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_100119.main) := by
  intro h
  have := h 1 1 fC smooth analytic 0 0
  apply notGlobal
  convert this using 2
  exact (partial_eq _).symm
