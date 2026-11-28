import OMAStatements.S_mo_420625

-- Problem: Are the derivatives of the entropy power along the heat flow alternating in sign?
-- Upstream: statements/mo-420625.lean (declaration OMA.S_mo_420625.main)
-- Credit: @artnoage (the owner of the agents is credited as the solver)
--
-- Disproof at order k = 3 in dimension d = 1, for X uniform on two points at distance 1.
-- With overlap t = E log(1 + exp((x - 1/2)/t)) under N(0,t), the entropy power is
--   N t = 8 π e t exp(-2 overlap t),   0 < overlap t ≤ 2 exp(-1/(8t)),
-- and N is smooth on (0,∞) (the overlap is an analytic moment generating function after an
-- affine substitution). So N - 8πe t is negative and flat at 0. If the third derivative were
-- nonnegative on (0,∞), the second difference N(h) - 2N(2h) + N(3h) = h² N₂(η) would force the
-- second derivative N₂ to be nonnegative, so N would be convex, and convexity with flatness
-- gives N(1) ≥ 8πe, a contradiction.
-- Agents: Codex (counterexample, law, entropy identity, bound, smoothness), Antigravity
-- (positivity of the overlap, review), Claude Code (calculus lemma, assembly).


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace CodexEntropy

noncomputable def coordinate : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

noncomputable def law : Measure (EuclideanSpace ℝ (Fin 1)) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac (coordinate 1)

noncomputable def power : ℝ → ℝ := OMA.S_mo_420625.entropyPower 1 law

noncomputable def gauss (t x : ℝ) : ℝ :=
  (√(2 * Real.pi * t))⁻¹ * Real.exp (-(x ^ 2) / (2 * t))

noncomputable def softplus (u : ℝ) : ℝ := Real.log (1 + Real.exp u)

noncomputable def overlap (t : ℝ) : ℝ :=
  ∫ x : ℝ, gauss t x * softplus ((x - 1 / 2) / t)

noncomputable def mixture (t x : ℝ) : ℝ := (gauss t x + gauss t (1 - x)) / 2

lemma law_probability : IsProbabilityMeasure law where
  measure_univ := by
    norm_num [law, Measure.add_apply, Measure.smul_apply]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]

lemma law_secondMoment : Integrable (fun y ↦ ‖y‖ ^ 2) law := by
  exact ((integrable_dirac (by simp)).smul_measure (by finiteness)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by finiteness))

lemma gauss_eq_pdf {t : ℝ} (ht : 0 < t) :
    gauss t = gaussianPDFReal 0 t.toNNReal := by
  ext x
  simp [gauss, gaussianPDFReal, Real.coe_toNNReal _ ht.le, neg_div]

lemma gauss_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < gauss t x := by
  unfold gauss
  positivity

lemma gauss_integrable {t : ℝ} (ht : 0 < t) : Integrable (gauss t) := by
  rw [gauss_eq_pdf ht]
  exact integrable_gaussianPDFReal _ _

lemma gauss_integral {t : ℝ} (ht : 0 < t) : ∫ x, gauss t x = 1 := by
  rw [gauss_eq_pdf ht]
  exact integral_gaussianPDFReal_eq_one _ (by positivity)

lemma gauss_mul_sq_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦ gauss t x * x ^ 2) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / (2 * t))
    (by positivity) (s := 2) (by norm_num)).const_mul (√(2 * Real.pi * t))⁻¹
  refine hi.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  change (√(2 * Real.pi * t))⁻¹ * (x ^ (2 : ℝ) * Real.exp (-(1 / (2 * t)) * x ^ 2)) =
    gauss t x * x ^ 2
  rw [gauss, Real.rpow_two]
  rw [show -(1 / (2 * t)) * x ^ 2 = -(x ^ 2) / (2 * t) by ring]
  ring

lemma gauss_mul_sq_integral {t : ℝ} (ht : 0 < t) :
    ∫ x, gauss t x * x ^ 2 = t := by
  have hv : t.toNNReal ≠ 0 := by positivity
  have h := variance_fun_id_gaussianReal (μ := 0) (v := t.toNNReal)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simp only [sub_zero] at h
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simpa [gauss_eq_pdf ht, smul_eq_mul, Real.coe_toNNReal _ ht.le] using h

lemma reflection_integrable (f : ℝ → ℝ) (hf : Integrable f) :
    Integrable (fun x ↦ f (1 - x)) := by
  have hp := (volume : Measure ℝ).measurePreserving_sub_left 1
  exact (show Integrable f (Measure.map (fun x : ℝ ↦ 1 - x) volume) by
    rw [hp.map_eq]
    exact hf).comp_measurable hp.measurable

lemma reflection_integral (f : ℝ → ℝ) (hf : Integrable f) :
    ∫ x, f (1 - x) = ∫ x, f x := by
  have hp := (volume : Measure ℝ).measurePreserving_sub_left 1
  calc
    ∫ x, f (1 - x) = ∫ x, f x ∂Measure.map (fun x : ℝ ↦ 1 - x) volume :=
      (integral_map hp.measurable.aemeasurable (by
        rw [hp.map_eq]
        exact hf.aestronglyMeasurable)).symm
    _ = ∫ x, f x := by rw [hp.map_eq]

lemma gauss_reflection {t : ℝ} (ht : 0 < t) (x : ℝ) :
    gauss t (1 - x) = gauss t x * Real.exp ((x - 1 / 2) / t) := by
  simp only [gauss, mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

lemma softplus_nonneg (u : ℝ) : 0 ≤ softplus u := by
  exact Real.log_nonneg (by linarith [Real.exp_pos u])

lemma softplus_le_exp (u : ℝ) : softplus u ≤ Real.exp u := by
  unfold softplus
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp u by positivity)
  linarith

lemma overlap_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦ gauss t x * softplus ((x - 1 / 2) / t)) := by
  refine (reflection_integrable (gauss t) (gauss_integrable ht)).mono'
      (by unfold gauss softplus; fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gauss_pos ht x).le (softplus_nonneg _))]
  rw [gauss_reflection ht]
  exact mul_le_mul_of_nonneg_left (softplus_le_exp _) (gauss_pos ht x).le

lemma density_coordinate {t : ℝ} (ht : 0 < t) (x : ℝ) :
    OMA.S_mo_420625.density 1 law t (coordinate x) = mixture t x := by
  unfold OMA.S_mo_420625.density law mixture gauss
  rw [integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, smul_eq_mul, Nat.cast_one, sub_zero, ← map_sub,
      LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs]
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring,
      Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi * t), ← Real.sqrt_eq_rpow]
    rw [show (x - 1) ^ 2 = (1 - x) ^ 2 by ring]
    ring
  · exact (integrable_dirac (by exact enorm_lt_top)).smul_measure (by finiteness)
  · exact (integrable_dirac (by exact enorm_lt_top)).smul_measure (by finiteness)

lemma gauss_log_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.log (gauss t x) = -Real.log (√(2 * Real.pi * t)) - x ^ 2 / (2 * t) := by
  rw [gauss, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

lemma mixture_log_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.log (mixture t x) =
      Real.log (gauss t x) - Real.log 2 + softplus ((x - 1 / 2) / t) := by
  have hg := gauss_pos ht x
  rw [mixture, gauss_reflection ht,
    show gauss t x + gauss t x * Real.exp ((x - 1 / 2) / t) =
        gauss t x * (1 + Real.exp ((x - 1 / 2) / t)) by ring,
    Real.log_div (by positivity) (by norm_num),
    Real.log_mul hg.ne' (by positivity)]
  unfold softplus
  ring

lemma gauss_log_mixture_integral {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦ gauss t x * Real.log (mixture t x)) ∧
      (∫ x, gauss t x * Real.log (mixture t x)) =
        -Real.log (√(2 * Real.pi * t)) - 1 / 2 - Real.log 2 + overlap t := by
  let a := fun x ↦ gauss t x * (-Real.log (√(2 * Real.pi * t)))
  let b := fun x ↦ gauss t x * x ^ 2 / (2 * t)
  let c := fun x ↦ gauss t x * Real.log 2
  let d := fun x ↦ gauss t x * softplus ((x - 1 / 2) / t)
  have h1 : Integrable a := (gauss_integrable ht).mul_const _
  have h2 : Integrable b := (gauss_mul_sq_integrable ht).div_const _
  have h3 : Integrable c := (gauss_integrable ht).mul_const _
  have h4 : Integrable d := overlap_integrable ht
  have heq : (fun x ↦ gauss t x * Real.log (mixture t x)) = a - b - c + d := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, a, b, c, d]
    rw [mixture_log_eq ht, gauss_log_eq ht]
    ring
  rw [heq]
  refine ⟨((h1.sub h2).sub h3).add h4, ?_⟩
  rw [integral_add' ((h1.sub h2).sub h3) h4, integral_sub' (h1.sub h2) h3,
    integral_sub' h1 h2]
  dsimp only [a, b, c, d]
  rw [integral_mul_const, integral_mul_const, integral_div,
    gauss_integral ht, gauss_mul_sq_integral ht, overlap]
  field_simp

lemma mixture_entropy {t : ℝ} (ht : 0 < t) :
    OMA.S_mo_420625.entropy 1 law t =
      Real.log (√(2 * Real.pi * t)) + 1 / 2 + Real.log 2 - overlap t := by
  let f := fun x ↦ gauss t x * Real.log (mixture t x)
  have hf : Integrable f := (gauss_log_mixture_integral ht).1
  have hr := reflection_integrable f hf
  have symm (x : ℝ) : mixture t (1 - x) = mixture t x := by
    unfold mixture
    rw [show 1 - (1 - x) = x by ring, add_comm]
  unfold OMA.S_mo_420625.entropy
  rw [← coordinate.measurePreserving.integral_comp coordinate.toHomeomorph.measurableEmbedding]
  simp only [density_coordinate ht]
  have heq : (fun x ↦ mixture t x * Real.log (mixture t x)) =
      fun x ↦ (f x + f (1 - x)) / 2 := by
    funext x
    dsimp [f]
    rw [symm]
    unfold mixture
    ring
  rw [heq, integral_div, integral_add hf hr, reflection_integral f hf]
  dsimp [f]
  rw [(gauss_log_mixture_integral ht).2]
  ring

lemma power_identity {t : ℝ} (ht : 0 < t) :
    power t = 8 * Real.pi * Real.exp 1 * t * Real.exp (-2 * overlap t) := by
  unfold power OMA.S_mo_420625.entropyPower
  rw [mixture_entropy ht]
  norm_num only [Nat.cast_one, div_one]
  rw [show 2 * (Real.log (√(2 * Real.pi * t)) + 1 / 2 + Real.log 2 - overlap t) =
      (Real.log (√(2 * Real.pi * t)) + Real.log (√(2 * Real.pi * t))) +
        1 + (Real.log 2 + Real.log 2) + -2 * overlap t by ring]
  simp only [Real.exp_add]
  rw [Real.exp_log (by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ← sq, Real.sq_sqrt (by positivity)]
  ring

noncomputable def overlapWeight (u : ℝ) : ℝ := Real.exp (-u / 2) * softplus u

lemma overlapWeight_nonneg (u : ℝ) : 0 ≤ overlapWeight u :=
  mul_nonneg (Real.exp_pos _).le (softplus_nonneg _)

lemma overlapWeight_le (u : ℝ) : overlapWeight u ≤ 2 := by
  have he : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add, show u / 2 + u / 2 = u by ring]
  have hsq : 1 + Real.exp u ≤ (1 + Real.exp (u / 2)) ^ 2 := by
    rw [he]
    nlinarith [Real.exp_pos (u / 2)]
  have hlog := Real.log_le_log (by positivity) hsq
  rw [Real.log_pow] at hlog
  have h : softplus u ≤ 2 * Real.exp (u / 2) := by
    change Real.log (1 + Real.exp u) ≤ _
    have hb := softplus_le_exp (u / 2)
    unfold softplus at hb
    linarith
  unfold overlapWeight
  calc
    Real.exp (-u / 2) * softplus u ≤
        Real.exp (-u / 2) * (2 * Real.exp (u / 2)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 2 := by
      rw [mul_left_comm, ← Real.exp_add, show -u / 2 + u / 2 = 0 by ring,
        Real.exp_zero, mul_one]

noncomputable def overlapMeasure : Measure ℝ :=
  volume.withDensity (fun u ↦ ENNReal.ofReal (overlapWeight u))

noncomputable def overlapIntegral (t : ℝ) : ℝ :=
  ∫ u : ℝ, overlapWeight u * Real.exp (-(t / 2) * u ^ 2)

lemma overlap_measure_measurable : Measurable (fun u ↦ ENNReal.ofReal (overlapWeight u)) := by
  unfold overlapWeight softplus
  fun_prop

lemma overlapIntegral_repr (t : ℝ) :
    overlapIntegral t = mgf (fun u : ℝ ↦ u ^ 2) overlapMeasure (-(t / 2)) := by
  unfold overlapIntegral mgf overlapMeasure
  rw [integral_withDensity_eq_integral_toReal_smul overlap_measure_measurable (by simp)]
  simp only [ENNReal.toReal_ofReal (overlapWeight_nonneg _), smul_eq_mul]

lemma overlapIntegral_integrable {s : ℝ} (hs : s < 0) :
    Integrable (fun u : ℝ ↦ overlapWeight u * Real.exp (s * u ^ 2)) := by
  have hg : Integrable (fun u : ℝ ↦ Real.exp (s * u ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := -s) (by linarith))
  refine (hg.const_mul 2).mono' (by unfold overlapWeight softplus; fun_prop)
    (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (overlapWeight_nonneg _) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (overlapWeight_le _) (Real.exp_pos _).le

lemma overlap_substitution {t : ℝ} (ht : 0 < t) :
    overlap t =
      t * (√(2 * Real.pi * t))⁻¹ * Real.exp (-1 / (8 * t)) * overlapIntegral t := by
  let f := fun x ↦ gauss t x * softplus ((x - 1 / 2) / t)
  have hscale : (∫ u : ℝ, f (1 / 2 + t * u)) = t⁻¹ * overlap t := by
    calc
      (∫ u : ℝ, f (1 / 2 + t * u)) =
          t⁻¹ * (∫ x : ℝ, f (1 / 2 + x)) := by
        simpa [abs_of_pos (inv_pos.mpr ht), smul_eq_mul] using
          (Measure.integral_comp_mul_left (fun x : ℝ ↦ f (1 / 2 + x)) t)
      _ = _ := by rw [integral_add_left_eq_self f]; rfl
  have hpoint : (fun u : ℝ ↦ f (1 / 2 + t * u)) = fun u ↦
      ((√(2 * Real.pi * t))⁻¹ * Real.exp (-1 / (8 * t))) *
        (overlapWeight u * Real.exp (-(t / 2) * u ^ 2)) := by
    funext u
    have harg : (1 / 2 + t * u - 1 / 2) / t = u := by
      field_simp
      ring
    have hexp : -(1 / 2 + t * u) ^ 2 / (2 * t) =
        -1 / (8 * t) + -u / 2 + -(t / 2) * u ^ 2 := by
      field_simp
      ring
    dsimp only [f]
    rw [harg, gauss, hexp, Real.exp_add, Real.exp_add, overlapWeight]
    ring
  calc
    overlap t = t * ∫ u : ℝ, f (1 / 2 + t * u) := by rw [hscale]; field_simp
    _ = _ := by rw [hpoint, integral_const_mul, overlapIntegral]; ring

lemma overlap_le {t : ℝ} (ht : 0 < t) :
    overlap t ≤ 2 * Real.exp (-1 / (8 * t)) := by
  have hc : 0 < t / 2 := by positivity
  have hI : overlapIntegral t ≤ 2 * √(Real.pi / (t / 2)) := by
    unfold overlapIntegral
    rw [← integral_gaussian (t / 2), ← integral_const_mul]
    exact integral_mono (overlapIntegral_integrable (by linarith))
      ((integrable_exp_neg_mul_sq hc).const_mul 2)
      (fun u ↦ mul_le_mul_of_nonneg_right (overlapWeight_le _) (Real.exp_pos _).le)
  have hsqrt : √(2 * Real.pi * t) = t * √(Real.pi / (t / 2)) := by
    rw [show 2 * Real.pi * t = t ^ 2 * (Real.pi / (t / 2)) by field_simp,
      Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  have hs : √(Real.pi / (t / 2)) ≠ 0 := by positivity
  rw [overlap_substitution ht]
  calc
    _ ≤ t * (√(2 * Real.pi * t))⁻¹ * Real.exp (-1 / (8 * t)) *
        (2 * √(Real.pi / (t / 2))) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by rw [hsqrt]; field_simp

lemma overlapIntegral_contDiffAt {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 3 overlapIntegral t := by
  have hopen : Set.Iio 0 ⊆ integrableExpSet (fun u : ℝ ↦ u ^ 2) overlapMeasure := by
    intro s hs
    change Integrable (fun u : ℝ ↦ Real.exp (s * u ^ 2)) overlapMeasure
    unfold overlapMeasure
    rw [integrable_withDensity_iff_integrable_smul' overlap_measure_measurable (by simp)]
    simpa only [ENNReal.toReal_ofReal (overlapWeight_nonneg _), smul_eq_mul] using
      overlapIntegral_integrable hs
  have hx : -(t / 2) ∈ interior (integrableExpSet (fun u : ℝ ↦ u ^ 2) overlapMeasure) :=
    interior_maximal hopen isOpen_Iio (by show -(t / 2) < 0; linarith)
  have h := (analyticAt_mgf hx).contDiffAt (n := 3)
  have hc : ContDiffAt ℝ 3 (fun x : ℝ ↦ -(x / 2)) t := by fun_prop
  have heq : overlapIntegral = fun s : ℝ ↦ mgf (fun u : ℝ ↦ u ^ 2) overlapMeasure (-(s / 2)) :=
    funext overlapIntegral_repr
  rw [heq]
  exact ContDiffAt.fun_comp (f := fun s : ℝ ↦ -(s / 2))
    (g := mgf (fun u : ℝ ↦ u ^ 2) overlapMeasure) t h hc

lemma overlap_contDiffAt {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 3 overlap t := by
  have hi := overlapIntegral_contDiffAt ht
  have h : ContDiffAt ℝ 3 (fun s : ℝ ↦
      s * (√(2 * Real.pi * s))⁻¹ * Real.exp (-1 / (8 * s)) * overlapIntegral s) t := by
    fun_prop (disch := positivity)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact overlap_substitution hs

lemma power_contDiffAt {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 3 power t := by
  have hd := overlap_contDiffAt ht
  have h : ContDiffAt ℝ 3
      (fun s : ℝ ↦ 8 * Real.pi * Real.exp 1 * s * Real.exp (-2 * overlap s)) t := by
    fun_prop
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact power_identity hs

lemma overlap_pos {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun x : ℝ ↦ gauss t x * softplus ((x - 1 / 2) / t))) :
    0 < overlap t := by
  refine integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℝ)) ?_ hint ?_ ?_
  · unfold gauss softplus
    refine (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul ?_
    refine Continuous.log (continuous_const.add (Real.continuous_exp.comp (by fun_prop))) ?_
    intro x
    positivity
  · intro x
    unfold gauss softplus
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Real.exp_pos ((x - 1 / 2) / t)]))
  · unfold gauss softplus
    refine mul_ne_zero (by positivity) (ne_of_gt ?_)
    exact Real.log_pos (by linarith [Real.exp_pos (((0 : ℝ) - 1 / 2) / t)])

end CodexEntropy

namespace MO420625
open Set

lemma third_deriv_neg (N : ℝ → ℝ) (C b A : ℝ) (hb : 0 < b)
    (hsm : ∀ t > 0, ContDiffAt ℝ 3 N t)
    (hflat : ∀ t, 0 < t → t ≤ b → |N t - C * t| ≤ A * t ^ 3)
    (hneg : N b < C * b) : ∃ t, 0 < t ∧ iteratedDeriv 3 N t < 0 := by
  by_contra hcon
  have h3 : ∀ t, 0 < t → 0 ≤ deriv (deriv (deriv N)) t := by
    intro t ht
    by_contra h
    refine hcon ⟨t, ht, ?_⟩
    rw [not_le] at h
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h
  have hopen : IsOpen (Ioi (0:ℝ)) := isOpen_Ioi
  have hN : ContDiffOn ℝ 3 N (Ioi 0) := fun t ht => (hsm t ht).contDiffWithinAt
  have hd0 : DifferentiableOn ℝ N (Ioi 0) := hN.differentiableOn (by norm_num)
  have hN1 : ContDiffOn ℝ 2 (deriv N) (Ioi 0) := hN.deriv_of_isOpen hopen (by norm_num)
  have hd1 : DifferentiableOn ℝ (deriv N) (Ioi 0) := hN1.differentiableOn (by norm_num)
  have hN2 : ContDiffOn ℝ 1 (deriv (deriv N)) (Ioi 0) := hN1.deriv_of_isOpen hopen (by norm_num)
  have hd2 : DifferentiableOn ℝ (deriv (deriv N)) (Ioi 0) := hN2.differentiableOn (by norm_num)
  have hat0 : ∀ t, 0 < t → HasDerivAt N (deriv N t) t := fun t ht =>
    ((hd0 t ht).differentiableAt (hopen.mem_nhds ht)).hasDerivAt
  have hmono : MonotoneOn (deriv (deriv N)) (Ioi 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ioi 0) hd2.continuousOn (by rwa [interior_Ioi])
      (by rw [interior_Ioi]; exact fun x hx => h3 x hx)
  have hA : A ≤ |A| := le_abs_self A
  have hA0 : 0 ≤ |A| := abs_nonneg A
  -- second difference
  have hSD : ∀ h, 0 < h → ∃ η, h < η ∧ η < 3 * h ∧
      N h - 2 * N (2 * h) + N (3 * h) = h ^ 2 * deriv (deriv N) η := by
    intro h hh
    have hφd : ∀ x, 0 < x → HasDerivAt (fun x => N (x + h) - N x)
        (deriv N (x + h) - deriv N x) x := fun x hx =>
      ((hat0 (x + h) (by linarith)).comp_add_const x h).sub (hat0 x hx)
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun x => N (x + h) - N x)
      (fun x => deriv N (x + h) - deriv N x) (a := h) (b := 2 * h) (by linarith)
      (fun x hx => (hφd x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hφd x (by linarith [hx.1]))
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    obtain ⟨η, hη, hηe⟩ := exists_deriv_eq_slope (deriv N) (a := ξ) (b := ξ + h) (by linarith)
      (hd1.continuousOn.mono (fun x hx => mem_Ioi.2 (by linarith [hx.1])))
      (hd1.mono (fun x hx => mem_Ioi.2 (by linarith [hx.1])))
    refine ⟨η, by linarith [hξ.1, hη.1], by linarith [hξ.2, hη.2], ?_⟩
    have e1 : deriv N (ξ + h) - deriv N ξ
        = (N (2 * h + h) - N (2 * h) - (N (h + h) - N h)) / (2 * h - h) := hξe
    rw [hηe, e1]
    have e2 : ξ + h - ξ = h := by ring
    have e3 : 2 * h + h = 3 * h := by ring
    have e4 : h + h = 2 * h := by ring
    have e5 : 2 * h - h = h := by ring
    rw [e2, e3, e4, e5]
    field_simp
    ring
  -- second derivative is nonnegative
  have hg2 : ∀ t, 0 < t → 0 ≤ deriv (deriv N) t := by
    intro t0 ht0
    by_contra hc
    rw [not_le] at hc
    obtain ⟨c, hcdef⟩ : ∃ c, c = -(deriv (deriv N) t0) := ⟨_, rfl⟩
    have hcpos : 0 < c := by linarith
    have hden : 0 < 88 * (|A| + 1) := by positivity
    obtain ⟨h, hhdef⟩ : ∃ h, h = min (min (t0 / 3) (b / 3)) (c / (88 * (|A| + 1))) := ⟨_, rfl⟩
    have hh : 0 < h := by
      rw [hhdef]
      exact lt_min (lt_min (by linarith) (by linarith)) (div_pos hcpos hden)
    have h1 : h ≤ t0 / 3 := by rw [hhdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : h ≤ b / 3 := by rw [hhdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have h4 : h ≤ c / (88 * (|A| + 1)) := by rw [hhdef]; exact min_le_right _ _
    rw [le_div_iff₀ hden] at h4
    obtain ⟨η, hη1, hη2, hSDe⟩ := hSD h hh
    have hle : deriv (deriv N) η ≤ deriv (deriv N) t0 :=
      hmono (mem_Ioi.2 (by linarith)) (mem_Ioi.2 ht0) (by linarith)
    have f1 := hflat h hh (by linarith)
    have f2 := hflat (2 * h) (by linarith) (by linarith)
    have f3 := hflat (3 * h) (by linarith) (by linarith)
    rw [abs_le] at f1 f2 f3
    have p2 : (2 * h) ^ 3 = 8 * h ^ 3 := by ring
    have p3 : (3 * h) ^ 3 = 27 * h ^ 3 := by ring
    rw [p2] at f2
    rw [p3] at f3
    have lower : -(44 * A * h ^ 3) ≤ N h - 2 * N (2 * h) + N (3 * h) := by linarith [f1.1, f2.2, f3.1]
    have hh2 : 0 < h ^ 2 := by positivity
    have hh3 : 0 < h ^ 3 := by positivity
    have upper : N h - 2 * N (2 * h) + N (3 * h) ≤ -c * h ^ 2 := by
      rw [hSDe]
      have := mul_le_mul_of_nonneg_left hle hh2.le
      rw [hcdef]
      linarith
    have k1 : 44 * A * h ^ 3 ≤ 44 * (|A| + 1) * h ^ 3 := by nlinarith
    have k2 : h * (88 * (|A| + 1)) * h ^ 2 ≤ c * h ^ 2 := mul_le_mul_of_nonneg_right h4 hh2.le
    have k3 : 44 * (|A| + 1) * h ^ 3 = h * (88 * (|A| + 1)) * h ^ 2 / 2 := by ring
    have k4 : 0 < c * h ^ 2 := mul_pos hcpos hh2
    linarith
  have hconv : ConvexOn ℝ (Ioi 0) N :=
    convexOn_of_deriv2_nonneg (convex_Ioi 0) hd0.continuousOn (by rwa [interior_Ioi])
      (by rwa [interior_Ioi]) (by
        rw [interior_Ioi]
        intro x hx
        simpa using hg2 x hx)
  -- contradiction with N b < C b
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = C * b - N b := ⟨_, rfl⟩
  have hδ : 0 < δ := by linarith
  have hden : 0 < 34 * (|A| + 1) * (b + 1) := by positivity
  obtain ⟨h, hhdef⟩ : ∃ h, h = min (min (b / 4) 1) (δ / (34 * (|A| + 1) * (b + 1))) := ⟨_, rfl⟩
  have hh : 0 < h := by
    rw [hhdef]
    exact lt_min (lt_min (by linarith) one_pos) (div_pos hδ hden)
  have h1 : h ≤ b / 4 := by rw [hhdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have h2 : h ≤ 1 := by rw [hhdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have h4 : h ≤ δ / (34 * (|A| + 1) * (b + 1)) := by rw [hhdef]; exact min_le_right _ _
  rw [le_div_iff₀ hden] at h4
  have s := hconv.slope_mono_adjacent (x := h) (y := 2 * h) (z := b) (mem_Ioi.2 hh)
    (mem_Ioi.2 hb) (by linarith) (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at s
  have f1 := hflat h hh (by linarith)
  have f2 := hflat (2 * h) (by linarith) (by linarith)
  rw [abs_le] at f1 f2
  have p2 : (2 * h) ^ 3 = 8 * h ^ 3 := by ring
  rw [p2] at f2
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = N h - C * h := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = N (2 * h) - C * (2 * h) := ⟨_, rfl⟩
  have hh3 : 0 < h ^ 3 := by positivity
  have hh2 : 0 < h ^ 2 := by positivity
  -- δ h ≤ (a1 - a2)(b - 2h) - a2 h
  have key : δ * h ≤ (a1 - a2) * (b - 2 * h) - a2 * h := by
    have e : (N (2 * h) - N h) * (b - 2 * h) ≤ (N b - N (2 * h)) * (2 * h - h) := s
    have eN1 : N h = a1 + C * h := by rw [ha1]; ring
    have eN2 : N (2 * h) = a2 + C * (2 * h) := by rw [ha2]; ring
    have eNb : N b = C * b - δ := by rw [hδdef]; ring
    rw [eN1, eN2, eNb] at e
    nlinarith
  have B : 0 ≤ |A| * h ^ 3 := by positivity
  have b1 : a1 - a2 ≤ 9 * |A| * h ^ 3 := by
    rw [ha1, ha2]; nlinarith [f1.2, f2.1]
  have b1' : -(9 * |A| * h ^ 3) ≤ a1 - a2 := by
    rw [ha1, ha2]; nlinarith [f1.1, f2.2]
  have b2 : -a2 ≤ 8 * |A| * h ^ 3 := by rw [ha2]; nlinarith [f2.1]
  have hb2 : 0 ≤ b - 2 * h := by linarith
  have t1 : (a1 - a2) * (b - 2 * h) ≤ 9 * |A| * h ^ 3 * b := by
    calc (a1 - a2) * (b - 2 * h) ≤ 9 * |A| * h ^ 3 * (b - 2 * h) :=
          mul_le_mul_of_nonneg_right b1 hb2
      _ ≤ 9 * |A| * h ^ 3 * b := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t2 : -a2 * h ≤ 8 * |A| * h ^ 3 * 1 := by
    calc -a2 * h ≤ 8 * |A| * h ^ 3 * h := mul_le_mul_of_nonneg_right b2 hh.le
      _ ≤ 8 * |A| * h ^ 3 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- δ h ≤ 17 (|A|+1)(b+1) h^3 ≤ 17 (|A|+1)(b+1) h * h ≤ (δ/2) h
  have t3 : δ * h ≤ 17 * (|A| + 1) * (b + 1) * h ^ 3 := by nlinarith
  have t4 : h ^ 3 ≤ h * h := by nlinarith
  have t5 : 17 * (|A| + 1) * (b + 1) * h ^ 3 ≤ 17 * (|A| + 1) * (b + 1) * (h * h) :=
    mul_le_mul_of_nonneg_left t4 (by positivity)
  have t6 : h * (34 * (|A| + 1) * (b + 1)) * h ≤ δ * h := mul_le_mul_of_nonneg_right h4 hh.le
  have t7 : 0 < δ * h := mul_pos hδ hh
  nlinarith

/-- (I6) From the representation `N t = C t exp(-2 D t)` and the bounds on `D`. -/
lemma flat_of_repr (N D : ℝ → ℝ) (C b : ℝ) (hC : 0 < C) (hb : 0 < b)
    (hrep : ∀ t, 0 < t → N t = C * t * Real.exp (-2 * D t))
    (hpos : ∀ t, 0 < t → 0 < D t)
    (hD : ∀ t, 0 < t → D t ≤ 2 * Real.exp (-1 / (8 * t))) :
    (∀ t, 0 < t → t ≤ b → |N t - C * t| ≤ 512 * C * t ^ 3) ∧ N b < C * b := by
  constructor
  · intro t ht _
    have hDt := hpos t ht
    have hexp1 : 1 - 2 * D t ≤ Real.exp (-2 * D t) := by
      have := Real.add_one_le_exp (-2 * D t)
      linarith
    have hexp2 : Real.exp (-2 * D t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    -- exp(-x) ≤ 2 / x^2 with x = 1/(8t)
    have hx : 0 < 1 / (8 * t) := by positivity
    have hquad : (1 / (8 * t)) ^ 2 / 2 ≤ Real.exp (1 / (8 * t)) := by
      have := Real.quadratic_le_exp_of_nonneg hx.le
      linarith [hx]
    have hE : Real.exp (-1 / (8 * t)) ≤ 128 * t ^ 2 := by
      have e : Real.exp (-1 / (8 * t)) = (Real.exp (1 / (8 * t)))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [e, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
      calc (128 * t ^ 2)⁻¹ = (1 / (8 * t)) ^ 2 / 2 := by field_simp; ring
        _ ≤ Real.exp (1 / (8 * t)) := hquad
    have hDle : D t ≤ 256 * t ^ 2 := by linarith [hD t ht]
    rw [hrep t ht, abs_le]
    have hCt : 0 < C * t := mul_pos hC ht
    constructor
    · -- C t e - C t ≥ -C t * 2 D ≥ -512 C t^3
      have h1 : C * t * (1 - 2 * D t) ≤ C * t * Real.exp (-2 * D t) :=
        mul_le_mul_of_nonneg_left hexp1 hCt.le
      have h2 : C * t * (2 * D t) ≤ C * t * (2 * (256 * t ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCt.le
      nlinarith
    · have h1 : C * t * Real.exp (-2 * D t) ≤ C * t * 1 :=
        mul_le_mul_of_nonneg_left hexp2 hCt.le
      have : 0 ≤ 512 * C * t ^ 3 := by positivity
      linarith
  · rw [hrep b hb]
    have : Real.exp (-2 * D b) < 1 := Real.exp_lt_one_iff.2 (by linarith [hpos b hb])
    have hCb : 0 < C * b := mul_pos hC hb
    nlinarith

end MO420625

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_420625.main) := by
  intro hmain
  have hC : (0 : ℝ) < 8 * Real.pi * Real.exp 1 := by positivity
  obtain ⟨hflat, hneg⟩ := MO420625.flat_of_repr CodexEntropy.power CodexEntropy.overlap
    (8 * Real.pi * Real.exp 1) 1 hC one_pos
    (fun t ht => CodexEntropy.power_identity ht)
    (fun t ht => CodexEntropy.overlap_pos ht (CodexEntropy.overlap_integrable ht))
    (fun t ht => CodexEntropy.overlap_le ht)
  obtain ⟨t, ht, hlt⟩ := MO420625.third_deriv_neg CodexEntropy.power
    (8 * Real.pi * Real.exp 1) 1 (512 * (8 * Real.pi * Real.exp 1)) one_pos
    (fun t ht => CodexEntropy.power_contDiffAt ht) hflat hneg
  have h := hmain 1 CodexEntropy.law le_rfl CodexEntropy.law_probability
    CodexEntropy.law_secondMoment 3 (by norm_num) t ht
  have e : iteratedDeriv 3 (OMA.S_mo_420625.entropyPower 1 CodexEntropy.law) t
      = iteratedDeriv 3 CodexEntropy.power t := rfl
  rw [e] at h
  norm_num at h
  linarith
