import FormalConjectures.Wikipedia.MeanValueProblem

-- Adapted from github.com/openai/math (commit 3344da59991ed94f9ba711217b29c1d760badfa6), lean/OAI/Analysis/StrictMeans (Koebe quarter theorem, area theorem route), (c) the OpenAI authors, Apache-2.0 licence.
-- The Smale argument (inverse branch via Mathlib covering-map lifting, then Koebe) is original to this file; Mathlib supplies Polynomial.isCoveringMapOn_eval.

namespace OAI

section Definitions
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower

end StrictInverseFirstPower
end Definitions

end OAI

namespace OAI

section
open Set MeasureTheory Complex
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

end
end StrictInverseFirstPower

end

end OAI

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma norm_sq_sub_complex (w a : ℂ) :
    ‖w - a‖ ^ 2 = ‖w‖ ^ 2 - 2 * (conj a * w).re + ‖a‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_sq_center_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DiffContOnCl ℂ f (ball c |r|)) :
    ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c r := by
  by_cases hr : r = 0
  · simp [hr]
  have hs : ContinuousOn f (sphere c |r|) := hf.2.mono (sphere_subset_closedBall.trans (by
    rw [closure_ball _ (abs_ne_zero.mpr hr)]))
  have hc : ContinuousOn (fun z => (conj (f c) * f z).re) (sphere c |r|) :=
    Complex.continuous_re.comp_continuousOn (hs.const_mul _)
  have hm : Real.circleAverage (fun z => (conj (f c) * f z).re) c r = ‖f c‖ ^ 2 := by
    have hd : DiffContOnCl ℂ (fun z => conj (f c) * f z) (ball c |r|) :=
      ⟨fun z hz => (hf.1 z hz).const_mul _, hf.2.const_mul _⟩
    calc
      _ = (Real.circleAverage (fun z => conj (f c) * f z) c r).re :=
        Complex.reCLM.circleAverage_comp_comm ((hs.const_mul _).circleIntegrable')
      _ = (conj (f c) * f c).re := by rw [hd.circleAverage]
      _ = ‖f c‖ ^ 2 := by
        simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re]
  have hineq := Real.circleAverage_mono
    ((hc.const_mul 2).sub (continuousOn_const (c := ‖f c‖ ^ 2))).circleIntegrable'
    (hs.norm.pow 2).circleIntegrable' (fun z _ => ?_)
  · rw [Real.circleAverage_sub] at hineq
    change Real.circleAverage ((2 : ℝ) • (fun z => (conj (f c) * f z).re)) c r -
      Real.circleAverage (fun _ => ‖f c‖ ^ 2) c r ≤ _ at hineq
    rw [Real.circleAverage_smul, Real.circleAverage_const, hm] at hineq
    · change 2 * ‖f c‖ ^ 2 - ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c r at hineq
      linarith
    · exact (hc.const_mul 2).circleIntegrable'
    · exact circleIntegrable_const _ _ _
  · have hn := sq_nonneg ‖f z - f c‖
    rw [norm_sq_sub_complex] at hn
    change 2 * (conj (f c) * f z).re - ‖f c‖ ^ 2 ≤ ‖f z‖ ^ 2
    linarith

lemma inverse_sq_conj_of_norm_eq {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    conj (z⁻¹ ^ 2) = z ^ 2 / (r : ℂ) ^ 4 := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; linarith
  have hc0 : conj z ≠ 0 := by simpa using hz0
  have hconj : conj z * z = (r : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz, Complex.ofReal_pow]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [map_pow, map_inv₀]
  apply (eq_div_iff (pow_ne_zero 4 hr0)).mpr
  calc
    (conj z)⁻¹ ^ 2 * (r : ℂ) ^ 4 = (conj z)⁻¹ ^ 2 * (conj z * z) ^ 2 := by
      rw [hconj]; ring
    _ = z ^ 2 := by field_simp

lemma norm_sq_inverse_sq_sub {z w : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    ‖w - z⁻¹ ^ 2‖ ^ 2 = ‖w‖ ^ 2 + r⁻¹ ^ 4 - 2 * r⁻¹ ^ 4 * (z ^ 2 * w).re := by
  rw [norm_sq_sub_complex, inverse_sq_conj_of_norm_eq hr hz, norm_pow, norm_inv, hz]
  rw [div_mul_eq_mul_div, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem circleAverage_norm_sq_pole {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball 0 r)) :
    Real.circleAverage (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) 0 r =
      Real.circleAverage (fun z => ‖g z‖ ^ 2) 0 r + r⁻¹ ^ 4 := by
  have hs : ContinuousOn g (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact hg.2.mono (sphere_subset_closedBall.trans (by rw [closure_ball _ hr.ne']))
  have hp : DiffContOnCl ℂ (fun z => z ^ 2 * g z) (ball 0 |r|) := by
    rw [abs_of_pos hr]
    exact ⟨fun z hz => ((differentiableAt_id.pow 2).differentiableWithinAt.mul (hg.1 z hz)),
      (continuousOn_id.pow 2).mul hg.2⟩
  have hpc : CircleIntegrable (fun z => z ^ 2 * g z) 0 r :=
    ((continuousOn_id.pow 2).mul hs).circleIntegrable'
  have hmean : Real.circleAverage (fun z => (z ^ 2 * g z).re) 0 r = 0 := by
    calc
      _ = (Real.circleAverage (fun z => z ^ 2 * g z) 0 r).re :=
        Complex.reCLM.circleAverage_comp_comm hpc
      _ = 0 := by rw [hp.circleAverage]; simp
  have hc : ContinuousOn (fun z => (z ^ 2 * g z).re) (sphere 0 |r|) :=
    Complex.continuous_re.comp_continuousOn ((continuousOn_id.pow 2).mul hs)
  rw [Real.circleAverage_congr_sphere (fun z hz =>
    norm_sq_inverse_sq_sub hr (by simpa only [mem_sphere, dist_zero_right, abs_of_pos hr] using hz))]
  rw [Real.circleAverage_fun_sub, Real.circleAverage_fun_add, Real.circleAverage_const]
  · have hm : Real.circleAverage (fun z => 2 * r⁻¹ ^ 4 * (z ^ 2 * g z).re) 0 r = 0 := by
      change Real.circleAverage ((2 * r⁻¹ ^ 4) • (fun z => (z ^ 2 * g z).re)) 0 r = 0
      rw [Real.circleAverage_smul, hmean, smul_zero]
    rw [hm, sub_zero]
  · exact (hs.norm.pow 2).circleIntegrable'
  · exact circleIntegrable_const _ _ _
  · exact ((hs.norm.pow 2).add continuousOn_const).circleIntegrable'
  · exact (hc.const_mul _).circleIntegrable'

theorem circleAverage_norm_sq_pole_lower {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball 0 r)) :
    r⁻¹ ^ 4 + ‖g 0‖ ^ 2 ≤ Real.circleAverage (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) 0 r := by
  rw [circleAverage_norm_sq_pole hr hg]
  have hm := norm_sq_center_le_circleAverage (r := r) (by simpa only [abs_of_pos hr] using hg)
  linarith

lemma circleAverage_eq_integral_neg_pi {f : ℂ → ℝ} {c : ℂ} {r : ℝ} :
    Real.circleAverage f c r = (2 * Real.pi)⁻¹ *
      ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi), smul_eq_mul,
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ)) (-Real.pi)]
  congr 2 <;> ring

lemma lintegral_circle_eq {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hf : ContinuousOn f (sphere c |r|)) (hpos : ∀ z ∈ sphere c |r|, 0 ≤ f z) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (f (circleMap c r θ))) =
      ENNReal.ofReal (2 * Real.pi * Real.circleAverage f c r) := by
  have hi : IntervalIntegrable (fun θ => f (circleMap c r θ)) volume (-Real.pi) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    exact hf.comp (continuous_circleMap c r).continuousOn (fun θ _ => circleMap_mem_sphere' c r θ)
  rw [circleAverage_eq_integral_neg_pi]
  have he : 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ)) =
      ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
  rw [he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact hi.1.mono_set (Ioo_subset_Ioc_self)
  · filter_upwards with θ
    exact hpos _ (circleMap_mem_sphere' c r θ)

lemma annulus_lintegral_polar_lower {f : ℂ → ℝ≥0∞} {r R : ℝ} (hr : 0 < r) (hf : Measurable f) :
    (∫⁻ ρ in Icc r R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal ρ * f (circleMap 0 ρ θ)) ≤
    ∫⁻ z in {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}, f z := by
  let A : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hpolar (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ in Icc r R ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * f (circleMap 0 p.1 p.2) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      apply le_of_eq
      symm
      apply lintegral_prod
      exact (ENNReal.measurable_ofReal.comp measurable_fst |>.mul
        (hf.comp (by fun_prop [circleMap]))).aemeasurable
    _ = ∫⁻ p : ℝ × ℝ in Icc r R ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * A.indicator f (Complex.polarCoord.symm p) := by
      apply setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [indicator_of_mem, hpolar]
      change r ≤ ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ ≤ R
      rw [Complex.norm_polarCoord_symm, abs_of_pos (lt_of_lt_of_le hr hp.1.1)]
      exact hp.1
    _ ≤ ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * A.indicator f (Complex.polarCoord.symm p) := by
      apply lintegral_mono_set
      exact prod_mono (fun ρ hρ => lt_of_lt_of_le hr hρ.1) Subset.rfl
    _ = ∫⁻ z in A, f z := by
      rw [← lintegral_indicator hA]
      exact Complex.lintegral_comp_polarCoord_symm _
    _ = _ := rfl

lemma radial_pole_integral {r R B : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    (∫ ρ in r..R, 2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + B ^ 2)) =
      Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) + Real.pi * B ^ 2 * (R ^ 2 - r ^ 2) := by
  have hz : (0 : ℝ) ∉ uIcc r R := notMem_uIcc_of_lt hr (hr.trans_le hR)
  have hi₁ := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := (-3 : ℤ)) (Or.inr hz)
  have hi₂ : IntervalIntegrable (fun ρ : ℝ => ρ) volume r R := continuous_id.intervalIntegrable _ _
  have he : (∫ ρ in r..R, 2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + B ^ 2)) =
      ∫ ρ in r..R, 2 * Real.pi * (ρ ^ (-3 : ℤ) + B ^ 2 * ρ) := by
    apply intervalIntegral.integral_congr
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := by intro he; subst ρ; exact hz hρ
    simp only [zpow_neg, zpow_ofNat]
    field_simp
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi₁ (hi₂.const_mul _), intervalIntegral.integral_const_mul,
    integral_zpow (Or.inr ⟨by norm_num, hz⟩), integral_id]
  norm_num
  ring

lemma pole_circle_density_lower {g : ℂ → ℂ} {ρ : ℝ} (hρpos : 0 < ρ)
    (hgd : DiffContOnCl ℂ g (ball 0 ρ)) :
    ENNReal.ofReal (2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2)) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal ρ *
        ENNReal.ofReal (‖g (circleMap 0 ρ θ) - (circleMap 0 ρ θ)⁻¹ ^ 2‖ ^ 2) := by
  have hs : ContinuousOn g (sphere 0 |ρ|) := by
    rw [abs_of_pos hρpos]
    exact hgd.2.mono (sphere_subset_closedBall.trans (by rw [closure_ball _ hρpos.ne']))
  have hsi : ContinuousOn (fun z : ℂ => z⁻¹ ^ 2) (sphere 0 |ρ|) :=
    (continuousOn_id.inv₀ (fun z hz => by
      intro he; change z = 0 at he; subst z; simp only [mem_sphere, dist_self, abs_of_pos hρpos] at hz; linarith)).pow 2
  have hsc : ContinuousOn (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) (sphere 0 |ρ|) :=
    (hs.sub hsi).norm.pow 2
  have he := lintegral_circle_eq hsc (fun _ _ => sq_nonneg _)
  rw [lintegral_const_mul' _ _ (by simp), he]
  rw [← ENNReal.ofReal_mul hρpos.le]
  apply ENNReal.ofReal_le_ofReal
  have hm := circleAverage_norm_sq_pole_lower hρpos hgd
  calc
    _ ≤ (2 * Real.pi * ρ) * Real.circleAverage (fun z => ‖g z - z⁻¹ ^ 2‖ ^ 2) 0 ρ :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem annulus_pole_area_lower {g : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : r ≤ R)
    (hg : DiffContOnCl ℂ g (ball 0 R)) :
    ENNReal.ofReal (Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) +
      Real.pi * ‖g 0‖ ^ 2 * (R ^ 2 - r ^ 2)) ≤
    ∫⁻ z in {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R},
      ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2) := by
  let A : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hgc : ContinuousOn g A := by
    apply hg.2.mono
    rw [closure_ball _ (hr.trans_le hR).ne']
    exact fun z hz => by simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hic : ContinuousOn (fun z : ℂ => z⁻¹ ^ 2) A :=
    (continuousOn_id.inv₀ (fun z hz => by intro he; change z = 0 at he; subst z; have hh : r ≤ ‖(0 : ℂ)‖ := hz.1; simpa using (hr.not_ge (by simpa using hh)))).pow 2
  let f : ℂ → ℝ≥0∞ := A.indicator (fun z => ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2))
  have hfc : ContinuousOn (fun z => ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2)) A :=
    ENNReal.continuous_ofReal.comp_continuousOn ((hgc.sub hic).norm.pow 2)
  have hfm : Measurable f := by
    have he : f = A.piecewise (fun z => ENNReal.ofReal (‖g z - z⁻¹ ^ 2‖ ^ 2)) (fun _ => 0) := by
      funext z
      by_cases hz : z ∈ A <;> simp [f, hz]
    rw [he]
    exact hfc.measurable_piecewise continuousOn_const hA
  have hp := annulus_lintegral_polar_lower (R := R) hr hfm
  have hpolar : (∫⁻ ρ in Icc r R, ENNReal.ofReal
      (2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2))) ≤
      ∫⁻ ρ in Icc r R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ρ * f (circleMap 0 ρ θ) := by
    apply setLIntegral_mono' measurableSet_Icc
    intro ρ hρ
    have hρpos : 0 < ρ := hr.trans_le hρ.1
    have hgd : DiffContOnCl ℂ g (ball 0 ρ) := hg.mono (ball_subset_ball hρ.2)
    have he (θ : ℝ) : f (circleMap 0 ρ θ) = ENNReal.ofReal (‖g (circleMap 0 ρ θ) - (circleMap 0 ρ θ)⁻¹ ^ 2‖ ^ 2) := by
      apply indicator_of_mem
      change r ≤ ‖circleMap 0 ρ θ‖ ∧ ‖circleMap 0 ρ θ‖ ≤ R
      rw [circleMap_zero, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos hρpos]
      exact hρ
    simp_rw [he]
    exact pole_circle_density_lower hρpos hgd
  have hintegrable : IntegrableOn (fun ρ : ℝ => 2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2)) (Icc r R) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_const.mul continuousOn_id).mul
      (((continuousOn_id.inv₀ (fun ρ hρ => (hr.trans_le hρ.1).ne')).pow 4).add continuousOn_const)
  have hid : (∫⁻ ρ in Icc r R, ENNReal.ofReal
      (2 * Real.pi * ρ * (ρ⁻¹ ^ 4 + ‖g 0‖ ^ 2))) =
      ENNReal.ofReal (Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) +
        Real.pi * ‖g 0‖ ^ 2 * (R ^ 2 - r ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR, radial_pole_integral hr hR]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
      have hρpos : 0 < ρ := hr.trans_le hρ.1
      positivity
  rw [hid] at hpolar
  calc
    _ ≤ _ := hpolar.trans hp
    _ = _ := by
      apply setLIntegral_congr_fun hA
      exact fun z hz => indicator_of_mem hz _

theorem re_le_of_forall_mem_frontier_re_le {U : Set ℂ} {f : ℂ → ℂ} {C : ℝ}
    (hb : Bornology.IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hc : ∀ z ∈ frontier U, (f z).re ≤ C) {z : ℂ} (hz : z ∈ closure U) :
    (f z).re ≤ C := by
  have he := Complex.differentiable_exp.comp_diffContOnCl hf
  have hn : ‖Complex.exp (f z)‖ ≤ Real.exp C :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hb he
      (fun w hw => by simpa only [Function.comp_apply, Complex.norm_exp] using Real.exp_le_exp.mpr (hc w hw)) hz
  simpa only [Complex.norm_exp, Real.exp_le_exp] using hn

theorem norm_realLinear_le_of_frontier {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {C : ℝ}
    (hb : Bornology.IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hc : ∀ z ∈ frontier U, ‖f z - c * conj (f z)‖ ≤ C)
    {z : ℂ} (hz : z ∈ closure U) (hC : 0 ≤ C) :
    ‖f z - c * conj (f z)‖ ≤ C := by
  let t := f z - c * conj (f z)
  let a := conj t - conj c * t
  have ident (w : ℂ) : (a * w).re = (conj t * (w - c * conj w)).re := by
    simp only [a, sub_mul, mul_sub, sub_re, mul_re, mul_im, conj_re, conj_im]
    ring
  have hbd : ∀ w ∈ frontier U, (a * f w).re ≤ ‖t‖ * C := by
    intro w hw
    rw [ident]
    calc
      (conj t * (f w - c * conj (f w))).re ≤ ‖conj t * (f w - c * conj (f w))‖ :=
        Complex.re_le_norm _
      _ = ‖t‖ * ‖f w - c * conj (f w)‖ := by rw [norm_mul, norm_conj]
      _ ≤ ‖t‖ * C := mul_le_mul_of_nonneg_left (hc w hw) (norm_nonneg _)
  have hd : DiffContOnCl ℂ (fun w => a * f w) U := ⟨fun w hw => (hf.1 w hw).const_mul a, hf.2.const_mul a⟩
  have hh := re_le_of_forall_mem_frontier_re_le hb hd hbd hz
  rw [ident] at hh
  change (conj t * t).re ≤ ‖t‖ * C at hh
  have he : (conj t * t).re = ‖t‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re]
  rw [he] at hh
  change ‖t‖ ≤ C
  nlinarith [norm_nonneg t]

theorem det_complexDerivative (a : ℂ) :
    (a • (1 : ℂ →L[ℝ] ℂ)).det = ‖a‖ ^ 2 := by
  change LinearMap.det (a • (1 : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two,
    ← Complex.normSq_eq_norm_sq]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Complex.normSq_apply]

theorem holomorphic_area {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ f z) (hi : InjOn f s) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖ ^ 2)) = volume (f '' s) := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  have h := lintegral_abs_det_fderiv_eq_addHaar_image volume hs hreal hi
  simpa only [det_complexDerivative, abs_sq] using h

def ellipseLinear (c : ℂ) : ℂ →L[ℝ] ℂ :=
  1 + c • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

lemma ellipseLinear_apply (c z : ℂ) : ellipseLinear c z = z + c * conj z := rfl

lemma det_ellipseLinear (c : ℂ) :
    (ellipseLinear c).det = 1 - ‖c‖ ^ 2 := by
  change LinearMap.det (ellipseLinear c : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two,
    ← Complex.normSq_eq_norm_sq]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ellipseLinear_apply, Complex.normSq_apply]
  ring

lemma norm_ellipseLinear_lower (c z : ℂ) :
    (1 - ‖c‖) * ‖z‖ ≤ ‖ellipseLinear c z‖ := by
  have hn := norm_sub_le (ellipseLinear c z) (c * conj z)
  rw [ellipseLinear_apply, add_sub_cancel_right, norm_mul, norm_conj] at hn
  rw [ellipseLinear_apply]
  nlinarith

def ellipseInverse (c z : ℂ) : ℂ := (z - c * conj z) / (1 - ‖c‖ ^ 2 : ℝ)

lemma ellipseLinear_inverse {c : ℂ} (hc : ‖c‖ < 1) (z : ℂ) :
    ellipseLinear c (ellipseInverse c z) = z := by
  have hd : (1 - ‖c‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg c]
  have hd' : ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hcconj : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [ellipseLinear_apply, ellipseInverse, map_div₀, map_sub, map_mul,
    Complex.conj_conj, Complex.conj_ofReal]
  field_simp [hd']
  push_cast at hcconj ⊢
  linear_combination -z * hcconj

lemma norm_ellipseInverse_le_two {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) (z : ℂ) :
    ‖ellipseInverse c z‖ ≤ 2 * ‖z‖ := by
  have hn := norm_ellipseLinear_lower c (ellipseInverse c z)
  rw [ellipseLinear_inverse (by linarith) z] at hn
  have hnonneg := norm_nonneg (ellipseInverse c z)
  nlinarith

lemma ellipseInverse_add (c z w : ℂ) :
    ellipseInverse c (z + w) = ellipseInverse c z + ellipseInverse c w := by
  simp only [ellipseInverse, map_add]
  ring

lemma ellipseInverse_linear {c : ℂ} (hc : ‖c‖ < 1) (z : ℂ) :
    ellipseInverse c (ellipseLinear c z) = z := by
  have h := ellipseLinear_inverse hc (ellipseLinear c z)
  have hn := norm_ellipseLinear_lower c (ellipseInverse c (ellipseLinear c z) - z)
  rw [map_sub, h, sub_self, norm_zero] at hn
  have hpos : 0 < 1 - ‖c‖ := sub_pos.mpr hc
  have he : ‖ellipseInverse c (ellipseLinear c z) - z‖ = 0 := by
    nlinarith [norm_nonneg (ellipseInverse c (ellipseLinear c z) - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma volume_ellipse_le {c : ℂ} (hc : ‖c‖ ≤ 1) (s : Set ℂ) :
    volume (ellipseLinear c '' s) ≤ volume s := by
  rw [Measure.addHaar_image_continuousLinearMap]
  have hd : LinearMap.det (ellipseLinear c : ℂ →ₗ[ℝ] ℂ) = 1 - ‖c‖ ^ 2 := det_ellipseLinear c
  rw [hd, abs_of_nonneg (by nlinarith [norm_nonneg c])]
  calc
    ENNReal.ofReal (1 - ‖c‖ ^ 2) * volume s ≤ 1 * volume s := by
      gcongr
      exact_mod_cast (by nlinarith [sq_nonneg ‖c‖] : 1 - ‖c‖ ^ 2 ≤ 1)
    _ = _ := one_mul _

lemma norm_ellipseInverse_eq {c : ℂ} (hc : ‖c‖ < 1) (z : ℂ) :
    ‖ellipseInverse c z‖ = ‖z - c * conj z‖ / (1 - ‖c‖ ^ 2) := by
  have hd : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  simp only [ellipseInverse, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hd]

theorem ellipse_max_annulus {f : ℂ → ℂ} {r R C : ℝ} {c : ℂ}
    (hc : ‖c‖ < 1) (hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f {z | r < ‖z‖ ∧ ‖z‖ < R})
    (hfc : ContinuousOn f {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R → ‖ellipseInverse c (f z)‖ ≤ C)
    {z : ℂ} (hz : r ≤ ‖z‖ ∧ ‖z‖ ≤ R) : ‖ellipseInverse c (f z)‖ ≤ C := by
  by_cases hi : r < ‖z‖ ∧ ‖z‖ < R
  · let U : Set ℂ := {z | r < ‖z‖ ∧ ‖z‖ < R}
    have hcl : closure U ⊆ {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} :=
      closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩)
        ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    have hb : Bornology.IsBounded U :=
      (isBounded_ball (x := (0 : ℂ)) (r := R)).subset (fun w hw => by
        simpa only [mem_ball, dist_zero_right] using hw.2)
    have hfront : ∀ w ∈ frontier U, ‖w‖ = r ∨ ‖w‖ = R := by
      intro w hw
      rcases frontier_inter_subset {w : ℂ | r < ‖w‖} {w : ℂ | ‖w‖ < R} hw with hw | hw
      · exact Or.inl ((frontier_lt_subset_eq continuous_const continuous_norm hw.1).symm)
      · exact Or.inr (frontier_lt_subset_eq continuous_norm continuous_const hw.2)
    have hD : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
    have hm := norm_realLinear_le_of_frontier hb (⟨hf, hfc.mono hcl⟩ : DiffContOnCl ℂ f U)
      (c := c) (C := C * (1 - ‖c‖ ^ 2)) (fun w hw => ?_)
      (subset_closure hi) (mul_nonneg hC hD.le)
    · rw [norm_ellipseInverse_eq hc]
      exact (div_le_iff₀ hD).mpr hm
    · exact (div_le_iff₀ hD).mp (by simpa only [norm_ellipseInverse_eq hc] using hbd w (hfront w hw))
  · apply hbd z
    push Not at hi
    by_cases he : ‖z‖ = r
    · exact Or.inl he
    · exact Or.inr (le_antisymm hz.2 (hi (lt_of_le_of_ne hz.1 (Ne.symm he))))

theorem volume_image_annulus_le {f : ℂ → ℂ} {r R C : ℝ} {c : ℂ}
    (hc : ‖c‖ < 1) (hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f {z | r < ‖z‖ ∧ ‖z‖ < R})
    (hfc : ContinuousOn f {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R → ‖ellipseInverse c (f z)‖ ≤ C) :
    volume (f '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}) ≤ ENNReal.ofReal (Real.pi * C ^ 2) := by
  have hs : f '' {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} ⊆ ellipseLinear c '' closedBall 0 C := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨ellipseInverse c (f z), ?_, ellipseLinear_inverse hc _⟩
    simpa only [mem_closedBall, dist_zero_right] using ellipse_max_annulus hc hC hf hfc hbd hz
  calc
    _ ≤ volume (ellipseLinear c '' closedBall 0 C) := measure_mono hs
    _ ≤ volume (closedBall 0 C) := volume_ellipse_le hc.le _
    _ = ENNReal.ofReal (Real.pi * C ^ 2) := by
      rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hC]
      have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
        rw [← NNReal.coe_real_pi]
        simp only [ENNReal.ofReal_coe_nnreal]
      rw [hpi, mul_comm]

lemma ellipse_pole_identity {z b : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    ellipseLinear (b * (r : ℂ) ^ 2) z⁻¹ = z⁻¹ + b * z := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; linarith
  have hc0 : conj z ≠ 0 := by simpa using hz0
  have hn : conj z * z = (r : ℂ) ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz, Complex.ofReal_pow]
  rw [ellipseLinear_apply, map_inv₀, ← hn]
  field_simp

lemma ellipse_pole_boundary {h : ℂ → ℂ} {b z : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hz : ‖z‖ = r) (hc : ‖b * (r : ℂ) ^ 2‖ ≤ 1 / 2)
    (hh : ‖h z - b * z‖ ≤ ε * r) :
    ‖ellipseInverse (b * (r : ℂ) ^ 2) (z⁻¹ + h z)‖ ≤ r⁻¹ + 2 * ε * r := by
  have he : z⁻¹ + h z = ellipseLinear (b * (r : ℂ) ^ 2) z⁻¹ + (h z - b * z) := by
    rw [ellipse_pole_identity hr hz]
    ring
  rw [he, ellipseInverse_add, ellipseInverse_linear (by linarith)]
  calc
    _ ≤ ‖z⁻¹‖ + ‖ellipseInverse (b * (r : ℂ) ^ 2) (h z - b * z)‖ := norm_add_le _ _
    _ ≤ r⁻¹ + 2 * ‖h z - b * z‖ := by
      rw [norm_inv, hz]
      exact add_le_add (le_refl _) (norm_ellipseInverse_le_two hc _)
    _ ≤ _ := by linarith

lemma deriv_diffContOnCl_inner {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h (ball 0 1))
    {R : ℝ} (hR : R < 1) : DiffContOnCl ℂ (deriv h) (ball 0 R) := by
  have ha := (hd.analyticOnNhd isOpen_ball).deriv
  refine ⟨ha.differentiableOn.mono (ball_subset_ball hR.le), ha.continuousOn.mono ?_⟩
  exact (closure_ball_subset_closedBall).trans (closedBall_subset_ball hR)

lemma pole_annulus_comparison {h : ℂ → ℂ} {r R C : ℝ} {c : ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    (hr : 0 < r) (hrR : r ≤ R) (hR : R < 1) (hc : ‖c‖ < 1) (hC : 0 ≤ C)
    (hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R →
      ‖ellipseInverse c (z⁻¹ + h z)‖ ≤ C) :
    Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2) + Real.pi * ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2) ≤
      Real.pi * C ^ 2 := by
  let A : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hsub : A ⊆ ball 0 1 \ {0} := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using hz.2.trans_lt hR
    · intro he
      have he' : z = 0 := he
      have hh := hz.1
      rw [he', norm_zero] at hh
      linarith
  have hder (z : ℂ) (hz : z ∈ A) :
      HasDerivAt (fun z => z⁻¹ + h z) (deriv h z - z⁻¹ ^ 2) z := by
    have hd' := (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hz).1)).hasDerivAt
    have hn : z ≠ 0 := fun he => (hsub hz).2 he
    have hsum : HasDerivAt (fun w : ℂ => w⁻¹ + h w) (-(z ^ 2)⁻¹ + deriv h z) z :=
      (hasDerivAt_inv hn).add hd'
    convert hsum using 1; simp [inv_pow, sub_eq_add_neg, add_comm]
  have hdG : ∀ z ∈ A, DifferentiableAt ℂ (fun z => z⁻¹ + h z) z :=
    fun z hz => (hder z hz).differentiableAt
  have hU : {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} ⊆ A := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hv := volume_image_annulus_le hc hC
    (fun z hz => (hdG z (hU hz)).differentiableWithinAt)
    (fun z hz => (hdG z hz).continuousAt.continuousWithinAt) hbd
  have hl := annulus_pole_area_lower hr hrR (deriv_diffContOnCl_inner hd hR)
  have he : (∫⁻ z in A, ENNReal.ofReal (‖deriv h z - z⁻¹ ^ 2‖ ^ 2)) =
      volume ((fun z => z⁻¹ + h z) '' A) := by
    rw [← holomorphic_area hA hdG (hi.mono hsub)]
    apply setLIntegral_congr_fun hA
    intro z hz
    dsimp only
    rw [(hder z hz).deriv]
  rw [he] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hl.trans hv)

lemma pole_area_small_radius {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    {R ε : ℝ} (hRpos : 0 < R) (hR : R < 1) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2) ≤ R⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2 := by
  have hd0 := hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), ‖h z - deriv h 0 * z‖ ≤ ε * ‖z‖ := by
    simpa only [h0, sub_zero, smul_eq_mul, mul_comm] using hd0.hasDerivAt.isLittleO.bound hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp he
  have hcont : ContinuousOn (fun z => z⁻¹ + h z) (sphere 0 R) := by
    intro z hz
    have hzR : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hzR; linarith
    exact ((continuousAt_inv₀ hz0).add
      (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa [mem_ball, dist_zero_right, hzR] using hR))).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hcont
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id'.mpr nhdsWithin_le_nhds
  have hts : Tendsto (fun r : ℝ => ‖deriv h 0‖ * r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert ht.pow 2 |>.const_mul ‖deriv h 0‖ using 1; simp
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖deriv h 0‖ * r ^ 2 < 1 / 2 :=
    hts.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have houter : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * M ≤ r⁻¹ :=
    tendsto_inv_nhdsGT_zero.eventually_ge_atTop _
  filter_upwards [eventually_mem_nhdsWithin, ht.eventually (gt_mem_nhds hRpos),
    ht.eventually (gt_mem_nhds hδ), hsmall, houter] with r hr hrR hrδ hsmall houter
  have hrpos : 0 < r := hr
  let c : ℂ := deriv h 0 * (r : ℂ) ^ 2
  have hc : ‖c‖ ≤ 1 / 2 := by
    dsimp [c]
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    exact hsmall.le
  have hC : 0 ≤ r⁻¹ + 2 * ε * r := by positivity
  have hbd : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R →
      ‖ellipseInverse c (z⁻¹ + h z)‖ ≤ r⁻¹ + 2 * ε * r := by
    intro z hz
    rcases hz with hz | hz
    · apply ellipse_pole_boundary hrpos hz hc
      have hb := hδbound (y := z) (by simpa only [dist_zero_right, hz] using hrδ)
      simpa only [hz] using hb
    · calc
        _ ≤ 2 * ‖z⁻¹ + h z‖ := norm_ellipseInverse_le_two hc _
        _ ≤ 2 * M := by
          gcongr
          exact hM z (by simpa only [mem_sphere, dist_zero_right] using hz)
        _ ≤ r⁻¹ + 2 * ε * r := by nlinarith
  have harea := pole_annulus_comparison hd hi hrpos hrR.le hR (by linarith : ‖c‖ < 1) hC hbd
  have hsq : (r⁻¹ + 2 * ε * r) ^ 2 = r⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2 := by
    field_simp
    ring
  rw [hsq] at harea
  have hm : Real.pi * (r⁻¹ ^ 2 - R⁻¹ ^ 2 + ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2)) ≤
      Real.pi * (r⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2) := by
    nlinarith only [harea]
  have hm' := (mul_le_mul_iff_right₀ Real.pi_pos).mp hm
  linarith

lemma pole_coefficient_radius {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0}))
    {R : ℝ} (hRpos : 0 < R) (hR : R < 1) :
    ‖deriv h 0‖ ^ 2 * R ^ 2 ≤ R⁻¹ ^ 2 := by
  have hb (ε : ℝ) (hε : 0 < ε) : ‖deriv h 0‖ ^ 2 * R ^ 2 ≤ R⁻¹ ^ 2 + 4 * ε := by
    have hl : Tendsto (fun r : ℝ => ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2)) (𝓝[>] (0 : ℝ))
        (𝓝 (‖deriv h 0‖ ^ 2 * R ^ 2)) := by
      have hc : ContinuousAt (fun r : ℝ => ‖deriv h 0‖ ^ 2 * (R ^ 2 - r ^ 2)) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hu : Tendsto (fun r : ℝ => R⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (R⁻¹ ^ 2 + 4 * ε)) := by
      have hc : ContinuousAt (fun r : ℝ => R⁻¹ ^ 2 + 4 * ε + 4 * ε ^ 2 * r ^ 2) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hl hu (pole_area_small_radius hd h0 hi hRpos hR hε)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh := hb (ε / 4) (by positivity)
  linarith

theorem pole_coefficient_le_one {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (h0 : h 0 = 0)
    (hi : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) :
    ‖deriv h 0‖ ≤ 1 := by
  have hl : Tendsto (fun R : ℝ => ‖deriv h 0‖ ^ 2 * R ^ 2) (𝓝[<] (1 : ℝ))
      (𝓝 (‖deriv h 0‖ ^ 2)) := by
    have hc : ContinuousAt (fun R : ℝ => ‖deriv h 0‖ ^ 2 * R ^ 2) 1 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun R : ℝ => R⁻¹ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun R : ℝ => R⁻¹ ^ 2) 1 :=
      (continuousAt_id.inv₀ one_ne_zero).pow 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ R in 𝓝[<] (1 : ℝ), ‖deriv h 0‖ ^ 2 * R ^ 2 ≤ R⁻¹ ^ 2 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with R hR hRpos
    exact pole_coefficient_radius hd h0 hi hRpos hR
  have hh := le_of_tendsto_of_tendsto hl hu he
  nlinarith [norm_nonneg (deriv h 0)]

end
end StrictInverseFirstPower

end

end OAI

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

open Set Filter Metric Complex
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

theorem hasDerivAt_continuous_squareRoot {f g : ℂ → ℂ} {z d : ℂ}
    (hf : HasDerivAt f d z) (hg : ContinuousAt g z) (hg0 : g z ≠ 0)
    (hsq : ∀ᶠ w in 𝓝 z, g w ^ 2 = f w) :
    HasDerivAt g (d / (2 * g z)) z := by
  have hden : g z + g z ≠ 0 := by simpa only [← two_mul] using mul_ne_zero two_ne_zero hg0
  have hd : ∀ᶠ w in 𝓝 z, g w + g z ≠ 0 := (hg.add_const _).eventually_ne hden
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := (hasDerivAt_iff_tendsto_slope.mp hf).div
    ((hg.add_const _).tendsto.mono_left nhdsWithin_le_nhds) hden
  have he : (fun w => slope f z w / (g w + g z)) =ᶠ[𝓝[≠] z] slope g z := by
    filter_upwards [hsq.filter_mono nhdsWithin_le_nhds, hd.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with w hw hwd hwz
    rw [slope_def_field, slope_def_field, ← hw, ← hsq.self_of_nhds]
    field_simp
    ring
  simpa only [← two_mul] using ht.congr' he

theorem exists_holomorphic_squareRoot {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ 2 = f z := by
  have hz : 0 ∉ f '' U := by
    rintro ⟨z, hz, he⟩
    exact hzero z hz he
  obtain ⟨g, hg, hsq⟩ := Complex.exists_continuousOn_pow_eq hc hU hf.continuousOn hz (by decide : 2 ≠ 0)
  refine ⟨g, fun z hz => ?_, fun z _ => hsq z⟩
  have hgn : g z ≠ 0 := by
    intro he
    apply hzero z hz
    rw [← hsq z, he, zero_pow (by decide : 2 ≠ 0)]
  exact (hasDerivAt_continuous_squareRoot (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    (hg.continuousAt (hU.mem_nhds hz)) hgn (Filter.Eventually.of_forall hsq)).differentiableAt.differentiableWithinAt

theorem exists_normalized_holomorphic_squareRoot {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hU : IsOpen U) (hc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z ∈ U, f z ≠ 0) (ha : a ∈ U) (hfa : f a = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, g z ^ 2 = f z) ∧ g a = 1 := by
  obtain ⟨g, hg, hsq⟩ := exists_holomorphic_squareRoot hU hc hf hzero
  have hga : g a ^ 2 = 1 := (hsq a ha).trans hfa
  have hgn : g a ≠ 0 := by intro he; simp [he] at hga
  refine ⟨fun w => g w / g a, hg.div_const _, ?_, div_self hgn⟩
  intro w hw
  rw [div_pow, hsq w hw, hga, div_one]

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma simplyConnected_disk : IsSimplyConnected (ball (0 : ℂ) 1) := by
  let := (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, by simp⟩
  change SimplyConnectedSpace (ball (0 : ℂ) 1)
  exact inferInstance

lemma sq_mem_disk {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : z ^ 2 ∈ ball (0 : ℂ) 1 := by
  simp only [mem_ball, dist_zero_right, norm_pow] at *
  nlinarith [norm_nonneg z]

lemma mul_dslope_zero (f : ℂ → ℂ) (hf0 : f 0 = 0) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa [hf0, smul_eq_mul] using sub_smul_dslope f (0 : ℂ) z

theorem exists_odd_root_transform {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z ^ 2 = dslope f 0 z) ∧
      InjOn (fun z => z * g (z ^ 2)) (ball 0 1) := by
  have hdU : DifferentiableOn ℂ (dslope f 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hd
  have hu0 : dslope f 0 0 = 1 := by simpa using h1
  have hun (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : dslope f 0 z ≠ 0 := by
    intro he
    by_cases hz0 : z = 0
    · simp [hz0, h1] at he
    · apply hz0
      apply hi hz (by simp)
      rw [← mul_dslope_zero f h0 z, he, mul_zero, h0]
  obtain ⟨g, hg, hgsq, hg0⟩ := exists_normalized_holomorphic_squareRoot
    isOpen_ball simplyConnected_disk hdU hun (by simp) hu0
  have hgn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : g z ≠ 0 := by
    intro he
    apply hun z hz
    rw [← hgsq z hz, he, zero_pow (by decide : 2 ≠ 0)]
  refine ⟨g, hg, hg0, hgn, hgsq, ?_⟩
  intro z hz w hw he
  have he2 : z ^ 2 = w ^ 2 := by
    apply hi (sq_mem_disk hz) (sq_mem_disk hw)
    calc f (z ^ 2) = (z * g (z ^ 2)) ^ 2 := by
          rw [mul_pow, hgsq _ (sq_mem_disk hz), mul_dslope_zero f h0]
         _ = (w * g (w ^ 2)) ^ 2 := congrArg (· ^ 2) he
         _ = f (w ^ 2) := by
          rw [mul_pow, hgsq _ (sq_mem_disk hw), mul_dslope_zero f h0]
  dsimp only at he
  rw [he2] at he
  exact mul_right_cancel₀ (hgn _ (sq_mem_disk hw)) he

theorem second_coefficient_le_two {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (dslope f 0) 0‖ ≤ 2 := by
  obtain ⟨g, hg, hg0, hgn, hgsq, hqi⟩ := exists_odd_root_transform hd hi h0 h1
  let v : ℂ → ℂ := fun z => (g z)⁻¹
  have hv : DifferentiableOn ℂ v (ball 0 1) := hg.inv hgn
  have hv0 : v 0 = 1 := by simp [v, hg0]
  let H : ℂ → ℂ := fun z => z * dslope v 0 (z ^ 2)
  have hds : DifferentiableOn ℂ (dslope v 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hv
  have hH : DifferentiableOn ℂ H (ball 0 1) := differentiableOn_id.mul
    (hds.comp (differentiableOn_id.pow 2) (fun _ hz => sq_mem_disk hz))
  have hH0 : H 0 = 0 := by simp [H]
  have hG (z : ℂ) (hz : z ≠ 0) : z⁻¹ + H z = (z * g (z ^ 2))⁻¹ := by
    have hs := sub_smul_dslope v (0 : ℂ) (z ^ 2)
    simp only [sub_zero, smul_eq_mul, hv0] at hs
    dsimp only [H]
    rw [mul_inv_rev]
    dsimp only [v] at hs
    field_simp
    linear_combination hs
  have hGi : InjOn (fun z => z⁻¹ + H z) (ball 0 1 \ {0}) := by
    intro z hz w hw he
    dsimp only at he
    rw [hG z hz.2, hG w hw.2, inv_inj] at he
    exact hqi hz.1 hw.1 he
  have ha := pole_coefficient_le_one hH hH0 hGi
  have hd0 := hg.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hvd : HasDerivAt v (-deriv g 0) 0 := by
    convert hd0.hasDerivAt.inv (hgn 0 (by simp)) using 1
    all_goals first | rfl | simp [hg0]
  have hHd : deriv H 0 = -deriv g 0 := by
    have hp : HasDerivAt (fun z : ℂ => z ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℂ)).pow 2 using 1 <;> first | rfl | norm_num
    have hdss : HasDerivAt (dslope v 0) (deriv (dslope v 0) (0 ^ 2)) (0 ^ 2) :=
      (hds.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ^ 2 ∈ ball 0 1))).hasDerivAt
    have he := (hasDerivAt_id (0 : ℂ)).mul (hdss.comp (0 : ℂ) hp)
    convert he.deriv using 1 <;> first | rfl | simp [hvd.deriv]
  have hud : deriv (dslope f 0) 0 = 2 * deriv g 0 := by
    have he : (fun z => g z ^ 2) =ᶠ[𝓝 (0 : ℂ)] dslope f 0 := by
      filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
      exact hgsq z hz
    have hp : HasDerivAt (fun z => g z ^ 2) (2 * deriv g 0) 0 := by
      convert hd0.hasDerivAt.pow 2 using 1
      all_goals first | rfl | simp [hg0]
    exact (hp.congr_of_eventuallyEq he.symm).deriv
  rw [hHd, norm_neg] at ha
  rw [hud, norm_mul]
  norm_num
  linarith

end
end StrictInverseFirstPower

end

end OAI

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Metric Complex
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma omitted_mobius_normalized {f : ℂ → ℂ} {c : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 1 - c * f z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / (1 - c * f z)) (ball 0 1) ∧
    InjOn (fun z => f z / (1 - c * f z)) (ball 0 1) ∧
    (f 0 / (1 - c * f 0) = 0) ∧
    deriv (fun z => f z / (1 - c * f z)) 0 = 1 := by
  refine ⟨hd.div ((differentiableOn_const (1 : ℂ)).sub (hd.const_mul c)) hn, ?_, by simp [h0], ?_⟩
  · intro z hz w hw he
    apply hi hz hw
    have he' := (div_eq_div_iff (hn z hz) (hn w hw)).mp he
    linear_combination he'
  · have hdf : HasDerivAt f 1 0 := by
      simpa only [h1] using (hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).hasDerivAt
    have he := hdf.div ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) (hn 0 (by simp))
    convert he.deriv using 1
    all_goals first | rfl | simp [h0]

lemma omitted_mobius_coefficient {f : ℂ → ℂ} {c : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    deriv (dslope (fun z => f z / (1 - c * f z)) 0) 0 =
      deriv (dslope f 0) 0 + c := by
  let g : ℂ → ℂ := fun z => f z / (1 - c * f z)
  have hd0 := hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hdf : HasDerivAt f 1 0 := by simpa only [h1] using hd0.hasDerivAt
  have hn0 : 1 - c * f 0 ≠ 0 := by simp [h0]
  have hgd : HasDerivAt g 1 0 := by
    convert hdf.div ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) hn0 using 1
    all_goals first | rfl | simp [h0]
  have hg0 : g 0 = 0 := by simp [g, h0]
  have he (z : ℂ) : dslope g 0 z = dslope f 0 z / (1 - c * f z) := by
    by_cases hz : z = 0
    · simp [hz, hgd.deriv, h0, h1]
    · simp only [dslope_of_ne _ hz, slope_def_field, sub_zero, hg0, h0]
      dsimp only [g]
      ring
  have hdU := ((Complex.differentiableOn_dslope
    (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).mpr hd).differentiableAt
      (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hp := hdU.hasDerivAt.div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) hn0
  have hpe : HasDerivAt (dslope g 0) (deriv (dslope f 0) 0 + c) 0 := by
    convert hp using 1
    all_goals first | rfl | exact funext he | simp [h0, h1]
  exact hpe.deriv

theorem omitted_value_quarter {f : ℂ → ℂ} {w : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (hw : w ∉ f '' ball 0 1) :
    (1 / 4 : ℝ) ≤ ‖w‖ := by
  have hw0 : w ≠ 0 := by
    intro he
    apply hw
    exact ⟨0, by simp, by rw [h0, he]⟩
  have hn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 1 - w⁻¹ * f z ≠ 0 := by
    intro he
    apply hw
    refine ⟨z, hz, ?_⟩
    have ha : w⁻¹ * f z = 1 := (sub_eq_zero.mp he).symm
    calc f z = w * (w⁻¹ * f z) := by rw [← mul_assoc, mul_inv_cancel₀ hw0, one_mul]
         _ = w := by rw [ha, mul_one]
  obtain ⟨hgd, hgi, hg0, hg1⟩ := omitted_mobius_normalized hd hi h0 h1 hn
  have ha := second_coefficient_le_two hd hi h0 h1
  have hb := second_coefficient_le_two hgd hgi hg0 hg1
  rw [omitted_mobius_coefficient hd h0 h1] at hb
  have hc : ‖w⁻¹‖ ≤ 4 := by
    calc ‖w⁻¹‖ = ‖(deriv (dslope f 0) 0 + w⁻¹) - deriv (dslope f 0) 0‖ := by ring_nf
         _ ≤ ‖deriv (dslope f 0) 0 + w⁻¹‖ + ‖deriv (dslope f 0) 0‖ := norm_sub_le _ _
         _ ≤ 4 := by linarith
  rw [norm_inv] at hc
  have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hh := mul_le_mul_of_nonneg_right hc hnpos.le
  rw [inv_mul_cancel₀ (ne_of_gt hnpos)] at hh
  linarith

theorem koebe_quarter {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  intro w hw
  by_contra hn
  have hh := omitted_value_quarter hd hi h0 h1 hn
  simp only [mem_ball, dist_zero_right] at hw
  linarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma scale_disk_mem {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball 0 1) :
    (r : ℂ) * w ∈ ball (0 : ℂ) r := by
  simp only [mem_ball, dist_zero_right] at hw ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr hw

theorem local_koebe_quarter {F : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ F (ball a r)) (hi : InjOn F (ball a r))
    (hn : deriv F a ≠ 0) :
    ball (F a) (r * ‖deriv F a‖ / 4) ⊆ F '' ball a r := by
  let d : ℂ := (r : ℂ) * deriv F a
  have hdne : d ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hn
  let g : ℂ → ℂ := fun w => (F (a + (r : ℂ) * w) - F a) / d
  have hm : MapsTo (fun w : ℂ => a + (r : ℂ) * w) (ball 0 1) (ball a r) := by
    intro w hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using scale_disk_mem hr hw
  have hcomp : DifferentiableOn ℂ (fun w => F (a + (r : ℂ) * w)) (ball 0 1) :=
    hd.comp (by fun_prop) hm
  have hgd : DifferentiableOn ℂ g (ball 0 1) := hcomp.sub_const _ |>.div_const _
  have hgi : InjOn g (ball 0 1) := by
    intro w hw u hu he
    have hh := hi (hm hw) (hm hu) (by
      have he' := (div_left_inj' hdne).mp he
      exact sub_left_injective he')
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') (add_left_cancel hh)
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : deriv g 0 = 1 := by
    have ha := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hb : HasDerivAt (fun w : ℂ => a + (r : ℂ) * w) (r : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add a
    have he : a + (r : ℂ) * 0 = a := by simp
    rw [← he] at ha
    have h := ((ha.comp 0 hb).sub_const (F a)).div_const d
    have hh : HasDerivAt g (deriv F (a + (r : ℂ) * 0) * (r : ℂ) / d) 0 := h
    rw [hh.deriv, he]
    dsimp [d]
    field_simp [hn, Complex.ofReal_ne_zero.mpr hr.ne']
  intro ξ hξ
  have hnorm : ‖d‖ = r * ‖deriv F a‖ := by simp [d, abs_of_pos hr]
  have hh : (ξ - F a) / d ∈ ball (0 : ℂ) (1 / 4) := by
    simp only [mem_ball, dist_eq_norm] at hξ
    simp only [mem_ball, dist_zero_right, norm_div]
    rw [div_lt_iff₀ (norm_pos_iff.mpr hdne), hnorm]
    linarith
  obtain ⟨w, hw, he⟩ := koebe_quarter hgd hgi hg0 hg1 hh
  refine ⟨a + r * w, hm hw, ?_⟩
  exact sub_left_injective ((div_left_inj' hdne).mp he)

end
end StrictInverseFirstPower

end

end OAI

namespace MVPBP
open Set Filter Metric Complex Polynomial
open scoped Topology

theorem exists_branch (p : Polynomial ℂ) (z : ℂ) (R : ℝ) (hR : 0 < R)
    (hcrit : ∀ c : ℂ, p.derivative.eval c = 0 → R ≤ ‖p.eval c - p.eval z‖) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (ball (p.eval z) R) ∧ InjOn ψ (ball (p.eval z) R) ∧
      HasDerivAt ψ (p.derivative.eval z)⁻¹ (p.eval z) ∧
      ψ (p.eval z) = z ∧ ∀ w ∈ ball (p.eval z) R, p.eval (ψ w) = w := by
  have hne : Nonempty (ball (p.eval z) R) := ⟨⟨p.eval z, mem_ball_self hR⟩⟩
  have hcc : ContractibleSpace (ball (p.eval z) R) :=
    (convex_ball (p.eval z) R).contractibleSpace ⟨p.eval z, mem_ball_self hR⟩
  have hlpc : LocallyPathConnectedSpace (ball (p.eval z) R) := isOpen_ball.locallyPathConnectedSpace
  have cov := p.isCoveringMapOn_eval
  let f : C(ball (p.eval z) R, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hs : ∀ a, f a ∈ (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
    rintro ⟨a, ha⟩ ⟨c, hc, hca⟩
    have h1 := hcrit c hc
    have h2 : p.eval c = a := hca
    rw [h2] at h1
    have h3 : ‖a - p.eval z‖ < R := by simpa [dist_eq_norm] using ha
    exact absurd h1 (not_le.mpr h3)
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := cov.existsUnique_continuousMap_lifts f
    (a₀ := ⟨p.eval z, mem_ball_self hR⟩) (e₀ := z) rfl hs
  classical
  let ψ : ℂ → ℂ := fun w => if h : w ∈ ball (p.eval z) R then F ⟨w, h⟩ else z
  have hψ : ∀ w (h : w ∈ ball (p.eval z) R), ψ w = F ⟨w, h⟩ := fun w h => dif_pos h
  have hψp : ∀ w ∈ ball (p.eval z) R, p.eval (ψ w) = w := by
    intro w hw
    rw [hψ w hw]
    exact congrFun hFp ⟨w, hw⟩
  have hcont : ContinuousOn ψ (ball (p.eval z) R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (ball (p.eval z) R).domRestrict ψ = F := by
      funext ⟨w, hw⟩
      exact hψ w hw
    rw [this]
    exact F.continuous
  have hd : ∀ w ∈ ball (p.eval z) R, HasDerivAt ψ (p.derivative.eval (ψ w))⁻¹ w := by
    intro w hw
    have hnz : p.derivative.eval (ψ w) ≠ 0 := by
      intro h0
      have h1 := hcrit _ h0
      rw [hψp w hw] at h1
      have h3 : ‖w - p.eval z‖ < R := by simpa [dist_eq_norm] using hw
      exact absurd h1 (not_le.mpr h3)
    refine HasDerivAt.of_local_left_inverse (f := p.eval) (hcont.continuousAt (isOpen_ball.mem_nhds hw))
      (p.hasDerivAt (ψ w)) hnz ?_
    filter_upwards [isOpen_ball.mem_nhds hw] with y hy using hψp y hy
  have h0 : ψ (p.eval z) = z := by
    rw [hψ _ (mem_ball_self hR)]
    exact hF0
  refine ⟨ψ, fun w hw => (hd w hw).differentiableAt.differentiableWithinAt, ?_, ?_, h0, hψp⟩
  · intro a ha b hb hab
    rw [← hψp a ha, ← hψp b hb, hab]
  · have := hd _ (mem_ball_self hR)
    rwa [h0] at this

theorem main (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) :
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 * ‖p.derivative.eval z‖ := by
  by_cases hz : p.derivative.eval z = 0
  · exact ⟨z, hz, by simp [hz]⟩
  have hdeg : 2 ≤ p.natDegree := Polynomial.le_natDegree_of_coe_le_degree hp
  have hd1 : p.derivative.natDegree = p.natDegree - 1 := Polynomial.natDegree_derivative p
  have hp0 : p.derivative ≠ 0 := by
    intro h
    rw [h] at hd1
    simp only [natDegree_zero] at hd1
    omega
  have hd2 : p.derivative.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp0]
    exact_mod_cast (by omega : p.derivative.natDegree ≠ 0)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p.derivative hd2
  have hmem : ∀ c, c ∈ p.derivative.roots.toFinset ↔ p.derivative.eval c = 0 := by
    intro c
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    rfl
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image p.derivative.roots.toFinset
    (fun c => ‖p.eval c - p.eval z‖) ⟨r, (hmem r).mpr hr⟩
  have hc0' : p.derivative.eval c0 = 0 := (hmem c0).mp hc0
  have hmin' : ∀ c, p.derivative.eval c = 0 → ‖p.eval c0 - p.eval z‖ ≤ ‖p.eval c - p.eval z‖ :=
    fun c hc => hmin c ((hmem c).mpr hc)
  refine ⟨c0, hc0', ?_⟩
  set R := ‖p.eval c0 - p.eval z‖ with hRdef
  rcases (norm_nonneg (p.eval c0 - p.eval z)).eq_or_lt with h0 | hR
  · have : p.eval z - p.eval c0 = 0 := by
      rw [← norm_eq_zero, norm_sub_rev]
      exact h0.symm
    rw [this]
    simp only [norm_zero, zero_div]
    positivity
  obtain ⟨ψ, hψd, hψi, hψder, hψz, hψp⟩ := exists_branch p z R hR hmin'
  have hder : deriv ψ (p.eval z) = (p.derivative.eval z)⁻¹ := hψder.deriv
  have hn : deriv ψ (p.eval z) ≠ 0 := by
    rw [hder]
    exact inv_ne_zero hz
  have hk := OAI.StrictInverseFirstPower.local_koebe_quarter hR hψd hψi hn
  rw [hψz, hder, norm_inv] at hk
  have hnot : c0 ∉ ball z (R * (‖p.derivative.eval z‖)⁻¹ / 4) := by
    intro hc
    obtain ⟨w, hw, hwc⟩ := hk hc
    have := hψp w hw
    rw [hwc] at this
    have h3 : ‖w - p.eval z‖ < R := by simpa [dist_eq_norm] using hw
    rw [this] at hRdef
    exact absurd hRdef (ne_of_gt h3)
  have hdist : R * (‖p.derivative.eval z‖)⁻¹ / 4 ≤ ‖z - c0‖ := by
    have := not_lt.mp (fun h => hnot (by simpa [dist_eq_norm] using h))
    rw [norm_sub_rev]
    simpa [dist_eq_norm] using this
  have hnp : 0 < ‖p.derivative.eval z‖ := norm_pos_iff.mpr hz
  have hpos : 0 < ‖z - c0‖ := lt_of_lt_of_le (by positivity) hdist
  rw [div_le_iff₀ hpos, norm_sub_rev]
  have : R * (‖p.derivative.eval z‖)⁻¹ / 4 * (4 * ‖p.derivative.eval z‖) = R := by
    field_simp
  calc R = R * (‖p.derivative.eval z‖)⁻¹ / 4 * (4 * ‖p.derivative.eval z‖) := this.symm
    _ ≤ ‖z - c0‖ * (4 * ‖p.derivative.eval z‖) := by gcongr
    _ = 4 * ‖p.derivative.eval z‖ * ‖z - c0‖ := by ring

end MVPBP

theorem OMA.solution : type_of% @MeanValueProblem.mean_value_problem_leq_4 :=
  fun p hp z _ => MVPBP.main p hp z
