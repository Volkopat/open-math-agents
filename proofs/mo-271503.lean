import OMAStatements.S_mo_271503
import Mathlib

/-!
Hans posed MathOverflow question 271503. The median bound for convex Gaussian
functions is due to Stanisław Kwapień (1994). The argument through Ehrhard’s
inequality is described by Gozlan, Madiman, Roberto and Samson. The heat
semigroup comparison used here follows the method of Barthe and Huet.
-/

open Real

namespace LognormalMedian

/-- Translation of the one-dimensional normal density with variance t. -/
noncomputable def K (t r w : ℝ) : ℝ :=
  (sqrt (2*π))⁻¹ * (sqrt t)⁻¹ * exp (-((w-r)^2)/(2*t))

theorem kernel_space (t r w : ℝ) :
    HasDerivAt (fun u => K t u w) (K t r w * ((w-r)/t)) r := by
  have h := (((((hasDerivAt_id r).const_sub w).pow 2).neg.div_const (2*t)).exp).const_mul
    ((sqrt (2*π))⁻¹ * (sqrt t)⁻¹)
  apply h.congr_deriv
  simp only [K, id_eq, Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem kernel_space_twice (t r w : ℝ) :
    HasDerivAt (deriv (fun u => K t u w))
      (K t r w * ((w-r)^2/t^2 - 1/t)) r := by
  rw [show deriv (fun u => K t u w) = fun u => K t u w * ((w-u)/t) by
    funext u; exact (kernel_space t u w).deriv]
  apply ((kernel_space t r w).mul (((hasDerivAt_id r).const_sub w).div_const t)).congr_deriv
  simp only [id_eq]
  ring

theorem kernel_time {t : ℝ} (ht : 0 < t) (r w : ℝ) :
    HasDerivAt (fun u => K u r w)
      (K t r w * ((w-r)^2/t^2 - 1/t) / 2) t := by
  have hs := (Real.hasDerivAt_sqrt ht.ne').inv (Real.sqrt_pos.2 ht).ne'
  have hden := (hasDerivAt_id t).const_mul (2 : ℝ)
  have hex := ((hasDerivAt_const t (-((w-r)^2))).div hden (by positivity)).exp
  apply ((hs.const_mul ((sqrt (2*π))⁻¹)).mul hex).congr_deriv
  simp only [id_eq, K, Pi.div_apply, Pi.inv_apply]
  have hs0 := (Real.sqrt_pos.2 ht).ne'
  have hs2 := Real.sq_sqrt ht.le
  generalize hv : sqrt t = v at hs2 hs0 ⊢
  rw [← hs2]
  field_simp [hs0]
  ring

/-- Uniform spatial decay on a compact neighborhood in time and center. -/
theorem local_exponential_bound {t₀ t t₁ r R : ℝ} (h₀ : 0 < t₀)
    (hl : t₀ ≤ t) (hr : t ≤ t₁) (hc : |r| ≤ R) (w : ℝ) :
    exp (-((w-r)^2)/(2*t)) ≤ exp (R^2/(2*t₀)) * exp (-(w^2)/(4*t₁)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htt := h₀.trans_le hl
  have hr2 : r^2 ≤ R^2 := by
    calc r^2 = |r|^2 := (sq_abs _).symm
         _ ≤ R^2 := pow_le_pow_left₀ (abs_nonneg _) hc _
  calc
    -((w-r)^2)/(2*t) ≤ (R^2 - w^2/2)/(2*t) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (w-2*r)]
    _ = R^2/(2*t) - w^2/(4*t) := by ring
    _ ≤ R^2/(2*t₀) - w^2/(4*t₁) := sub_le_sub
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))
    _ = _ := by ring

theorem integrable_majorant {b : ℝ} (hb : 0 < b) (C : ℝ) :
    MeasureTheory.Integrable (fun w : ℝ => C * ((1+w^2) * exp (-b*w^2))) := by
  have h2 : MeasureTheory.Integrable (fun w : ℝ => w^2 * exp (-b*w^2)) := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)
  have h := ((integrable_exp_neg_mul_sq hb).add h2).const_mul C
  simpa only [Pi.add_apply, add_mul, one_mul] using h


open MeasureTheory Filter Set Topology

noncomputable def J (t r w : ℝ) := K t r w * ((w-r)/t)
noncomputable def S (t r w : ℝ) := K t r w * ((w-r)^2/t^2-1/t)

theorem J_space (t r w : ℝ) : HasDerivAt (fun u => J t u w) (S t r w) r := by
  convert kernel_space_twice t r w using 1
  · exact funext fun u => (kernel_space t u w).deriv.symm
  · rfl

theorem kernel_bounds {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (_hR : 0 ≤ R) :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ t r w, a ≤ t → t ≤ b → |r| ≤ R →
      |K t r w| ≤ B w ∧ |J t r w| ≤ B w ∧ |S t r w| ≤ B w := by
  let D := (sqrt (2*π))⁻¹ * (sqrt a)⁻¹ * exp (R^2/(2*a))
  let v := a⁻¹
  let P := 4 * (1+R^2) * (1+v^2+v)
  have hv : 0 ≤ v := inv_nonneg.mpr ha.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP : 1 ≤ P := by dsimp [P]; nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg v), mul_nonneg (sq_nonneg R) hv, sq_nonneg R, sq_nonneg v]
  have hb := ha.trans_le hab
  refine ⟨fun w => D*P*((1+w^2)*exp (-(1/(4*b))*w^2)), integrable_majorant (by positivity) _, ?_⟩
  intro t r w hat htb hrc
  have ht := ha.trans_le hat
  have hi : t⁻¹ ≤ v := inv_anti₀ ha hat
  have hr : r^2 ≤ R^2 := (sq_abs r).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hrc 2)
  have hv2 : (t⁻¹)^2 ≤ v^2 := pow_le_pow_left₀ (by positivity) hi _
  let E := exp (-(1/(4*b))*w^2)
  have hE : 0 ≤ E := (exp_pos _).le
  have hk : |K t r w| ≤ D * E := by
    rw [abs_of_nonneg (show 0 ≤ K t r w by unfold K; positivity)]
    have h := local_exponential_bound ha hat htb hrc w
    have h₁ := inv_anti₀ (sqrt_pos.2 ha) (sqrt_le_sqrt hat)
    dsimp [K,D,E]
    rw [show -(1/(4*b))*w^2 = -(w^2)/(4*b) by ring]
    calc
      _ ≤ ((sqrt (2*π))⁻¹*(sqrt a)⁻¹) * (exp (R^2/(2*a)) * exp (-(w^2)/(4*b))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity)) h (by positivity) (by positivity)
      _ = _ := by ring
  have hwr : (w-r)^2 ≤ 2*(1+R^2)*(1+w^2) := by
    nlinarith [sq_nonneg (w+r), sq_nonneg (R*w)]
  let A := 2*(1+R^2)*(1+w^2)
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg R, sq_nonneg w, sq_nonneg (R*w)]
  have hwra : |w-r| ≤ A := by nlinarith [sq_abs (w-r), sq_nonneg (|w-r|-1)]
  have hm : A * (1+v^2+v) ≤ P * (1+w^2) := by
    dsimp [A,P]
    have hh : 0 ≤ (1+R^2)*(1+w^2)*(1+v^2+v) := by positivity
    linarith only [show 2*((1+R^2)*(1+w^2)*(1+v^2+v)) ≤ 4*((1+R^2)*(1+w^2)*(1+v^2+v)) by linarith]
  have hbig : 1 ≤ P*(1+w^2) := by nlinarith [mul_nonneg (show 0 ≤ P by linarith) (sq_nonneg w)]
  have hlin : |(w-r)/t| ≤ P*(1+w^2) := by
    rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
    exact (mul_le_mul hwra hi (by positivity) (by linarith)).trans
      ((mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg v] : v ≤ 1+v^2+v) (by linarith)).trans hm)
  have hquad : |(w-r)^2/t^2-1/t| ≤ P*(1+w^2) := by
    calc
      _ ≤ (w-r)^2 * (t⁻¹)^2 + t⁻¹ := by
        have h := abs_sub_le ((w-r)^2/t^2) 0 (1/t)
        rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (w-r)^2/t^2), abs_of_nonneg (by positivity : 0 ≤ 1/t)] at h
        simpa only [div_eq_mul_inv, one_mul, inv_pow] using h
      _ ≤ A*v^2 + v := add_le_add (mul_le_mul hwr hv2 (by positivity) (by linarith)) hi
      _ ≤ A*(1+v^2+v) := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) hv]
      _ ≤ _ := hm
  have bound (c : ℝ) (hc : |c| ≤ P*(1+w^2)) :
      |K t r w * c| ≤ D*P*((1+w^2)*E) := by
    rw [abs_mul]
    calc
      _ ≤ (D*E)*(P*(1+w^2)) := mul_le_mul hk hc (abs_nonneg _) (mul_nonneg hD hE)
      _ = _ := by ring
  exact ⟨by simpa only [mul_one] using bound 1 (by simpa using hbig), bound _ hlin, bound _ hquad⟩

noncomputable def heat (g : ℝ → ℝ) (t r : ℝ) := ∫ w, g w * K t r w
noncomputable def heatX (g : ℝ → ℝ) (t r : ℝ) := ∫ w, g w * J t r w
noncomputable def heatXX (g : ℝ → ℝ) (t r : ℝ) := ∫ w, g w * S t r w

private theorem under_integral {x₀ : ℝ} {U V : ℝ → ℝ → ℝ} {B g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ w, |g w| ≤ 1) (hB : Integrable B)
    (hU : ∀ x, Continuous (U x)) (hV : Continuous (V x₀))
    (h0 : ∀ w, |U x₀ w| ≤ B w)
    (hnear : ∀ᶠ x in 𝓝 x₀, ∀ w, |V x w| ≤ B w ∧
        HasDerivAt (fun u => U u w) (V x w) x) :
    HasDerivAt (fun x => ∫ w, g w * U x w) (∫ w, g w * V x₀ w) x₀ := by
  have hmul (w c : ℝ) (h : |c| ≤ B w) : ‖g w*c‖ ≤ B w := by
    rw [Real.norm_eq_abs, abs_mul]
    simpa using (mul_le_mul (hg1 w) h (abs_nonneg _) zero_le_one)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x w => g w * U x w)
    (F' := fun x w => g w * V x w) (bound := B) hnear
    (Eventually.of_forall fun x => (hg.mul (hU x)).aestronglyMeasurable) ?_
    (hg.mul hV).aestronglyMeasurable ?_ hB ?_).2
  · exact hB.mono' (hg.mul (hU x₀)).aestronglyMeasurable (ae_of_all _ fun w => hmul w _ (h0 w))
  · exact ae_of_all _ fun w x hx => hmul w _ (hx w).1
  · exact ae_of_all _ fun w x hx => ((hx w).2.const_mul (g w))

/-- The first and second spatial derivatives and the time derivative pass through the integral. -/
theorem heat_jets {g : ℝ → ℝ} (hg : Continuous g) (hg1 : ∀ w, |g w| ≤ 1)
    {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HasDerivAt (heat g t) (heatX g t r) r ∧
    HasDerivAt (heatX g t) (heatXX g t r) r ∧
    HasDerivAt (fun u => heat g u r) (heatXX g t r / 2) t := by
  obtain ⟨B,hB,h⟩ := kernel_bounds (a := t/2) (b := 2*t) (R := |r|+1)
    (by linarith) (by linarith) (by positivity)
  have ht₁ : t/2 ≤ t := by linarith
  have ht₂ : t ≤ 2*t := by linarith
  have hr : |r| ≤ |r|+1 := by linarith
  have hn : ∀ᶠ x in 𝓝 r, |x| < |r|+1 :=
    (continuous_abs.continuousAt).eventually_lt continuousAt_const (by simp)
  have hu : ∀ᶠ u in 𝓝 t, t/2 < u ∧ u < 2*t :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hK (u v : ℝ) : Continuous (K u v) := by unfold K; fun_prop
  have hJ (u v : ℝ) : Continuous (J u v) := by unfold J; exact (hK u v).mul (by fun_prop)
  have hS (u v : ℝ) : Continuous (S u v) := by unfold S; exact (hK u v).mul (by fun_prop)
  have h₀ := fun w => h t r w ht₁ ht₂ hr
  refine ⟨under_integral hg hg1 hB (hK t) (hJ t r) (fun w => (h₀ w).1) ?_,
    under_integral hg hg1 hB (hJ t) (hS t r) (fun w => (h₀ w).2.1) ?_, ?_⟩
  · filter_upwards [hn] with x hx w
    exact ⟨(h t x w ht₁ ht₂ hx.le).2.1, kernel_space t x w⟩
  · filter_upwards [hn] with x hx w
    exact ⟨(h t x w ht₁ ht₂ hx.le).2.2, J_space t x w⟩
  · have he : heatXX g t r / 2 = ∫ w, g w * (S t r w / 2) := by
      unfold heatXX
      simp only [← mul_div_assoc, integral_div]
    rw [he]
    apply under_integral (U := fun u => K u r) (V := fun u w => S u r w / 2)
      hg hg1 hB (fun u => hK u r) ((hS t r).div_const _) (fun w => (h₀ w).1)
    filter_upwards [hu] with u hu w
    refine ⟨?_, kernel_time (by linarith [hu.1]) r w⟩
    rw [abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
    linarith [(h u r w hu.1.le hu.2.le hr).2.2, abs_nonneg (S u r w)]

theorem heat_equation {g : ℝ → ℝ} (hg : Continuous g) (hg1 : ∀ w, |g w| ≤ 1)
    {t : ℝ} (ht : 0 < t) (r : ℝ) :
    2 * deriv (fun u => heat g u r) t = deriv (deriv (heat g t)) r := by
  have h := heat_jets hg hg1 ht r
  rw [h.2.2.deriv, show deriv (heat g t) = heatX g t from
    funext fun x => (heat_jets hg hg1 ht x).1.deriv, h.2.1.deriv]
  ring

end LognormalMedian

open Real MeasureTheory ProbabilityTheory Set Topology

namespace LognormalMedian

noncomputable def Φ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x
noncomputable def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem phi_formula (x : ℝ) : φ x = (sqrt (2 * π))⁻¹ * exp (-(x^2)/2) := by
  simp [φ, gaussianPDFReal]

theorem normal_integral (x : ℝ) : Φ x = ∫ t in Iic x, φ t := by
  rw [Φ, cdf_eq_real, Measure.real, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]
  rfl

theorem normal_cdf_deriv (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have hi : Integrable φ := integrable_gaussianPDFReal _ _
  have hc : Continuous φ := by unfold φ gaussianPDFReal; fun_prop
  have hfun : Φ = fun z => (∫ t in (0 : ℝ)..z, φ t) + Φ 0 := by
    funext z
    rw [normal_integral z, normal_integral 0]
    exact sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn)
  rw [hfun]
  exact (intervalIntegral.integral_hasDerivAt_right hi.intervalIntegrable
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const _

theorem normal_cdf_strict : StrictMono Φ := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(normal_cdf_deriv x).deriv]
  exact gaussianPDFReal_pos _ _ _ one_ne_zero

theorem normal_pdf_deriv (x : ℝ) : HasDerivAt φ (-x * φ x) x := by
  rw [show φ = fun t => (sqrt (2 * π))⁻¹ * exp (-(t^2)/2) from funext phi_formula]
  have square := (hasDerivAt_id x).pow 2
  apply ((((square.neg.div_const 2).exp).const_mul _).congr_deriv)
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
  ring

end LognormalMedian

open Set Real MeasureTheory

namespace LognormalMedian

/-- Tangent inequality for normal CDF shifts, on the entire real line.
The normalizing constant of the Gaussian density can be any positive k. -/
theorem normal_shift_tangent {F : ℝ → ℝ} (k : ℝ) (hk : 0 < k)
    (hF : ∀ z, HasDerivAt F (k * exp (-(z^2)/2)) z)
    (a b z : ℝ) (ha : 0 ≤ a) :
    F (z+a) - F (b+a) ≤ exp (-a*b - a^2/2) * (F z - F b) := by
  let slope := fun x : ℝ => exp (-a*x - a^2/2)
  let G := fun x : ℝ => F (x+a) - slope b * F x
  have hd (x : ℝ) : HasDerivAt G (k * exp (-(x^2)/2) * (slope x - slope b)) x := by
    have h := ((hF (x+a)).comp x ((hasDerivAt_id x).add_const a)).sub
      ((hF x).const_mul (slope b))
    apply h.congr_deriv
    dsimp only [slope, id_eq]
    have hpow : -(x^2)/2 + (-a*x - a^2/2) = -((x+a)^2)/2 := by ring
    rw [← hpow, Real.exp_add]
    ring
  have anti : Antitone slope := by
    intro x y hxy
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hxy)]
  have hgc : Continuous G := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hgd : Differentiable ℝ G := fun x => (hd x).differentiableAt
  have hm : MonotoneOn G (Iic b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic b) hgc.continuousOn hgd.differentiableOn
    intro x hx
    rw [(hd x).deriv]
    exact mul_nonneg (mul_nonneg hk.le (exp_pos _).le)
      (sub_nonneg.mpr (anti (show x ≤ b from Set.mem_Iic.mp (interior_subset hx))))
  have hn : AntitoneOn G (Ici b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici b) hgc.continuousOn hgd.differentiableOn
    intro x hx
    rw [(hd x).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk.le (exp_pos _).le)
      (sub_nonpos.mpr (anti (show b ≤ x from Set.mem_Ici.mp (interior_subset hx))))
  have h : G z ≤ G b := by
    rcases le_total z b with hz | hz
    · exact hm (mem_Iic.mpr hz) (mem_Iic.mpr le_rfl) hz
    · exact hn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  dsimp [G, slope] at h
  linarith

/-- Integrating the tangent inequality controls a shift of an arbitrary
profile, including after several Gaussian coordinates have been integrated. -/
theorem shift_under_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F H : ℝ → ℝ) (x : Ω → ℝ) (b m : ℝ)
    (ht : ∀ z, H z - H b ≤ m * (F z - F b))
    (hF : Integrable (fun ω => F (x ω)) P) (hH : Integrable (fun ω => H (x ω)) P)
    (hb : ∫ ω, F (x ω) ∂P = F b) :
    (∫ ω, H (x ω) ∂P) ≤ H b := by
  have h := integral_mono (μ := P) (hH.sub (integrable_const (H b)))
    ((hF.sub (integrable_const (F b))).const_mul m) (fun ω => ht (x ω))
  change (∫ ω, H (x ω) - H b ∂P) ≤ ∫ ω, m * (F (x ω) - F b) ∂P at h
  rw [integral_sub hH (integrable_const _), integral_const_mul,
    integral_sub hF (integrable_const _), integral_const, integral_const,
    probReal_univ, one_smul, one_smul, hb, sub_self, mul_zero] at h
  linarith

end LognormalMedian

namespace LognormalMedian
open Filter

noncomputable def Q := Function.invFun Φ

theorem continuous_Φ : Continuous Φ := continuous_iff_continuousAt.mpr fun x => (normal_cdf_deriv x).continuousAt

theorem Φ_mem (x : ℝ) : Φ x ∈ Ioo 0 1 :=
  ⟨(cdf_nonneg _ (x-1)).trans_lt (normal_cdf_strict (by linarith : x-1 < x)),
   (normal_cdf_strict (by linarith : x < x+1)).trans_le (cdf_le_one _ _)⟩

theorem Φ_Q {y : ℝ} (hy : y ∈ Ioo 0 1) : Φ (Q y) = y := by
  have hb : Tendsto Φ atBot (𝓝 0) := tendsto_cdf_atBot _
  have ht : Tendsto Φ atTop (𝓝 1) := tendsto_cdf_atTop _
  obtain ⟨a,ha⟩ := (hb.eventually_lt_const hy.1).exists
  obtain ⟨b,hb⟩ := (ht.eventually_const_lt hy.2).exists
  exact Function.invFun_eq (intermediate_value_univ a b continuous_Φ ⟨ha.le,hb.le⟩)

theorem Q_Φ (x : ℝ) : Q (Φ x) = x := normal_cdf_strict.injective (Φ_Q (Φ_mem x))

theorem deriv_Q {y : ℝ} (hy : y ∈ Ioo 0 1) : HasDerivAt Q (φ (Q y))⁻¹ y := by
  have hn := Ioo_mem_nhds hy.1 hy.2
  have hc : ContinuousAt Q y := by
    apply tendsto_order.mpr
    constructor
    · intro x hx
      have hx' := normal_cdf_strict hx
      rw [Φ_Q hy] at hx'
      filter_upwards [hn, lt_mem_nhds hx'] with z hz hz'
      exact normal_cdf_strict.lt_iff_lt.mp (by rwa [Φ_Q hz])
    · intro x hx
      have hx' := normal_cdf_strict hx
      rw [Φ_Q hy] at hx'
      filter_upwards [hn, gt_mem_nhds hx'] with z hz hz'
      exact normal_cdf_strict.lt_iff_lt.mp (by rwa [Φ_Q hz])
  exact HasDerivAt.of_local_left_inverse hc (normal_cdf_deriv _) (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'
    (by filter_upwards [hn] with x hx; exact Φ_Q hx)

noncomputable abbrev γ := gaussianReal 0 1

noncomputable def foldG (f : ℝ → ℝ) := Q (∫ x, Φ (f x) ∂γ)

theorem Φ_integrable {f : ℝ → ℝ} (hf : Continuous f) : Integrable (fun x => Φ (f x)) γ :=
  (integrable_const (1:ℝ)).mono' (continuous_Φ.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs, abs_of_pos (Φ_mem _).1] using (Φ_mem (f x)).2.le)

theorem integral_Φ_mem {f : ℝ → ℝ} (hf : Continuous f) : (∫ x, Φ (f x) ∂γ) ∈ Ioo 0 1 := by
  have hp {u : ℝ → ℝ} (hu : Integrable u γ) (hp : ∀ x, 0 < u x) : 0 < ∫ x, u x ∂γ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hu]
    have hs : Function.support u = univ := eq_univ_of_forall fun x => (hp x).ne'
    simp [hs]
  refine ⟨hp (Φ_integrable hf) (fun x => (Φ_mem _).1), ?_⟩
  have h := hp ((integrable_const (1:ℝ)).sub (Φ_integrable hf)) (fun x => sub_pos.mpr (Φ_mem _).2)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const _) (Φ_integrable hf)] at h
  simpa using h

theorem Φ_foldG {f : ℝ → ℝ} (hf : Continuous f) : Φ (foldG f) = ∫ x, Φ (f x) ∂γ :=
  Φ_Q (integral_Φ_mem hf)

theorem foldG_shift {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a : ℝ} (ha : 0 ≤ a) (hle : ∀ x, f x ≤ g x + a) : foldG f ≤ foldG g + a := by
  apply normal_cdf_strict.le_iff_le.mp
  rw [Φ_foldG hf]
  refine (integral_mono (Φ_integrable hf) (Φ_integrable (hg.add_const a))
    (fun x => normal_cdf_strict.monotone (hle x))).trans ?_
  apply shift_under_integral γ Φ (fun x => Φ (x+a)) g (foldG g)
    (exp (-a * foldG g - a^2/2)) _ (Φ_integrable hg) (Φ_integrable (hg.add_const a)) (Φ_foldG hg).symm
  intro z
  exact normal_shift_tangent _ (by positivity) (fun x => phi_formula x ▸ normal_cdf_deriv x) _ _ _ ha
end LognormalMedian

namespace LognormalMedian

/-- The chain rule twice for a function composed with the normal CDF.
The input is the first and second spatial derivatives of the probit. -/
theorem cdf_second {F φ u : ℝ → ℝ} {a : ℝ}
    (hF : ∀ z, HasDerivAt F (φ z) z)
    (hφ : ∀ z, HasDerivAt φ (-z * φ z) z)
    (hu : ∀ z, DifferentiableAt ℝ u z)
    (hd : DifferentiableAt ℝ (deriv u) a) :
    deriv (deriv (F ∘ u)) a =
      φ (u a) * (deriv (deriv u) a - u a * (deriv u a) ^ 2) := by
  have hcomp : deriv (F ∘ u) = fun z => φ (u z) * deriv u z := by
    funext z
    exact ((hF (u z)).comp z (hu z).hasDerivAt).deriv
  rw [hcomp]
  change deriv ((φ ∘ u) * deriv u) a = _
  rw [(((hφ (u a)).comp a (hu a).hasDerivAt).mul hd.hasDerivAt).deriv]
  simp only [Function.comp_apply]
  ring

/-- Convert the scalar heat equation for a CDF to the quasilinear probit equation. -/
theorem probit_heat {φ ut uxx u ux : ℝ} (hp : 0 < φ)
    (heat : 2 * (φ * ut) = φ * (uxx - u * ux ^ 2)) :
    2 * ut = uxx - u * ux ^ 2 := by
  apply mul_left_cancel₀ hp.ne'
  linarith only [heat, mul_assoc (2 : ℝ) φ ut, mul_comm (2 : ℝ) φ,
    mul_assoc φ 2 ut]

/-- Jets at the mixed argument and at the two endpoints. The second
derivative is along the line where both spatial variables move equally. -/
theorem midpoint_evolution
    (z u v gz gu gv zt ut vt zxx uxx vxx : ℝ)
    (hz : 2 * zt = zxx - z * gz ^ 2)
    (hu : 2 * ut = uxx - u * gu ^ 2)
    (hv : 2 * vt = vxx - v * gv ^ 2) :
    (zt - (ut + vt) / 2) - (zxx - (uxx + vxx) / 2) / 2 +
      u * (gz + gu) / 2 * ((gz - gu) / 2) +
      v * (gz + gv) / 2 * ((gz - gv) / 2) +
      gz ^ 2 / 2 * (z - (u + v) / 2) = 0 := by
  linear_combination hz / 2 - hu / 4 - hv / 4

private theorem drift_lower (K b x : ℝ) (hK : 0 ≤ K)
    (h : |b| ≤ K * (1 + |x|)) : -(K * (1 + 3 * x ^ 2)) ≤ 2 * b * x := by
  have h1 := mul_le_mul_of_nonneg_right h (abs_nonneg x)
  have h2 := neg_abs_le (b*x)
  rw [abs_mul] at h2
  have h3 := mul_nonneg hK (sq_nonneg (|x| - 1))
  have hx : |x|^2 = x^2 := sq_abs x
  nlinarith [show K * |x| ^ 2 = K * x ^ 2 by rw [hx]]

/-- Strict supersolution for linearly growing drift on the entire plane.
The left side is the operator on exp((3K+3)t)(1+x²+y²), after division
by the positive exponential. -/
theorem quadratic_barrier (K b₁ b₂ c x y : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h₁ : |b₁| ≤ K * (1 + |x|)) (h₂ : |b₂| ≤ K * (1 + |y|)) :
    0 < (3*K+3) * (1+x^2+y^2) - 2 + 2*b₁*x + 2*b₂*y + c*(1+x^2+y^2) := by
  have h := mul_nonneg hc (show 0 ≤ 1 + x^2 + y^2 by positivity)
  nlinarith [drift_lower K b₁ x hK h₁, drift_lower K b₂ y hK h₂, sq_nonneg x, sq_nonneg y]

end LognormalMedian

namespace LognormalMedian
open Filter
open scoped NNReal

noncomputable def U (f : ℝ → ℝ) (t r : ℝ) := foldG fun w => f (r + sqrt t * w)

theorem U_zero (f : ℝ → ℝ) (r : ℝ) : U f 0 r = f r := by
  simp [U, foldG, Q_Φ]

theorem U_cont {f : ℝ → ℝ} (hf : Continuous f) : Continuous (Function.uncurry (U f)) := by
  let F := fun (p : ℝ × ℝ) w => Φ (f (p.2 + sqrt p.1 * w))
  have h₁ (p : ℝ × ℝ) : Continuous (F p) := continuous_Φ.comp (hf.comp (by fun_prop))
  have h₂ (w : ℝ) : Continuous (fun p => F p w) := continuous_Φ.comp (hf.comp (by fun_prop))
  have hC : Continuous (fun p => ∫ w, F p w ∂γ) := continuous_of_dominated
    (fun p => (h₁ p).aestronglyMeasurable)
    (fun p => ae_of_all _ fun w => (show ‖F p w‖ ≤ 1 by
      change |Φ _| ≤ 1
      rw [abs_of_pos (Φ_mem _).1]
      exact (Φ_mem _).2.le))
    (integrable_const _) (ae_of_all _ h₂)
  apply continuous_iff_continuousAt.mpr
  intro p
  change ContinuousAt (Q ∘ (fun z => ∫ w, F z w ∂γ)) p
  apply ContinuousAt.comp _ hC.continuousAt
  exact (deriv_Q (integral_Φ_mem (hf.comp (by fun_prop : Continuous (fun w : ℝ => p.2 + sqrt p.1*w))))).continuousAt

theorem U_lip {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) : LipschitzWith L (U f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [Real.dist_eq, abs_sub_le_iff]
  have h (r s : ℝ) : U f t r ≤ U f t s + L * dist r s := by
    apply foldG_shift (hf.continuous.comp (by fun_prop)) (hf.continuous.comp (by fun_prop)) (by positivity)
    intro w
    have hh := hf.dist_le_mul (r+sqrt t*w) (s+sqrt t*w)
    rw [dist_add_right, Real.dist_eq] at hh
    dsimp only [Function.comp_apply]
    linarith [le_abs_self (f (r+sqrt t*w) - f (s+sqrt t*w))]
  have h₁ := h r s
  have h₂ := h s r
  rw [dist_comm s r] at h₂
  exact ⟨by linarith, by linarith⟩

theorem heat_as_fold {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    Φ (U f t r) = heat (Φ ∘ f) t r := by
  rw [U, Φ_foldG (f := fun w => f (r + sqrt t * w)) (hf.comp (by fun_prop))]
  let v : ℝ≥0 := ⟨t, ht.le⟩
  have hv : v ≠ 0 := by intro he; exact ht.ne' (congrArg NNReal.toReal he)
  have hm : γ.map (fun w => r + sqrt t * w) = gaussianReal r v := by
    rw [show (fun w => r + sqrt t * w) = (r + ·) ∘ (sqrt t * ·) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    congr 1
    · ring
    · ext
      simp [v, Real.sq_sqrt ht.le]; rfl
  have hc := continuous_Φ.comp hf
  calc
    _ = ∫ w, (Φ ∘ f) w ∂(γ.map (fun w => r + sqrt t * w)) :=
      (integral_map (by fun_prop) hc.aestronglyMeasurable).symm
    _ = _ := by
      rw [hm, integral_gaussianReal_eq_integral_smul hv]
      apply integral_congr_ae
      apply ae_of_all
      intro w
      change (sqrt (2*π*t))⁻¹ * exp (-(w-r)^2/(2*t)) * (Φ ∘ f) w = (Φ ∘ f) w * K t r w
      simp only [sqrt_mul (by positivity : 0 ≤ 2*π), mul_inv, K]
      ring

/-- The inverse Gaussian CDF transforms the heat equation into a scalar nonlinear equation. -/
theorem U_jets {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    DifferentiableAt ℝ (U f t) r ∧ DifferentiableAt ℝ (deriv (U f t)) r ∧
    DifferentiableAt ℝ (fun u => U f u r) t ∧
    2 * deriv (fun u => U f u r) t = deriv (deriv (U f t)) r - U f t r * (deriv (U f t) r)^2 := by
  let g := Φ ∘ f
  have hg : Continuous g := continuous_Φ.comp hf
  have hg1 (w : ℝ) : |g w| ≤ 1 := by
    change |Φ _| ≤ 1
    rw [abs_of_pos (Φ_mem _).1]
    exact (Φ_mem _).2.le
  have hprob (r : ℝ) : heat g t r ∈ Ioo 0 1 := heat_as_fold hf ht r ▸ Φ_mem _
  have hrep (u r : ℝ) (hu : 0 < u) : U f u r = Q (heat g u r) := by
    rw [← heat_as_fold hf hu, Q_Φ]
  have hx (r : ℝ) : HasDerivAt (U f t) ((φ (U f t r))⁻¹ * heatX g t r) r := by
    rw [funext (fun r => hrep t r ht)]
    exact (deriv_Q (hprob r)).comp r (heat_jets hg hg1 ht r).1
  have ht_eq : (fun u => U f u r) =ᶠ[𝓝 t] fun u => Q (heat g u r) := by
    filter_upwards [lt_mem_nhds ht] with u hu
    exact hrep u r hu
  have htime := ((deriv_Q (hprob r)).comp t (heat_jets hg hg1 ht r).2.2).congr_of_eventuallyEq ht_eq
  have hxx : DifferentiableAt ℝ (deriv (U f t)) r := by
    rw [funext (fun r => (hx r).deriv)]
    apply DifferentiableAt.mul _ (heat_jets hg hg1 ht r).2.1.differentiableAt
    exact (((normal_pdf_deriv _).comp r (hx r)).differentiableAt).inv (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'
  refine ⟨(hx r).differentiableAt, hxx, htime.differentiableAt, ?_⟩
  have htcomp := (normal_cdf_deriv _).comp t htime.differentiableAt.hasDerivAt
  have ht_eq' : (fun u => heat g u r) =ᶠ[𝓝 t] Φ ∘ (fun u => U f u r) := by
    filter_upwards [lt_mem_nhds ht] with u hu
    exact (heat_as_fold hf hu r).symm
  have hd := (htcomp.congr_of_eventuallyEq ht_eq').deriv
  have hxd := cdf_second normal_cdf_deriv normal_pdf_deriv (fun r => (hx r).differentiableAt) hxx
  have hx_eq : Φ ∘ U f t = heat g t := funext (heat_as_fold hf ht)
  rw [hx_eq] at hxd
  apply probit_heat (gaussianPDFReal_pos 0 1 (U f t r) one_ne_zero)
  change 2 * (φ _ * _) = φ _ * _
  rw [← hd, ← hxd, heat_equation hg hg1 ht]
end LognormalMedian

open Filter Set Topology

namespace LognormalMedian

theorem second_nonneg_at_min {f : ℝ → ℝ} {a : ℝ}
    (hf : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra! hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hf.deriv_eq_zero hc
  have hconst : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hf, hmax] with x hx hy
    exact le_antisymm hy hx
  have h := hconst.deriv.deriv_eq
  simp at h
  linarith

abbrev Point := ℝ × ℝ × ℝ

end LognormalMedian

namespace LognormalMedian
open Real

theorem negative_minimum {W : ℝ → ℝ → ℝ → ℝ}
    (hc : Continuous fun p : Point => W p.1 p.2.1 p.2.2)
    (h0 : ∀ r s, 0 ≤ W 0 r s) (hbad : W 1 0 0 < 0)
    {R : ℝ} (hR : 0 < R)
    (hout : ∀ t ∈ Icc (0:ℝ) 1, ∀ r s, R ≤ |r| ∨ R ≤ |s| → 0 ≤ W t r s) :
    ∃ t ∈ Ioc (0:ℝ) 1, ∃ r s, W t r s < 0 ∧
      (∀ᶠ u in 𝓝[<] t, W t r s ≤ W u r s) ∧
      ∀ x y, W t r s ≤ W t x y := by
  let A := Icc (0:ℝ) 1 ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hcA : IsCompact A := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hq : ((1,0,0) : Point) ∈ A := ⟨⟨by norm_num, le_rfl⟩, ⟨by linarith,hR.le⟩, by linarith,hR.le⟩
  obtain ⟨⟨t,r,s⟩, hp, hm⟩ := hcA.exists_isMinOn ⟨_,hq⟩ hc.continuousOn
  have ht : t ∈ Icc (0:ℝ) 1 := hp.1
  have hw : W t r s < 0 := (hm hq).trans_lt hbad
  have hpos : 0 < t := ht.1.lt_of_ne (by rintro rfl; exact hw.not_ge (h0 r s))
  have hglob (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) (x y : ℝ) : W t r s ≤ W u x y := by
    by_cases hh : R ≤ |x| ∨ R ≤ |y|
    · exact hw.le.trans (hout u hu x y hh)
    · push Not at hh
      exact hm (show (u,x,y) ∈ A from ⟨hu, abs_le.mp hh.1.le, abs_le.mp hh.2.le⟩)
  refine ⟨t,⟨hpos,ht.2⟩,r,s,hw,?_,hglob t ht⟩
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hpos), self_mem_nhdsWithin] with u hu hu'
    exact hglob u ⟨hu.le,(show u < t from hu').le.trans ht.2⟩ r s

theorem time_nonpos {f : ℝ → ℝ} {t d : ℝ} (hf : HasDerivAt f d t)
    (hm : ∀ᶠ u in 𝓝[<] t, f t ≤ f u) : d ≤ 0 := by
  apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  filter_upwards [hm, self_mem_nhdsWithin] with x hx hxt
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr (show x < t from hxt).le)

theorem barrier_radius {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ R > 0, ∀ r s : ℝ, R ≤ |r| ∨ R ≤ |s| →
      M*(1+|r|+|s|) ≤ η*(1+r^2+s^2) := by
  let R := 1+3*M/η
  have hR : 1 ≤ R := by dsimp [R]; linarith [show 0 ≤ 3*M/η by positivity]
  refine ⟨R, by linarith, ?_⟩
  intro r s hs
  let z := max |r| |s|
  have hz : R ≤ z := hs.elim (fun h => h.trans (le_max_left _ _)) (fun h => h.trans (le_max_right _ _))
  have h₁ : 3*M ≤ η*z := by
    have h' : 3*M/η ≤ z := by dsimp [R] at hz; linarith
    linarith [(div_le_iff₀ hη).mp h']
  have hzz : z^2 ≤ r^2+s^2 := by
    rcases le_total |r| |s| with h|h
    · simp only [z, max_eq_right h, sq_abs]; linarith [sq_nonneg r]
    · simp only [z, max_eq_left h, sq_abs]; linarith [sq_nonneg s]
  calc
    _ ≤ M*(3*z) := mul_le_mul_of_nonneg_left (by linarith [show |r| ≤ z from le_max_left _ _, show |s| ≤ z from le_max_right _ _]) hM
    _ ≤ η*z^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (show 0 ≤ z by linarith)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hη.le
end LognormalMedian

namespace LognormalMedian
open Filter Real Set
open scoped NNReal

theorem U_growth {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∃ M ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ r, |U f t r| ≤ M * (1+|r|) := by
  have hc : Continuous (fun t : ℝ => |U f t 0|) :=
    continuous_abs.comp ((U_cont hf.continuous).comp (continuous_id.prodMk continuous_const))
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).bddAbove_image (f := fun t : ℝ => |U f t 0|) hc.continuousOn
  refine ⟨max |B| L, (abs_nonneg B).trans (le_max_left _ _), ?_⟩
  intro t ht r
  have hdiff := (U_lip hf t).dist_le_mul r 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at hdiff
  have hcenter : |U f t 0| ≤ max |B| L := (hB (mem_image_of_mem _ ht)).trans ((le_abs_self _).trans (le_max_left _ _))
  calc
    _ ≤ |U f t r - U f t 0| + |U f t 0| := by simpa using abs_add_le (U f t r - U f t 0) (U f t 0)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (le_max_right |B| (L:ℝ)) (abs_nonneg r)]

private noncomputable def W (z u v : ℝ → ℝ → ℝ) (η A t r s : ℝ) :=
  z t ((r+s)/2) - (u t r + v t s)/2 + η*exp (A*t)*(1+r^2+s^2)


private theorem line_first (z u v : ℝ → ℝ) (hz : Differentiable ℝ z) (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (B r s i j : ℝ) :
    ∀ d : ℝ, HasDerivAt
      (fun e => z (((r+i*e)+(s+j*e))/2) - (u (r+i*e)+v (s+j*e))/2 +
        B*(1+(r+i*e)^2+(s+j*e)^2))
      (deriv z (((r+i*d)+(s+j*d))/2) * ((i+j)/2) -
        (deriv u (r+i*d)*i + deriv v (s+j*d)*j)/2 +
        B*(2*(r+i*d)*i+2*(s+j*d)*j)) d := by
  intro d
  have hr := ((hasDerivAt_id d).const_mul i).const_add r
  have hs := ((hasDerivAt_id d).const_mul j).const_add s
  have hm := (hr.add hs).div_const 2
  have h1 := (hz _).hasDerivAt.comp d hm
  have h2 := (((hu _).hasDerivAt.comp d hr).add ((hv _).hasDerivAt.comp d hs)).div_const 2
  have h3 := ((((hr.pow 2).const_add 1).add (hs.pow 2))).const_mul B
  have h := (h1.sub h2).add h3
  apply h.congr_deriv
  simp [id_eq]

private theorem minimum_jets (z u v : ℝ → ℝ)
    (hz : Differentiable ℝ z) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hzz : Differentiable ℝ (deriv z)) (huu : Differentiable ℝ (deriv u)) (hvv : Differentiable ℝ (deriv v))
    (B r s : ℝ) (H : ∀ x y, z ((r+s)/2) - (u r + v s)/2 + B*(1+r^2+s^2) ≤
      z ((x+y)/2) - (u x+v y)/2 + B*(1+x^2+y^2)) :
    (deriv z ((r+s)/2) - deriv u r)/2 + 2*B*r = 0 ∧
    (deriv z ((r+s)/2) - deriv v s)/2 + 2*B*s = 0 ∧
    0 ≤ deriv (deriv z) ((r+s)/2) - (deriv (deriv u) r + deriv (deriv v) s)/2 + 4*B := by
  let F := fun (i j d : ℝ) => z (((r+i*d)+(s+j*d))/2) - (u (r+i*d)+v (s+j*d))/2 + B*(1+(r+i*d)^2+(s+j*d)^2)
  have hm (i j : ℝ) : IsLocalMin (F i j) 0 := by
    apply Eventually.of_forall
    intro d
    simpa [F] using H (r+i*d) (s+j*d)
  have h (i j d : ℝ) := line_first z u v hz hu hv B r s i j d
  have h₁ (i j : ℝ) := (h i j 0).deriv.symm.trans (hm i j).deriv_eq_zero
  refine ⟨by linarith [show _ from (by simpa using h₁ 1 0 : deriv z ((r+s)/2)*(1/2) - deriv u r / 2 + B*(2*r)=0)],
    by linarith [show _ from (by simpa using h₁ 0 1 : deriv z ((r+s)/2)*(1/2) - deriv v s / 2 + B*(2*s)=0)], ?_⟩
  have hD : deriv (F 1 1) = fun d => deriv z (((r+s)/2)+d) - (deriv u (r+d)+deriv v (s+d))/2 + B*(2*(r+d)+2*(s+d)) := by
    funext d
    rw [(h 1 1 d).deriv]
    simp only [one_mul, mul_one, show ((1:ℝ)+1)/2=1 by norm_num, show (r+d+(s+d))/2 = (r+s)/2+d by ring]
  have hd (x : ℝ) := (hasDerivAt_id (0:ℝ)).const_add x
  have hh1 := (hzz _).hasDerivAt.comp 0 (hd ((r+s)/2))
  have hh2 := (((huu _).hasDerivAt.comp 0 (hd r)).add ((hvv _).hasDerivAt.comp 0 (hd s))).div_const 2
  have hh3 := (((hd r).const_mul 2).add ((hd s).const_mul 2)).const_mul B
  have hh := (hh1.sub hh2).add hh3
  have hmin := second_nonneg_at_min (hm 1 1) (h 1 1 0).continuousAt
  rw [hD] at hmin
  have hder := hh.deriv
  simp only [Pi.add_def, Pi.sub_def, Function.comp_def, id_eq, add_zero, mul_one] at hder
  rw [hder] at hmin
  linarith
end LognormalMedian

namespace LognormalMedian
open Filter Real Set
open scoped NNReal

private theorem paired_growth {z u v : ℝ} {r s M : ℝ} (hM : 0 ≤ M)
    (hz : |z| ≤ M*(1+|(r+s)/2|)) (hu : |u| ≤ M*(1+|r|)) (hv : |v| ≤ M*(1+|s|)) :
    -(2*M*(1+|r|+|s|)) ≤ z - (u+v)/2 := by
  have hmid : |(r+s)/2| ≤ (|r|+|s|)/2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_add_le r s]
  nlinarith [neg_abs_le z, le_abs_self u, le_abs_self v, mul_le_mul_of_nonneg_left hmid hM,
    mul_nonneg hM (abs_nonneg r), mul_nonneg hM (abs_nonneg s)]

private theorem drift_bound {a x p q L M : ℝ} (hM : 0 ≤ M) (_hL : 0 ≤ L)
    (ha : |a| ≤ M*(1+|x|)) (hp : |p| ≤ L) (hq : |q| ≤ L) :
    |a*(p+q)/2| ≤ M*L*(1+|x|) := by
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2),abs_mul]
  have hh := mul_le_mul ha ((abs_add_le p q).trans (add_le_add hp hq)) (abs_nonneg _) (by positivity)
  linarith

/-- Preservation of midpoint concavity under one Gaussian marginal. The quadratic barrier forces a negative minimum into a bounded region. -/
theorem foldG_midpoint {f g h : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith L g) (hh : LipschitzWith L h)
    (hmid : ∀ r s, (f r + g s)/2 ≤ h ((r+s)/2)) : (foldG f + foldG g)/2 ≤ foldG h := by
  let z := U h
  let u := U f
  let v := U g
  obtain ⟨Mf,hMf,hF⟩ := U_growth hf
  obtain ⟨Mg,hMg,hG⟩ := U_growth hg
  obtain ⟨Mh,hMh,hH⟩ := U_growth hh
  let M := Mf+Mg+Mh
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have bound {V a x : ℝ} (ha : a ≤ M) (hx : |V| ≤ a*(1+|x|)) :=
    hx.trans (mul_le_mul_of_nonneg_right ha (by positivity))
  have hU t ht x := bound (show Mf ≤ M by dsimp [M]; linarith) (hF t ht x)
  have hV t ht x := bound (show Mg ≤ M by dsimp [M]; linarith) (hG t ht x)
  have hZ t ht x := bound (show Mh ≤ M by dsimp [M]; linarith) (hH t ht x)
  let k := M * L
  let A := 3*k+3
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  by_contra! hn
  let δ := (foldG f + foldG g)/2 - foldG h
  have hδ : 0 < δ := sub_pos.mpr hn
  let η := δ/(2*exp A)
  have hη : 0 < η := by dsimp [η]; positivity
  let w := W z u v η A
  have wc : Continuous fun p : Point => w p.1 p.2.1 p.2.2 := by
    have hcZ := (U_cont hh.continuous).comp (f := fun p : Point => (p.1,(p.2.1+p.2.2)/2)) (by fun_prop)
    have hcU := (U_cont hf.continuous).comp (f := fun p : Point => (p.1,p.2.1)) (by fun_prop)
    have hcV := (U_cont hg.continuous).comp (f := fun p : Point => (p.1,p.2.2)) (by fun_prop)
    exact (hcZ.sub ((hcU.add hcV).div_const 2)).add (by fun_prop : Continuous (fun p : Point => η*exp (A*p.1)*(1+p.2.1^2+p.2.2^2)))
  have w0 (r s : ℝ) : 0 ≤ w 0 r s := by
    simp only [w,W,z,u,v,U_zero,mul_zero,exp_zero,mul_one]
    exact add_nonneg (sub_nonneg.mpr (hmid _ _)) (by positivity)
  have w1 : w 1 0 0 < 0 := by
    have h1 (j : ℝ → ℝ) : U j 1 0 = foldG j := by simp [U]
    simp only [w,W,z,u,v,add_zero,zero_div,h1,mul_one,zero_pow (by decide : 2 ≠ 0)]
    have hcancel : η * exp A = δ/2 := by dsimp [η]; field_simp
    rw [hcancel]
    dsimp [δ]
    linarith
  obtain ⟨R,hR,hout⟩ := barrier_radius (M := 2*M) (by positivity) hη
  have hwout (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (r s : ℝ) (hb : R ≤ |r| ∨ R ≤ |s|) : 0 ≤ w t r s := by
    have hE : 1 ≤ exp (A*t) := Real.one_le_exp (mul_nonneg hA ht.1)
    have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hη.le) (show 0 ≤ 1+r^2+s^2 by positivity)
    have hC := paired_growth hM (hZ t ht ((r+s)/2)) (hU t ht r) (hV t ht s)
    dsimp only [w,W,z,u,v]
    linarith [hout r s hb]
  obtain ⟨t,ht,r,s,hneg,htmin,hsmin⟩ := negative_minimum wc w0 w1 hR hwout
  let m := (r+s)/2
  let B := η*exp (A*t)
  have hB : 0 < B := by dsimp [B]; positivity
  have Z := U_jets hh.continuous ht.1
  have F := U_jets hf.continuous ht.1
  have G := U_jets hg.continuous ht.1
  have ⟨hr,hs,hdiag⟩ := minimum_jets (z t) (u t) (v t) (fun x => (Z x).1) (fun x => (F x).1) (fun x => (G x).1)
    (fun x => (Z x).2.1) (fun x => (F x).2.1) (fun x => (G x).2.1) B r s hsmin
  have td := (((Z m).2.2.1.hasDerivAt.sub (((F r).2.2.1.hasDerivAt.add
    (G s).2.2.1.hasDerivAt).div_const 2))).add (((((hasDerivAt_id t).const_mul A).exp).const_mul η).mul_const (1+r^2+s^2))
  have htime := time_nonpos td htmin
  let gz := deriv (z t) m
  let gu := deriv (u t) r
  let gv := deriv (v t) s
  let b₁ := u t r * (gz+gu)/2
  let b₂ := v t s * (gz+gv)/2
  let c := gz^2/2
  have H := midpoint_evolution (z t m) (u t r) (v t s) gz gu gv _ _ _ _ _ _
    (Z m).2.2.2 (F r).2.2.2 (G s).2.2.2
  have hgz : |gz| ≤ L := norm_deriv_le_of_lipschitz (U_lip hh t)
  have hgu : |gu| ≤ L := norm_deriv_le_of_lipschitz (U_lip hf t)
  have hgv : |gv| ≤ L := norm_deriv_le_of_lipschitz (U_lip hg t)
  have htc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have barr := quadratic_barrier k b₁ b₂ c r s hk hc (drift_bound hM L.coe_nonneg (hU t htc r) hgz hgu)
    (drift_bound hM L.coe_nonneg (hV t htc s) hgz hgv)
  change _ - _ + b₁*((gz-gu)/2) + b₂*((gz-gv)/2) + c*(z t m-(u t r+v t s)/2) = 0 at H
  change (gz-gu)/2 + 2*B*r = 0 at hr
  change (gz-gv)/2 + 2*B*s = 0 at hs
  change z t m - (u t r + v t s)/2 + B*(1+r^2+s^2) < 0 at hneg
  change 0 < A*(1+r^2+s^2)-2+2*b₁*r+2*b₂*s+c*(1+r^2+s^2) at barr
  change _ - _ + η * (exp (A*t)*(A*1))*(1+r^2+s^2) ≤ 0 at htime
  have hb' : η * (exp (A*t)*(A*1)) = B*A := by dsimp [B]; ring
  rw [hb'] at htime
  have hN := mul_nonpos_of_nonneg_of_nonpos hc hneg.le
  linarith only [H, mul_pos hB barr, htime, hdiag, hN,
    congrArg (b₁ * ·) hr, congrArg (b₂ * ·) hs]
end LognormalMedian

namespace LognormalMedian
open Filter Real MeasureTheory Set
open scoped NNReal

abbrev V (n : ℕ) := Fin n → ℝ
noncomputable abbrev Γ (n : ℕ) := Measure.pi (fun _ : Fin n => γ)
noncomputable def foldN {n : ℕ} (f : V n → ℝ) := Q (∫ x, Φ (f x) ∂Γ n)
def ins {n : ℕ} (r : ℝ) (x : V n) : V (n+1) := (0 : Fin (n+1)).insertNth r x

theorem ins_dist {n : ℕ} (r s : ℝ) (x y : V n) :
    dist (ins r x) (ins s y) = max (dist r s) (dist x y) :=
  Fin.dist_insertNth_insertNth (α := fun _ => ℝ) 0 r s x y

private theorem lip_slice {n : ℕ} {f : V (n+1) → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : V n) :
    LipschitzWith L (fun r => f (ins r x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  simpa only [ins_dist,dist_self,max_eq_left dist_nonneg] using hf.dist_le_mul (ins r x) (ins s x)

private theorem lip_fold_slice {n : ℕ} {f : V (n+1) → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun x => foldG (fun r => f (ins r x))) := by
  have h (x y : V n) : foldG (fun r => f (ins r x)) ≤ foldG (fun r => f (ins r y)) + L * dist x y := by
    apply foldG_shift (lip_slice hf x).continuous (lip_slice hf y).continuous (by positivity)
    intro r
    have h := hf.dist_le_mul (ins r x) (ins r y)
    rw [ins_dist,dist_self,max_eq_right dist_nonneg,Real.dist_eq] at h
    linarith [le_abs_self (f (ins r x) - f (ins r y))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_sub_le_iff]
  have h₁ := h x y
  have h₂ := h y x
  rw [dist_comm y x] at h₂
  constructor <;> linarith

private theorem foldN_succ {n : ℕ} {f : V (n+1) → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    foldN f = foldN (fun x => foldG (fun r => f (ins r x))) := by
  unfold foldN
  congr 1
  simp_rw [Φ_foldG (lip_slice hf _).continuous]
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => γ) 0).symm
  rw [← mp.integral_comp']
  change (∫ p : ℝ × V n, Φ (f (e p)) ∂γ.prod (Γ n)) = _
  rw [integral_prod_symm]
  · rfl
  · apply (integrable_const (1:ℝ)).mono'
    · exact (continuous_Φ.measurable.comp (hf.continuous.measurable.comp e.measurable)).aestronglyMeasurable
    · exact ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_pos (Φ_mem _).1]
        exact (Φ_mem _).2.le

/-- Fubini and induction give the functional midpoint inequality for a finite Gaussian product. -/
theorem foldN_midpoint {n : ℕ} {f g h : V n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith L g) (hh : LipschitzWith L h)
    (hm : ∀ x y, (f x+g y)/2 ≤ h (fun i => (x i+y i)/2)) :
    (foldN f + foldN g)/2 ≤ foldN h := by
  induction n with
  | zero =>
    have h0 (j : V 0 → ℝ) : foldN j = j 0 := by
      unfold foldN
      rw [show (fun x => Φ (j x)) = (fun _ => Φ (j 0)) from funext fun x => congrArg (fun y => Φ (j y)) (Subsingleton.elim _ _)]
      simp [Q_Φ]
    simpa only [h0, show (fun i : Fin 0 => ((0 : V 0) i + (0 : V 0) i)/2) = 0 from Subsingleton.elim _ _] using hm 0 0
  | succ n ih =>
    rw [foldN_succ hf,foldN_succ hg,foldN_succ hh]
    apply ih (lip_fold_slice hf) (lip_fold_slice hg) (lip_fold_slice hh)
    intro x y
    apply foldG_midpoint (lip_slice hf x) (lip_slice hg y) (lip_slice hh _)
    intro r s
    convert hm (ins r x) (ins s y) using 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [ins]
end LognormalMedian

namespace LognormalMedian
open Filter Real MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

theorem gen_Φ_integrable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] {P : Measure E} [IsProbabilityMeasure P] {f : E → ℝ} (hf : Continuous f) : Integrable (fun x => Φ (f x)) P :=
  (integrable_const (1:ℝ)).mono' (continuous_Φ.comp hf).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs, abs_of_pos (Φ_mem _).1] using (Φ_mem (f x)).2.le)

theorem gen_integral_Φ_mem {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] {P : Measure E} [IsProbabilityMeasure P] {f : E → ℝ} (hf : Continuous f) : (∫ x, Φ (f x) ∂P) ∈ Ioo 0 1 := by
  have hp {u : E → ℝ} (hu : Integrable u P) (hp : ∀ x, 0 < u x) : 0 < ∫ x, u x ∂P := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hu]
    have hs : Function.support u = univ := eq_univ_of_forall fun x => (hp x).ne'
    simp [hs]
  refine ⟨hp (gen_Φ_integrable hf) (fun x => (Φ_mem _).1), ?_⟩
  have h := hp ((integrable_const (1:ℝ)).sub (gen_Φ_integrable hf)) (fun x => sub_pos.mpr (Φ_mem _).2)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const _) (gen_Φ_integrable hf)] at h
  simpa using h


theorem Φ_neg (x : ℝ) : Φ (-x) = 1 - Φ x := by
  have hneg : γ.map (fun z : ℝ => -z) = γ := by simp [γ, gaussianReal_map_neg]
  have he : Φ (-x) = γ.real (Ici x) := by
    rw [Φ, cdf_eq_real]
    change γ.real _ = _
    conv_lhs => rw [← hneg, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext z
    simp
  let : NullSingletonClass γ := nullSingletonClass_gaussianReal one_ne_zero
  rw [he, Φ, cdf_eq_real, ← measureReal_congr (μ := γ) (Iio_ae_eq_Iic (a := x)), ← compl_Iio, measureReal_compl measurableSet_Iio,probReal_univ]

private noncomputable def step (y : ℝ) : ℝ := if 0 < y then 1 else if y < 0 then 0 else Φ 0

private theorem step_lim (y : ℝ) : Tendsto (fun k : ℕ => Φ ((k:ℝ)*y)) atTop (𝓝 (step y)) := by
  rcases lt_trichotomy 0 y with h|rfl|h
  · simp only [step,if_pos h]
    exact (tendsto_cdf_atTop _).comp (Tendsto.atTop_mul_const h tendsto_natCast_atTop_atTop)
  · simp [step]
  · simp only [step,if_neg h.not_gt,if_pos h]
    exact (tendsto_cdf_atBot _).comp (Tendsto.atTop_mul_const_of_neg h tendsto_natCast_atTop_atTop)

private noncomputable def limitCDF {n : ℕ} (f : V n → ℝ) (a : ℝ) := ∫ x, step (a-f x) ∂Γ n
private noncomputable def smoothCDF {n : ℕ} (f : V n → ℝ) (k : ℕ) (a : ℝ) := ∫ x, Φ ((k:ℝ)*(a-f x)) ∂Γ n

private theorem CDF_lim {n : ℕ} {f : V n → ℝ} (hf : Continuous f) (a : ℝ) :
    Tendsto (fun k => smoothCDF f k a) atTop (𝓝 (limitCDF f a)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun k => (continuous_Φ.comp (by fun_prop : Continuous (fun x => (k:ℝ)*(a-f x)))).aestronglyMeasurable)
    (integrable_const _) _ (ae_of_all _ fun x => step_lim _)
  exact fun k => ae_of_all _ fun x => by
    change |Φ _| ≤ 1
    rw [abs_of_pos (Φ_mem _).1]
    exact (Φ_mem _).2.le

private theorem limit_bounds {n : ℕ} {f : V n → ℝ} (hf : Continuous f) (a : ℝ) :
    (Γ n).real {x | f x < a} ≤ limitCDF f a ∧ limitCDF f a ≤ (Γ n).real {x | f x ≤ a} := by
  have hs : Measurable step := by exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const)
  have hsi : Integrable (fun x => step (a-f x)) (Γ n) := by
    apply (integrable_const (1:ℝ)).mono' (hs.comp (measurable_const.sub hf.measurable)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |step (a-f x)| ≤ 1
      unfold step; split_ifs <;> simp [abs_of_pos (Φ_mem 0).1, (Φ_mem 0).2.le]
  have hlt := measurableSet_lt hf.measurable (measurable_const (a := a))
  have hle := measurableSet_le hf.measurable (measurable_const (a := a))
  have hind (s : Set (V n)) (hs : MeasurableSet s) :
      (Γ n).real s = ∫ x, s.indicator (fun _ => (1:ℝ)) x ∂Γ n := by simp [integral_indicator hs]
  rw [hind _ hlt,hind _ hle]
  constructor
  · apply integral_mono ((integrable_const _).indicator hlt) hsi
    intro x
    simp only [indicator,mem_ofPred_eq,step]
    split_ifs <;> linarith [(Φ_mem 0).1,(Φ_mem 0).2]
  · apply integral_mono hsi ((integrable_const _).indicator hle)
    intro x
    simp only [indicator,mem_ofPred_eq,step]
    split_ifs <;> linarith [(Φ_mem 0).1,(Φ_mem 0).2]

private theorem tail_mean {E : Type*} [MeasurableSpace E] {P : Measure E} [IsProbabilityMeasure P]
    {f : E → ℝ} (hf : Integrable f P) {a : ℝ}
    (h : ∀ s > 0, P.real {x | f x < a-s} ≤ P.real {x | a+s ≤ f x}) :
    a ≤ ∫ x, f x ∂P := by
  let l := fun x => max (a-f x) 0
  let r := fun x => max (f x-a) 0
  have hl : Integrable l P := ((integrable_const a).sub hf).pos_part
  have hr : Integrable r P := (hf.sub (integrable_const a)).pos_part
  have hl0 : 0 ≤ᵐ[P] l := ae_of_all _ fun _ => le_max_right _ _
  have hr0 : 0 ≤ᵐ[P] r := ae_of_all _ fun _ => le_max_right _ _
  have hlr : ∫ x, l x ∂P ≤ ∫ x, r x ∂P := by
    apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hr0)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hl hl0, ofReal_integral_eq_lintegral_ofReal hr hr0,
      lintegral_eq_lintegral_meas_lt P hl0 hl.aemeasurable, lintegral_eq_lintegral_meas_le P hr0 hr.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
    have hs' : 0 < s := hs
    have H := h s hs'
    rw [measureReal_def, measureReal_def, ENNReal.toReal_le_toReal (by finiteness) (by finiteness)] at H
    convert H using 2 <;> ext x <;> simp [l,r,not_le.mpr hs',hs'.not_gt] <;> constructor <;> intro hh <;> linarith
  have heq : (fun x => r x - l x) = (fun x => f x - a) := by
    funext x; dsimp [r,l]; rcases le_total (f x) a with hh|hh <;> simp [max_def] <;> split_ifs <;> linarith
  have he := congrArg (fun j : E → ℝ => ∫ x, j x ∂P) heq
  simp only [integral_sub hr hl, integral_sub hf (integrable_const a), integral_const,probReal_univ,one_smul] at he
  linarith
end LognormalMedian

namespace LognormalMedian
open Filter Real MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

/-- If the probability below a is less than one half, reflection bounds the lower tail by the upper tail. Integrating the tails gives the mean bound. -/
theorem mean_of_small_cdf {n : ℕ} {f : V n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hm : ∀ x y, f (fun i => (x i + y i)/2) ≤ (f x+f y)/2)
    (hi : Integrable f (Γ n)) {a : ℝ} (ha : (Γ n).real {x | f x ≤ a} < 1/2) : a ≤ ∫ x, f x ∂Γ n := by
  have hΦ0 : Φ 0 = 1/2 := by have h := Φ_neg 0; rw [neg_zero] at h; linarith
  have hn := (CDF_lim hf.continuous a).eventually_lt_const ((limit_bounds hf.continuous a).2.trans_lt ha)
  apply tail_mean hi
  intro s hs
  have hl : limitCDF f (a-s) + limitCDF f (a+s) ≤ 1 := by
    apply le_of_tendsto ((CDF_lim hf.continuous (a-s)).add (CDF_lim hf.continuous (a+s)))
    filter_upwards [hn] with k hk
    let H := fun (v : ℝ) (x : V n) => (k:ℝ)*(v-f x)
    have hL (v : ℝ) : LipschitzWith ((k:ℝ≥0)*L) (H v) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [H,Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k),NNReal.coe_mul, NNReal.coe_natCast]
      rw [show v-f x-(v-f y)=f y-f x by ring,abs_sub_comm]
      simpa only [← mul_assoc, Real.dist_eq] using mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (Nat.cast_nonneg (α := ℝ) k)
    have h := foldN_midpoint (hL (a-s)) (hL (a+s)) (hL a) (by
      intro x y; dsimp [H]; nlinarith [mul_le_mul_of_nonneg_left (hm x y) (Nat.cast_nonneg (α := ℝ) k)])
    have hF (v : ℝ) : Φ (foldN (H v)) = smoothCDF f k v := Φ_Q (gen_integral_Φ_mem (hL v).continuous)
    have hneg : foldN (H a) < 0 := normal_cdf_strict.lt_iff_lt.mp (by rwa [hF,hΦ0])
    have hle : foldN (H (a-s)) ≤ -foldN (H (a+s)) := by linarith
    have hr := normal_cdf_strict.monotone hle
    rw [Φ_neg, hF, hF] at hr
    linarith
  have H1 := (limit_bounds hf.continuous (a-s)).1
  have H2 := (limit_bounds hf.continuous (a+s)).1
  have H3 := measureReal_add_measureReal_compl (μ := Γ n) (measurableSet_lt hf.continuous.measurable (measurable_const (a := a+s)))
  rw [probReal_univ,show {x | f x < a+s}ᶜ = {x | a+s ≤ f x} by ext; simp] at H3
  linarith

theorem median_le_expectation {n : ℕ} {f : V n → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hm : ∀ x y, f (fun i => (x i+y i)/2) ≤ (f x+f y)/2)
    (hi : Integrable f (Γ n))
    (hfull : ∀ a b : ℝ, a < b → 0 < (Γ n).real {x | a < f x ∧ f x < b})
    {m : ℝ} (hmedian : 1/2 ≤ (Γ n).real {x | m ≤ f x}) : m ≤ ∫ x, f x ∂Γ n := by
  by_contra! hbad
  obtain ⟨a,ha,ham⟩ := exists_between hbad
  apply ha.not_ge (mean_of_small_cdf hf hm hi ?_)
  let S := {x | a < f x ∧ f x < m}
  let T := {x | m ≤ f x}
  have hdis : Disjoint S T := disjoint_left.mpr fun x hx hy => hx.2.not_ge hy
  have hmeas : MeasurableSet T := measurableSet_le measurable_const hf.continuous.measurable
  have hin : S ∪ T ⊆ {x | f x ≤ a}ᶜ := by
    rintro x (hx|hx)
    · exact hx.1.not_ge
    · exact (ham.trans_le hx).not_ge
  have h := measureReal_mono (μ := Γ n) hin
  rw [measureReal_union hdis hmeas,measureReal_compl (measurableSet_le hf.continuous.measurable measurable_const),probReal_univ] at h
  have hs : 0 < (Γ n).real S := hfull a m ham
  change 1/2 ≤ (Γ n).real T at hmedian
  linarith
end LognormalMedian

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace LognormalMedian

/-- The root only gives laws of the coordinate logarithms. These laws already
give the measurability required by the finite-product independence theorem. -/
theorem joint_log_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (x : Fin n → Ω → ℝ) (μ : ℝ) (v : NNReal)
    (hi : iIndepFun x P)
    (hl : ∀ i, P.map (fun ω => log (x i ω)) = gaussianReal μ v) :
    P.map (fun ω i => log (x i ω)) = Measure.pi (fun _ : Fin n => gaussianReal μ v) := by
  let L := fun (i : Fin n) (ω : Ω) => log (x i ω)
  have hm (i) : AEMeasurable (L i) P := by
    apply AEMeasurable.of_map_ne_zero
    change P.map (fun ω => log (x i ω)) ≠ 0
    rw [hl i]
    exact IsProbabilityMeasure.ne_zero _
  have hL : iIndepFun L P := hi.comp (fun _ => log) (fun _ => measurable_log)
  exact (hL.map_fun_eq_pi_map hm).trans (congrArg Measure.pi (funext hl))

/-- Cauchy--Schwarz in precisely the form needed for midpoint convexity. -/
theorem midpoint_exp_sum {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    (∑ i, exp ((u i + v i) / 2)) ^ 2 ≤ (∑ i, exp (u i)) * ∑ i, exp (v i) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; positivity
  · intro i _; positivity
  · intro i _
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring

/-- Passing from the multiplicative midpoint inequality to logarithms. -/
theorem midpoint_log_sum {ι : Type*} [Fintype ι] [Nonempty ι] (u v : ι → ℝ) :
    log (∑ i, exp ((u i + v i) / 2)) ≤
      (log (∑ i, exp (u i)) + log (∑ i, exp (v i))) / 2 := by
  have hs (w : ι → ℝ) : 0 < ∑ i, exp (w i) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have h := Real.log_le_log (sq_pos_of_pos (hs (fun i => (u i + v i) / 2)))
    (midpoint_exp_sum u v)
  rw [Real.log_pow, Real.log_mul (hs u).ne' (hs v).ne'] at h
  norm_num at h
  linarith

/-- Strictness follows from nonconstancy of the log mean. -/
theorem strict_exp_mean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Integrable f P)
    (he : Integrable (Real.exp ∘ f) P)
    (hnc : ¬ f =ᵐ[P] Function.const Ω (∫ ω, f ω ∂P)) :
    Real.exp (∫ ω, f ω ∂P) < ∫ ω, Real.exp (f ω) ∂P := by
  have h := strictConvexOn_exp.ae_eq_const_or_map_average_lt
    Real.continuous_exp.continuousOn isClosed_univ (ae_of_all P fun _ => Set.mem_univ _) hf he
  simpa only [average_eq_integral] using h.resolve_left (by simpa only [average_eq_integral] using hnc)

end LognormalMedian

namespace LognormalMedian
open Real MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable def stat {n : ℕ} (μ σ : ℝ) (x : V n) :=
  log (∑ i, exp (μ+σ*x i)) - log n

private theorem sum_exp_pos {n : ℕ} [Nonempty (Fin n)] (u : V n) : 0 < ∑ i, exp (u i) :=
  Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty

private theorem exp_stat {n : ℕ} (hn : 0 < n) (μ σ : ℝ) (x : V n) :
    exp (stat μ σ x) = (1/(n:ℝ))*∑ i, exp (μ+σ*x i) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [stat, exp_sub, exp_log (sum_exp_pos _),exp_log (Nat.cast_pos.mpr hn)]
  ring

private theorem stat_lip {n : ℕ} (hn : 0 < n) (μ σ : ℝ) (hσ : 0 < σ) :
    LipschitzWith σ.toNNReal (stat (n := n) μ σ) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have bound (x y : V n) : stat μ σ x - stat μ σ y ≤ σ*dist x y := by
    have he (i : Fin n) : exp (μ+σ*x i) ≤ exp (σ*dist x y)*exp (μ+σ*y i) := by
      rw [← exp_add,exp_le_exp]
      have h := dist_le_pi_dist x y i
      rw [Real.dist_eq] at h
      nlinarith [mul_le_mul_of_nonneg_left ((le_abs_self _).trans h) hσ.le]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => he i)
    rw [← Finset.mul_sum] at hs
    have hlog := log_le_log (sum_exp_pos _) hs
    rw [log_mul (exp_pos _).ne' (sum_exp_pos _).ne', log_exp] at hlog
    dsimp [stat]; linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_sub_le_iff,Real.coe_toNNReal _ hσ.le]
  exact ⟨bound x y,by simpa only [dist_comm y x] using bound y x⟩

private theorem stat_mid {n : ℕ} (hn : 0 < n) (μ σ : ℝ) (x y : V n) :
    stat μ σ (fun i => (x i+y i)/2) ≤ (stat μ σ x + stat μ σ y)/2 := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have h := midpoint_log_sum (fun i => μ+σ*x i) (fun i => μ+σ*y i)
  simp only [show ∀ i, (μ+σ*x i+(μ+σ*y i))/2 = μ+σ*((x i+y i)/2) by intro i;ring] at h
  dsimp [stat]; linarith

private theorem stat_full {n : ℕ} (hn : 0 < n) (μ σ : ℝ) (hσ : 0 < σ) :
    ∀ a b : ℝ, a < b → 0 < (Γ n).real {x | a < stat μ σ x ∧ stat μ σ x < b} := by
  let : Measure.IsOpenPosMeasure γ := (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  intro a b hab
  let q := ((a+b)/2-μ)/σ
  have hq : stat μ σ (fun _ : Fin n => q) = (a+b)/2 := by
    dsimp [stat]
    simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,log_mul (Nat.cast_pos.mpr hn).ne' (exp_pos _).ne',log_exp]
    dsimp [q]; field_simp; ring
  have ho := (isOpen_Ioo (a := a) (b := b)).preimage (stat_lip hn μ σ hσ).continuous
  have hp := ho.measure_pos (Γ n) (show ((stat μ σ) ⁻¹' Ioo a b).Nonempty from ⟨fun _ => q, by change a < _ ∧ _ < b; rw [hq]; constructor <;> linarith⟩)
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

private theorem integrable_stat {n : ℕ} (hn : 0 < n) (μ σ : ℝ) (hσ : 0 < σ) :
    Integrable (stat (n := n) μ σ) (Γ n) ∧ Integrable (exp ∘ stat (n := n) μ σ) (Γ n) := by
  let f := stat (n := n) μ σ
  have hf := stat_lip hn μ σ hσ
  have hid : Integrable (fun x : V n => x) (Γ n) := Integrable.of_eval (fun i => integrable_eval (μ := fun _ => γ) IsGaussian.integrable_id)
  constructor
  · apply ((integrable_const |f 0|).add (hid.norm.const_mul σ)).mono' hf.continuous.aestronglyMeasurable
    apply ae_of_all
    intro x
    have hh := hf.dist_le_mul x 0
    rw [Real.dist_eq,dist_zero_right,Real.coe_toNNReal _ hσ.le] at hh
    have htri := abs_add_le (f x-f 0) (f 0)
    change |f x| ≤ |f 0|+σ*‖x‖
    rw [sub_add_cancel] at htri
    linarith
  · have hx (i : Fin n) : Integrable (fun x : V n => exp (σ*x i)) (Γ n) :=
      integrable_comp_eval (μ := fun _ => γ) (integrable_exp_mul_gaussianReal σ)
    have hi := (integrable_finsetSum Finset.univ (fun i _ => (hx i).const_mul (exp μ))).const_mul (1/(n:ℝ))
    apply hi.congr
    exact ae_of_all _ fun x => by simp [Function.comp_apply,exp_stat hn,exp_add]

theorem median_exp_stat {n : ℕ} (hn : 0 < n) (μ σ : ℝ) (hσ : 0 < σ) (m : ℝ)
    (hm : 1/2 ≤ (Γ n).real {x | m ≤ exp (stat μ σ x)}) :
    m < ∫ x, exp (stat μ σ x) ∂Γ n := by
  let f := stat (n := n) μ σ
  let c := ∫ x, f x ∂Γ n
  have ⟨hi,he⟩ := integrable_stat hn μ σ hσ
  have hfull := stat_full hn μ σ hσ
  have hnc : ¬ f =ᵐ[Γ n] Function.const (V n) c := by
    intro hc
    have hz : (Γ n) {x | c+1 < f x ∧ f x < c+2} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hc] with x hx
      change f x = c at hx
      change ¬ (_ ∧ _)
      rintro ⟨h,_⟩; change c+1 < f x at h; rw [hx] at h; linarith
    have H := hfull (c+1) (c+2) (by linarith)
    change 0 < ((Γ n) {x | c+1 < f x ∧ f x < c+2}).toReal at H
    simp [hz] at H
  have hs : exp c < ∫ x, exp (f x) ∂Γ n := strict_exp_mean _ hi he hnc
  apply lt_of_le_of_lt _ hs
  by_cases hp : 0 < m
  · have hset : {x | m ≤ exp (f x)} = {x | log m ≤ f x} := by
      ext x; exact (log_le_iff_le_exp hp).symm
    change 1/2 ≤ (Γ n).real {x | m ≤ exp (f x)} at hm
    rw [hset] at hm
    exact (log_le_iff_le_exp hp).mp (median_le_expectation (stat_lip hn μ σ hσ) (stat_mid hn μ σ) hi hfull hm)
  · exact (not_lt.mp hp).trans (exp_pos _).le
end LognormalMedian

open LognormalMedian Real MeasureTheory ProbabilityTheory Set

theorem OMA.solution : type_of% @OMA.S_mo_271503.main := by
  intro n hn μ σ hσ Ω _ _ x hind hpos hlaw m _ hmed
  let P := (ℙ : Measure Ω)
  let v := (σ^2).toNNReal
  let logs := fun ω (i : Fin n) => log (x i ω)
  let affine := fun (z : V n) (i : Fin n) => μ+σ*z i
  let meanExp := fun z : V n => (1/(n:ℝ))*∑ i, exp (z i)
  let Y := fun ω => (1/(n:ℝ))*∑ i, x i ω
  have haff : MeasurePreserving (fun w : ℝ => μ+σ*w) γ (gaussianReal μ v) := by
    refine ⟨by fun_prop, ?_⟩
    rw [show (fun w : ℝ => μ+σ*w) = (μ+·) ∘ (σ*·) by rfl, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul,gaussianReal_map_const_add]
    congr 1
    · ring
    · ext
      simp [v,Real.coe_toNNReal _ (sq_nonneg σ)]
  have hp : MeasurePreserving affine (Γ n) (Measure.pi (fun _ : Fin n => gaussianReal μ v)) :=
    measurePreserving_pi _ _ fun _ => haff
  have hlogs : P.map logs = Measure.pi (fun _ : Fin n => gaussianReal μ v) := joint_log_law P x μ v hind hlaw
  have hid : IdentDistrib logs affine P (Γ n) := ⟨AEMeasurable.of_map_ne_zero (hlogs ▸ IsProbabilityMeasure.ne_zero _),
    hp.measurable.aemeasurable,hlogs.trans hp.map_eq.symm⟩
  have hmean := hid.comp (u := meanExp) (by dsimp [meanExp]; fun_prop)
  have heq : meanExp ∘ logs =ᵐ[P] Y := by
    filter_upwards [ae_all_iff.mpr hpos] with ω hω
    dsimp [meanExp,logs,Y]
    simp only [exp_log (hω _)]
  have hy := (IdentDistrib.of_ae_eq hmean.aemeasurable_fst heq).symm.trans hmean
  have hfun : meanExp ∘ affine = fun z => exp (stat μ σ z) := by
    funext z
    exact (exp_stat hn μ σ z).symm
  rw [hfun] at hy
  have hprob := congrArg ENNReal.toReal (hy.measure_mem_eq (measurableSet_Ici (a := m)))
  change P.real {ω | m ≤ Y ω} = (Γ n).real {z | m ≤ exp (stat μ σ z)} at hprob
  change 1/2 ≤ P.real {ω | m ≤ Y ω} at hmed
  change m < ∫ ω, Y ω ∂P
  rw [hy.integral_eq]
  exact median_exp_stat hn μ σ hσ m (hprob ▸ hmed)
