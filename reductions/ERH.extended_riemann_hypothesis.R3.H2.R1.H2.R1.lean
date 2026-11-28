import OMAReductions.R_ERH_extended_riemann_hypothesis_R3_H2_R1
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall

/-! A single reciprocal Taylor germ at the real point 2 detects zeros in the
open half-plane to the right of 31/32, via the unit disk. -/
namespace OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1
open Complex Filter Set Metric NumberField
open scoped Topology NNReal ENNReal

/-- Entire regularization of the ideal series, including the classical
zero-free closed half-plane to the right of one. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
    (∀ s : ℂ, 1 < s.re → W s = (s-1)*dedekindZeta K s) ∧
    ∀ s : ℂ, 1 ≤ s.re → W s ≠ 0

/-- Subexponential growth of the Taylor coefficients of the transformed
reciprocal arithmetic germ. All derivatives are evaluated at zero. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let T := fun w : ℂ => (2+w/16)/(1-w)
    let G := fun w : ℂ => (((T w)-1)*dedekindZeta K (T w))⁻¹
    ∀ r : ℝ, 0 < r → r < 1 → ∃ C : ℝ, ∀ n : ℕ,
      ‖iteratedDeriv n G 0 / n.factorial‖ * r^n ≤ C

theorem inverse_coordinate {s : ℂ} (hs : 31/32 < s.re) :
    let w := (s-2)/(s+1/16)
    ‖w‖ < 1 ∧ (2+w/16)/(1-w) = s := by
  let w := (s-2)/(s+1/16)
  have hd : s+1/16 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  have hlt : ‖s-2‖ < ‖s+1/16‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),Complex.sq_norm,Complex.sq_norm]
    simp only [Complex.normSq_apply,sub_re,sub_im,add_re,add_im]
    norm_num
    nlinarith
  have hw : ‖w‖ < 1 := by
    rw [show ‖w‖ = ‖s-2‖/‖s+1/16‖ from norm_div _ _, div_lt_one (norm_pos_iff.mpr hd)]
    exact hlt
  have hw1 : 1-w ≠ 0 := sub_ne_zero.mpr (fun e => by rw [← e] at hw; simpa using hw)
  refine ⟨hw, (div_eq_iff hw1).mpr ?_⟩
  have hwrel : w*(s+1/16) = s-2 := div_mul_cancel₀ _ hd
  change 2+w/16 = s*(1-w)
  linear_combination hwrel

theorem coefficient_radius (a : ℕ → ℂ)
    (hb : ∀ r : ℝ, 0 < r → r < 1 → ∃ C : ℝ, ∀ n : ℕ, ‖a n‖*r^n ≤ C) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hlt
  obtain ⟨C,hC⟩ := hb r (by exact_mod_cast hr) (by exact_mod_cast hlt)
  apply (FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_bound C
  simpa only [FormalMultilinearSeries.ofScalars_norm] using hC

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R1.H2 := by
  intro h1 h2 K _ _
  obtain ⟨W,hW,hagree,hfree⟩ := h1 K
  let T := fun w : ℂ => (2+w/16)/(1-w)
  let G := fun w : ℂ => (((T w)-1)*dedekindZeta K (T w))⁻¹
  let a := fun n : ℕ => iteratedDeriv n G 0 / n.factorial
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hrad : 1 ≤ p.radius := coefficient_radius a (h2 K)
  have hT0 : T 0 = 2 := by norm_num [T]
  have hT {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ T w := by
    have hd : 1-w ≠ 0 := sub_ne_zero.mpr (fun e => by rw [← e] at hw; simpa using hw)
    exact (analyticAt_const.add analyticAt_id.div_const).div (analyticAt_const.sub analyticAt_id) hd
  have hWg (w : ℂ) (hw : ‖w‖ < 1) : AnalyticAt ℂ (fun v => W (T v)) w :=
    (hW.differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)).comp (hT hw)
  have hnear : ∀ᶠ w : ℂ in 𝓝 0, 1 < (T w).re :=
    (hT (w := 0) (by norm_num)).continuousAt.tendsto
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (T 0).re by rw [hT0]; norm_num))
  have hge : G =ᶠ[𝓝 0] (fun w => (W (T w))⁻¹) := by
    filter_upwards [hnear] with w hw
    rw [hagree (T w) hw]
  have hGa : AnalyticAt ℂ G 0 :=
    ((hWg 0 (by norm_num)).inv (hfree _ (by rw [hT0]; norm_num))).congr hge.symm
  obtain ⟨r,hr⟩ : HasFPowerSeriesAt G p 0 := hGa.hasFPowerSeriesAt
  have local_id : (fun w => W (T w) * p.sum w) =ᶠ[𝓝 0] (fun _ => 1) := by
    filter_upwards [eball_mem_nhds (0:ℂ) hr.r_pos, hge, hnear] with w hw he hright
    have hsum : p.sum w = G w := by simpa using (hr.sum hw).symm
    rw [hsum,he,mul_inv_cancel₀ (hfree _ hright.le)]
  have hprod : AnalyticOnNhd ℂ (fun w => W (T w) * p.sum w) (ball 0 1) := by
    intro w hw
    have hnorm : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    apply (hWg w hnorm).mul
    apply p.analyticOnNhd
    apply eball_subset_eball hrad
    rwa [← ENNReal.ofReal_one,Metric.eball_ofReal]
  have heq := hprod.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball (0:ℂ) 1).isPreconnected (mem_ball_self (by norm_num : (0:ℝ)<1)) local_id
  refine ⟨fun z => W z/(z-1), ⟨?_,?_⟩,?_⟩
  · intro z hz
    exact ((hW z).div (differentiableAt_id.sub_const (1:ℂ))
      (sub_ne_zero.mpr (show z ≠ 1 from hz))).differentiableWithinAt
  · intro s hs
    have hn : s ≠ 1 := by rintro rfl; norm_num at hs
    change W s/(s-1) = dedekindZeta K s
    rw [hagree s hs,mul_div_cancel_left₀ _ (sub_ne_zero.mpr hn)]
  · intro s hs hn
    obtain ⟨hw,hback⟩ := inverse_coordinate hs
    have e := heq (mem_ball_zero_iff.mpr hw)
    change W ((2+((s-2)/(s+1/16))/16)/(1-(s-2)/(s+1/16))) * _ = 1 at e
    rw [hback] at e
    exact div_ne_zero (fun h => by simp [h] at e) (sub_ne_zero.mpr hn)

end OMA.R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1
