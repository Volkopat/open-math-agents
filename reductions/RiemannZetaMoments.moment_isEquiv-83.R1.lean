import FormalConjectures.Paper.RiemannZetaMoments
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Reduction of `RiemannZetaMoments.moment_isEquiv₂`

Following A. E. Ingham (*Mean-value theorems in the theory of the Riemann zeta-function*,
Proc. London Math. Soc. 27 (1926), 273–300), we reduce the fourth-moment asymptotic
$$\frac{1}{T}\int_0^T \left|\zeta\!\left(\tfrac12 + it\right)\right|^4 dt \sim \frac{1}{2\pi^2}(\log T)^4$$
to three independent classical analytic number theory pillars for the balanced approximate
functional equation of $\zeta(s)^2$:
1. `H1`: **Approximate functional equation $L^2$-error for $\zeta^2$**: the balanced Dirichlet
   polynomial model `M t = D t + χ₂ t * star (D t)` (with divisor coefficients `σ 0 n`, cutoff
   `⌊t / (2 * π)⌋₊`, and functional-equation phase `χ₂ t = (Gammaℝ (1/2 - I*t) / Gammaℝ (1/2 + I*t))²`)
   approximates `ζ(1/2 + I * t)²` with integrated squared error `o(T (log T)⁴)` (and `‖M ·‖²`,
   `‖ζ² - M‖²` interval-integrable on `[0, T]`).
2. `H2`: **Off-diagonal and oscillatory cross-term cancellation**: the integrated squared norm of
   `M t` matches twice the moving-cutoff divisor-squared diagonal sum up to `o(T (log T)⁴)`.
3. `H3`: **Divisor-squared harmonic sum asymptotic (Ramanujan–Wilson–Ingham)**:
   $$\sum_{1 \le n \le X} \frac{d(n)^2}{n} \sim \frac{1}{4\pi^2} (\log X)^4 \qquad (X \to \infty).$$

Inside `main`, we prove from scratch:
- Continuity and `IntervalIntegrable` of `‖ζ(1/2 + I * t)‖⁴` on `[0, T]`.
- Pointwise AM-GM norm-square perturbation `|‖a‖² - ‖b‖²| ≤ ε * ‖b‖² + (1 + ε⁻¹) * ‖a - b‖²` for
  every `ε > 0`, lifting `H1` (`L²` error `o(T log⁴ T)`) to
  `(∫₀ᵀ ‖ζ(1/2 + I*t)‖⁴ - ∫₀ᵀ ‖M t‖²) = o(T (log T)⁴)`.
- Monotonicity and interval-integrability of `S(X) = ∑_{1 ≤ n ≤ ⌊X⌋₊} d(n)² / n`, and the
  upper/lower `[δ T, T]` monotonicity sandwich lifting `H3` to
  `∫₀ᵀ S(t / (2 * π)) dt ~ (1 / (4 * π²)) * T * (log T)⁴`.
- Assembly with `H2` and division by `T` to obtain `moment 2 ~[atTop] fun T ↦ (1 / (2 * π²)) * T.log ^ 4`.

Thanks to @MechaNuggan for the balanced `ζ²` approximate functional equation model and
divisor-squared diagonal reduction analysis.
Credit: @tkaiman
-/

namespace OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1

open Complex Filter Real Asymptotics MeasureTheory ArithmeticFunction
open scoped BigOperators Topology

private noncomputable def divSqDiag (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)

private noncomputable def zetaSqDirPoly (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊,
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))

private noncomputable def zetaSqModel (t : ℝ) : ℂ :=
  zetaSqDirPoly t +
    (Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ)) /
      Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) ^ 2 * star (zetaSqDirPoly t)

private lemma divSqDiag_nonneg (X : ℝ) : 0 ≤ divSqDiag X :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private lemma divSqDiag_mono : Monotone divSqDiag := by
  intro x y hxy
  unfold divSqDiag
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  intro n hn
  rw [Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, hn.2.trans (Nat.floor_mono hxy)⟩

private lemma abs_norm_sq_sub_le (a b : ℂ) {ε : ℝ} (hε : 0 < ε) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ ε * ‖b‖ ^ 2 + (1 + ε⁻¹) * ‖a - b‖ ^ 2 := by
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : ‖a‖ + ‖b‖ ≤ 2 * ‖b‖ + ‖a - b‖ := by
    have : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := le_trans (le_abs_self _) h1
    linarith
  have hprod : |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ ‖a - b‖ * (2 * ‖b‖ + ‖a - b‖) := by
    have hfac : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
    exact mul_le_mul h1 h2 (add_nonneg (norm_nonneg a) (norm_nonneg b)) (norm_nonneg (a - b))
  have hamgm : 2 * ‖a - b‖ * ‖b‖ ≤ ε * ‖b‖ ^ 2 + ε⁻¹ * ‖a - b‖ ^ 2 := by
    have hsq : 0 ≤ (Real.sqrt ε * ‖b‖ - (Real.sqrt ε)⁻¹ * ‖a - b‖) ^ 2 := sq_nonneg _
    have hεsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
    have hexp : (Real.sqrt ε * ‖b‖ - (Real.sqrt ε)⁻¹ * ‖a - b‖) ^ 2 =
        ε * ‖b‖ ^ 2 + ε⁻¹ * ‖a - b‖ ^ 2 - 2 * ‖a - b‖ * ‖b‖ := by
      calc (Real.sqrt ε * ‖b‖ - (Real.sqrt ε)⁻¹ * ‖a - b‖) ^ 2
          = Real.sqrt ε ^ 2 * ‖b‖ ^ 2 + (Real.sqrt ε)⁻¹ ^ 2 * ‖a - b‖ ^ 2 -
              2 * (Real.sqrt ε * (Real.sqrt ε)⁻¹) * ‖a - b‖ * ‖b‖ := by ring
        _ = ε * ‖b‖ ^ 2 + ε⁻¹ * ‖a - b‖ ^ 2 - 2 * ‖a - b‖ * ‖b‖ := by
              rw [inv_pow, hεsq, mul_inv_cancel₀ hne]; ring
    linarith
  nlinarith

private lemma log_div_const_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => (Real.log (c * T) / Real.log T) ^ 4) atTop (𝓝 1) := by
  have h0 : Tendsto (fun T : ℝ => Real.log c / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h1 : Tendsto (fun T : ℝ => 1 + Real.log c / Real.log T) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h1
  have hev : (fun T : ℝ => Real.log (c * T) / Real.log T) =ᶠ[atTop]
      (fun T : ℝ => 1 + Real.log c / Real.log T) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hTpos : 0 < T := by linarith
    have hlog : Real.log T ≠ 0 := (Real.log_pos hT).ne'
    rw [Real.log_mul hc.ne' hTpos.ne', add_div, div_self hlog]
    ring
  have hbase : Tendsto (fun T : ℝ => Real.log (c * T) / Real.log T) atTop (𝓝 1) :=
    h1.congr' hev.symm
  simpa using hbase.pow 4

private lemma integral_divSqDiag_isEquiv
    (hdiag : divSqDiag ~[atTop] fun X : ℝ => (1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4) :
    (fun T : ℝ => ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) ~[atTop]
      fun T : ℝ => (1 / (4 * Real.pi ^ 2)) * (T * Real.log T ^ 4) := by
  set c0 : ℝ := 1 / (4 * Real.pi ^ 2)
  have hc0 : 0 < c0 := by positivity
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  swap
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have : 0 < Real.log T := Real.log_pos hT
    positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose δ ∈ (0, 1) and η > 0 small enough that upper and lower bounds lie within ε of 1
  let δ : ℝ := min (1 / 2) (ε / 4)
  have hδpos : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδlt1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδle : δ ≤ ε / 4 := min_le_right _ _
  have hratio : Tendsto (fun X : ℝ => divSqDiag X / (c0 * Real.log X ^ 4)) atTop (𝓝 1) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp hdiag
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have : 0 < Real.log X := Real.log_pos hX
    positivity
  have hscale_hi : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop :=
    Filter.Tendsto.atTop_div_const h2pi tendsto_id
  have hscale_lo : Tendsto (fun T : ℝ => (δ / (2 * Real.pi)) * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
  have hhi_lim : Tendsto (fun T : ℝ => divSqDiag (T / (2 * Real.pi)) / (c0 * Real.log T ^ 4))
      atTop (𝓝 1) := by
    have hcomp := (hratio.comp hscale_hi).mul (log_div_const_tendsto_one (c := (2 * Real.pi)⁻¹) (by positivity))
    rw [mul_one] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (max 2 (4 * Real.pi))] with T hT
    have hT2 : 2 < T := lt_of_le_of_lt (le_max_left _ _) hT
    have hT4 : 4 * Real.pi < T := lt_of_le_of_lt (le_max_right _ _) hT
    have hlogT : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hlogT2 : Real.log (T / (2 * Real.pi)) ≠ 0 :=
      (Real.log_pos (by rw [one_lt_div h2pi]; linarith)).ne'
    have hmul : (2 * Real.pi)⁻¹ * T = T / (2 * Real.pi) := by ring
    dsimp [Function.comp_def]
    rw [hmul, div_pow]
    field_simp [hc0.ne', hlogT, hlogT2]
  have hlo_lim : Tendsto (fun T : ℝ => (1 - δ) * (divSqDiag ((δ / (2 * Real.pi)) * T) / (c0 * Real.log T ^ 4)))
      atTop (𝓝 (1 - δ)) := by
    have hcomp := (hratio.comp hscale_lo).mul (log_div_const_tendsto_one (c := δ / (2 * Real.pi)) (by positivity))
    rw [mul_one] at hcomp
    have hcomp' := hcomp.const_mul (1 - δ)
    rw [mul_one] at hcomp'
    refine hcomp'.congr' ?_
    filter_upwards [eventually_gt_atTop (max 2 (4 * Real.pi / δ))] with T hT
    have hT2 : 2 < T := lt_of_le_of_lt (le_max_left _ _) hT
    have hT4 : 4 * Real.pi / δ < T := lt_of_le_of_lt (le_max_right _ _) hT
    have hlogT : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
    have harg1 : 1 < (δ / (2 * Real.pi)) * T := by
      have h1 : 4 * Real.pi < T * δ := (div_lt_iff₀ hδpos).mp hT4
      have : 2 * Real.pi < δ * T := by linarith
      calc (1 : ℝ) = (2 * Real.pi) / (2 * Real.pi) := (div_self h2pi.ne').symm
        _ < (δ * T) / (2 * Real.pi) := div_lt_div_of_pos_right this h2pi
        _ = (δ / (2 * Real.pi)) * T := by ring
    have hlogArg : Real.log ((δ / (2 * Real.pi)) * T) ≠ 0 := (Real.log_pos harg1).ne'
    dsimp [Function.comp_def]
    set L₁ := Real.log ((δ / (2 * Real.pi)) * T)
    set L₂ := Real.log T
    set D₁ := divSqDiag ((δ / (2 * Real.pi)) * T)
    rw [div_pow]
    field_simp [hc0.ne', hlogT, hlogArg]
  have hev_hi : ∀ᶠ T : ℝ in atTop,
      divSqDiag (T / (2 * Real.pi)) / (c0 * Real.log T ^ 4) < 1 + ε :=
    hhi_lim.eventually (Iio_mem_nhds (by linarith))
  have hev_lo : ∀ᶠ T : ℝ in atTop,
      1 - ε < (1 - δ) * (divSqDiag ((δ / (2 * Real.pi)) * T) / (c0 * Real.log T ^ 4)) :=
    hlo_lim.eventually (Ioi_mem_nhds (by linarith))
  have hev := (hev_hi.and hev_lo).and (eventually_gt_atTop (2 : ℝ))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨⟨hhi, hlo⟩, hT2⟩ := hT₀ T hT
  have hTpos : 0 < T := by linarith
  have hlog_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have hden_pos : 0 < c0 * (T * Real.log T ^ 4) := by positivity
  have hf_mono : Monotone (fun t : ℝ => divSqDiag (t / (2 * Real.pi))) := fun a b hab =>
    divSqDiag_mono (div_le_div_of_nonneg_right hab h2pi.le)
  have hint_full : IntervalIntegrable (fun t : ℝ => divSqDiag (t / (2 * Real.pi))) volume 0 T :=
    hf_mono.intervalIntegrable
  have hint_left : IntervalIntegrable (fun t : ℝ => divSqDiag (t / (2 * Real.pi))) volume 0 (δ * T) :=
    hf_mono.intervalIntegrable
  have hint_right : IntervalIntegrable (fun t : ℝ => divSqDiag (t / (2 * Real.pi))) volume (δ * T) T :=
    hf_mono.intervalIntegrable
  have hupper_int : ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi)) ≤
      T * divSqDiag (T / (2 * Real.pi)) := by
    calc ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))
        ≤ ∫ _t in (0 : ℝ)..T, divSqDiag (T / (2 * Real.pi)) :=
          intervalIntegral.integral_mono_on hTpos.le hint_full intervalIntegrable_const
            fun t ht => hf_mono ht.2
      _ = T * divSqDiag (T / (2 * Real.pi)) := by simp
  have hlower_int : (1 - δ) * T * divSqDiag ((δ / (2 * Real.pi)) * T) ≤
      ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi)) := by
    have hsplit : (∫ t in (0 : ℝ)..(δ * T), divSqDiag (t / (2 * Real.pi))) +
        (∫ t in (δ * T)..T, divSqDiag (t / (2 * Real.pi))) =
        ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi)) :=
      intervalIntegral.integral_add_adjacent_intervals hint_left hint_right
    have hleft_nn : 0 ≤ ∫ t in (0 : ℝ)..(δ * T), divSqDiag (t / (2 * Real.pi)) :=
      intervalIntegral.integral_nonneg (by positivity) fun t _ => divSqDiag_nonneg _
    have hδT_le : δ * T ≤ T := by nlinarith
    have hright_ge : (1 - δ) * T * divSqDiag ((δ / (2 * Real.pi)) * T) ≤
        ∫ t in (δ * T)..T, divSqDiag (t / (2 * Real.pi)) := by
      have hconst : ∫ _t in (δ * T)..T, divSqDiag ((δ / (2 * Real.pi)) * T) =
          (1 - δ) * T * divSqDiag ((δ / (2 * Real.pi)) * T) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hδT_le intervalIntegrable_const hint_right
        fun t ht => ?_
      have harg : (δ / (2 * Real.pi)) * T = (δ * T) / (2 * Real.pi) := by ring
      rw [harg]
      exact hf_mono ht.1
    linarith
  have hupper_ratio : (∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) / (c0 * (T * Real.log T ^ 4)) < 1 + ε := by
    have h1 : (∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) / (c0 * (T * Real.log T ^ 4)) ≤
        (T * divSqDiag (T / (2 * Real.pi))) / (c0 * (T * Real.log T ^ 4)) :=
      div_le_div_of_nonneg_right hupper_int hden_pos.le
    have h2 : (T * divSqDiag (T / (2 * Real.pi))) / (c0 * (T * Real.log T ^ 4)) =
        divSqDiag (T / (2 * Real.pi)) / (c0 * Real.log T ^ 4) := by
      field_simp [hTpos.ne', hc0.ne', hlog_pos.ne']
    linarith
  have hlower_ratio : 1 - ε <
      (∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) / (c0 * (T * Real.log T ^ 4)) := by
    have h1 : ((1 - δ) * T * divSqDiag ((δ / (2 * Real.pi)) * T)) / (c0 * (T * Real.log T ^ 4)) ≤
        (∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) / (c0 * (T * Real.log T ^ 4)) :=
      div_le_div_of_nonneg_right hlower_int hden_pos.le
    have h2 : ((1 - δ) * T * divSqDiag ((δ / (2 * Real.pi)) * T)) / (c0 * (T * Real.log T ^ 4)) =
        (1 - δ) * (divSqDiag ((δ / (2 * Real.pi)) * T) / (c0 * Real.log T ^ 4)) := by
      field_simp [hTpos.ne', hc0.ne', hlog_pos.ne']
    linarith
  rw [Real.dist_eq, abs_lt]
  dsimp only [Pi.div_apply]
  exact ⟨by linarith, by linarith⟩

-- ### Hypotheses and main reduction theorem

/-- **Approximate functional equation $L^2$-error for $\zeta(1/2 + it)^2$** (Ingham 1926):
with the balanced Dirichlet polynomial `D(t) = ∑_{1 ≤ n ≤ ⌊t/(2π)⌋₊} d(n) n^{-1/2 - it}` and
functional-equation phase `χ₂(t) = (Γℝ(1/2 - it) / Γℝ(1/2 + it))²`, the model
`M(t) = D(t) + χ₂(t) * star (D(t))` satisfies `∫₀ᵀ ‖ζ(1/2 + it)² - M(t)‖² dt = o(T (log T)⁴)`
(with `‖M(·)‖²` and `‖ζ(1/2 + i·)² - M(·)‖²` interval-integrable on `[0, T]`). -/
def H1 : Prop :=
  let D : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊,
      ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))
  let M : ℝ → ℂ := fun t =>
    D t + (Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ)) /
      Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) ^ 2 * star (D t)
  (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t : ℝ => ‖M t‖ ^ 2) volume 0 T) ∧
  (∀ T : ℝ, 0 ≤ T →
    IntervalIntegrable (fun t : ℝ => ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - M t‖ ^ 2)
      volume 0 T) ∧
  (fun T : ℝ => ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - M t‖ ^ 2)
    =o[atTop] fun T : ℝ => T * Real.log T ^ 4

/-- **Off-diagonal and oscillatory cross-term cancellation for the balanced $\zeta^2$ model**
(Ingham 1926): the integrated squared norm of the balanced model `M(t) = D(t) + χ₂(t) * star (D(t))`
agrees with twice the integrated moving-cutoff diagonal sum
`2 ∫₀ᵀ ∑_{1 ≤ n ≤ ⌊t/(2π)⌋₊} d(n)² / n dt` up to `o(T (log T)⁴)`. -/
def H2 : Prop :=
  let D : ℝ → ℂ := fun t =>
    ∑ n ∈ Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊,
      ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))
  let M : ℝ → ℂ := fun t =>
    D t + (Complex.Gammaℝ (1 / 2 - Complex.I * (t : ℂ)) /
      Complex.Gammaℝ (1 / 2 + Complex.I * (t : ℂ))) ^ 2 * star (D t)
  (fun T : ℝ =>
    (∫ t in (0 : ℝ)..T, ‖M t‖ ^ 2) -
    2 * ∫ t in (0 : ℝ)..T,
      ∑ n ∈ Finset.Icc 1 ⌊t / (2 * Real.pi)⌋₊,
        ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ))
    =o[atTop] fun T : ℝ => T * Real.log T ^ 4

/-- **Divisor-squared harmonic sum asymptotic** (Ramanujan–Wilson–Ingham):
`∑_{1 ≤ n ≤ ⌊X⌋₊} d(n)² / n ~ (1 / (4 * π²)) * (log X)⁴` as `X → ∞`. -/
def H3 : Prop :=
  (fun X : ℝ => ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ))
    ~[atTop] fun X : ℝ => (1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4

theorem main : H1 → H2 → H3 → type_of% @RiemannZetaMoments.moment_isEquiv₂ := by
  intro ⟨hM_int, herr_int, herr_o⟩ h2 h3
  set mainTerm : ℝ → ℝ := fun T => (1 / (2 * Real.pi ^ 2)) * (T * Real.log T ^ 4)
  have hdiag_int : (fun T : ℝ => ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) ~[atTop]
      fun T : ℝ => (1 / (4 * Real.pi ^ 2)) * (T * Real.log T ^ 4) :=
    integral_divSqDiag_isEquiv h3
  have h2diag : (fun T : ℝ => 2 * ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) ~[atTop]
      mainTerm := by
    have h := (Asymptotics.IsEquivalent.refl (u := fun _ : ℝ => (2 : ℝ))).mul hdiag_int
    refine (h.congr_left (Filter.Eventually.of_forall fun _ => rfl)).congr_right
      (Filter.Eventually.of_forall fun T => ?_)
    dsimp [mainTerm]; ring
  have h2_main : (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2) -
      2 * ∫ t in (0 : ℝ)..T, divSqDiag (t / (2 * Real.pi))) =o[atTop] mainTerm := by
    have hconst : (fun T : ℝ => T * Real.log T ^ 4) =O[atTop] mainTerm := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨2 * Real.pi ^ 2, Filter.Eventually.of_forall fun T => ?_⟩
      dsimp [mainTerm]
      rw [abs_mul (1 / (2 * Real.pi ^ 2)),
        abs_of_pos (show (0 : ℝ) < 1 / (2 * Real.pi ^ 2) by positivity)]
      field_simp [show (Real.pi : ℝ) ≠ 0 by exact Real.pi_ne_zero]
      exact le_rfl
    exact h2.trans_isBigO hconst
  have hM_equiv : (fun T : ℝ => ∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2) ~[atTop] mainTerm := by
    rw [Asymptotics.IsEquivalent] at h2diag ⊢
    have hadd := h2_main.add h2diag
    refine hadd.congr_left fun T => ?_
    dsimp only [Pi.sub_apply]
    ring
  have hzeta_cont : Continuous (fun t : ℝ => ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4) := by
    have hdiff : Differentiable ℝ (fun t : ℝ => riemannZeta (1 / 2 + Complex.I * (t : ℂ))) := by
      intro t
      have hne : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
        intro heq
        have hre := congrArg Complex.re heq
        simp at hre
      have hz := (differentiableAt_riemannZeta hne).restrictScalars ℝ
      have hlin : DifferentiableAt ℝ (fun u : ℝ => (1 / 2 : ℂ) + Complex.I * (u : ℂ)) t := by
        fun_prop
      exact hz.comp t hlin
    exact (hdiff.continuous.norm).pow 4
  have hzeta_sub_M : (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4) -
      (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2)) =o[atTop] mainTerm := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hM_O : (fun T : ℝ => ∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2) =O[atTop] mainTerm :=
      hM_equiv.isBigO
    rw [Asymptotics.isBigO_iff] at hM_O
    obtain ⟨C, hC_ev⟩ := hM_O
    have hC1 : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    let ε : ℝ := c / (2 * max C 1)
    have hε : 0 < ε := by positivity
    have herr_main : (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2) =o[atTop] mainTerm := by
      have hconst : (fun T : ℝ => T * Real.log T ^ 4) =O[atTop] mainTerm := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨2 * Real.pi ^ 2, Filter.Eventually.of_forall fun T => ?_⟩
        dsimp [mainTerm]
        rw [abs_mul (1 / (2 * Real.pi ^ 2)),
          abs_of_pos (show (0 : ℝ) < 1 / (2 * Real.pi ^ 2) by positivity)]
        field_simp [show (Real.pi : ℝ) ≠ 0 by exact Real.pi_ne_zero]
        exact le_rfl
      exact herr_o.trans_isBigO hconst
    have herr_small := (Asymptotics.isLittleO_iff.mp herr_main) (show 0 < c / (2 * (1 + ε⁻¹)) by positivity)
    filter_upwards [hC_ev, herr_small, eventually_gt_atTop (1 : ℝ)] with T hCT herrT hT1
    have hT0 : 0 ≤ T := by linarith
    have hmain_pos : 0 < mainTerm T := by
      dsimp [mainTerm]
      have : 0 < Real.log T := Real.log_pos hT1
      positivity
    have hint_z : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4)
        volume 0 T := hzeta_cont.intervalIntegrable 0 T
    have hint_M : IntervalIntegrable (fun t : ℝ => ‖zetaSqModel t‖ ^ 2) volume 0 T :=
      hM_int T hT0
    have hint_e : IntervalIntegrable
        (fun t : ℝ => ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2)
        volume 0 T := herr_int T hT0
    have hnorm_sub : ‖(∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4) -
        (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2)‖ ≤
        ε * (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2) +
        (1 + ε⁻¹) * (∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2) := by
      rw [← intervalIntegral.integral_sub hint_z hint_M]
      have h1 : ‖∫ t in (0 : ℝ)..T,
          (‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4 - ‖zetaSqModel t‖ ^ 2)‖ ≤
          ∫ t in (0 : ℝ)..T,
            |‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4 - ‖zetaSqModel t‖ ^ 2| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
          (f := fun t : ℝ => ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4 - ‖zetaSqModel t‖ ^ 2) hT0
      have h2 : ∫ t in (0 : ℝ)..T,
            |‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4 - ‖zetaSqModel t‖ ^ 2| ≤
          ∫ t in (0 : ℝ)..T,
            (ε * ‖zetaSqModel t‖ ^ 2 +
              (1 + ε⁻¹) * ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on hT0 (hint_z.sub hint_M).abs
          ((hint_M.const_mul ε).add (hint_e.const_mul (1 + ε⁻¹))) fun t _ => ?_
        have hsq4 : ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4 =
            ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2‖ ^ 2 := by
          rw [norm_pow]; ring
        rw [hsq4]
        exact abs_norm_sq_sub_le _ _ hε
      have h3 : ∫ t in (0 : ℝ)..T,
            (ε * ‖zetaSqModel t‖ ^ 2 +
              (1 + ε⁻¹) * ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2) =
          ε * (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2) +
          (1 + ε⁻¹) * (∫ t in (0 : ℝ)..T,
            ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2) := by
        rw [intervalIntegral.integral_add (hint_M.const_mul ε) (hint_e.const_mul (1 + ε⁻¹)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      linarith
    have hM_nn : 0 ≤ ∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT0 fun t _ => sq_nonneg _
    have he_nn : 0 ≤ ∫ t in (0 : ℝ)..T,
        ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT0 fun t _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hM_nn, Real.norm_eq_abs, abs_of_pos hmain_pos] at hCT
    rw [Real.norm_eq_abs, abs_of_nonneg he_nn, Real.norm_eq_abs, abs_of_pos hmain_pos] at herrT
    simp only [Real.norm_eq_abs, abs_of_pos hmain_pos] at hnorm_sub ⊢
    have hterm1 : ε * (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2) ≤ (c / 2) * mainTerm T := by
      have hC_le : C ≤ max C 1 := le_max_left _ _
      have h1 : ∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2 ≤ max C 1 * mainTerm T := by nlinarith
      calc ε * (∫ t in (0 : ℝ)..T, ‖zetaSqModel t‖ ^ 2)
          ≤ ε * (max C 1 * mainTerm T) := mul_le_mul_of_nonneg_left h1 hε.le
        _ = (c / 2) * mainTerm T := by dsimp [ε]; field_simp [hC1.ne']
    have hterm2 : (1 + ε⁻¹) * (∫ t in (0 : ℝ)..T,
        ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2) ≤
        (c / 2) * mainTerm T := by
      have h1p : 0 < 1 + ε⁻¹ := by positivity
      calc (1 + ε⁻¹) * (∫ t in (0 : ℝ)..T,
              ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ)) ^ 2 - zetaSqModel t‖ ^ 2)
          ≤ (1 + ε⁻¹) * (c / (2 * (1 + ε⁻¹)) * mainTerm T) :=
            mul_le_mul_of_nonneg_left herrT h1p.le
        _ = (c / 2) * mainTerm T := by field_simp [h1p.ne']
    linarith
  have hzeta_equiv : (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 4) ~[atTop] mainTerm := by
    rw [Asymptotics.IsEquivalent] at hM_equiv ⊢
    exact (hzeta_sub_M.add hM_equiv).congr_left fun T => by dsimp only [Pi.sub_apply]; ring
  have hfinal := hzeta_equiv.div (Asymptotics.IsEquivalent.refl (u := fun T : ℝ => T))
  refine (hfinal.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T _
    dsimp [RiemannZetaMoments.moment]
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    dsimp [mainTerm]
    field_simp [hT.ne']

end OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1
