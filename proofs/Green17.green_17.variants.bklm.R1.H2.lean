import OMAReductions.R_Green17_green_17_variants_bklm_R1
import Mathlib

/-!
# Upgrading L^2-Bounded Product Correlation to 1-Bounded Product Correlation

We prove `OMA.R_Green17_green_17_variants_bklm_R1.H2` (Theorem 10 of Bhangale, Khot, Liu, and
Minzer, arXiv:2411.15133) with explicit exponent `C₂ = 17` via a direct Gaussian-smoothed Mellin
representation:
1. Polar-decompose `P i a = U i a * ‖P i a‖` and consider the 1-bounded product functions
   `Q_t i a = U i a * exp (I * t * log ‖P i a‖)` (zero when `P i a = 0`).
2. Approximate `r ↦ r` on `(0, ∞)` by
   `Φ_D(log r) = (e^(-1/2) / √(2π)) * ∫ L in -D..D, e^L * e^(-(log r - L)^2 / 2)` with
   `D = 2 * log (64 / δ)`. For all `r > 0`, `0 ≤ r - Φ_D(log r) ≤ (δ / 64) * (1 + r^2)`,
   yielding `‖orig - LHS‖ ≤ δ / 32`.
3. Expanding `e^(-(u - L)^2 / 2)` via the exact complex Gaussian Fourier integral writes `LHS`
   as a double integral against `corr(f, Q_t)` whose norm is at most `δ^17 * e^D ≤ δ / 4` if
   every `Q_t` had correlation `< δ^17`, contradicting `‖LHS‖ ≥ 31/32 * δ`.
-/

namespace Green17H2

open MeasureTheory Filter Finset
open scoped Topology BigOperators

/- ### Part 1: Gaussian integral and tail bounds -/

private lemma integral_gauss_half :
    ∫ t : ℝ, Real.exp (-(t ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  have hfun : (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) := by
    ext x; congr 1; ring
  rw [hfun] at h
  rw [h]
  congr 1
  field_simp

private lemma integrable_gauss_half :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by
  have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  convert h using 1
  ext t; congr 1; ring

private lemma gaussian_fourier_half (w : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
        Complex.exp ((w : ℂ) * (t : ℂ) * Complex.I) =
      ((Real.sqrt (2 * Real.pi) * Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) := by
  have hb : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  have hmain := GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I hb (-w)
  have hstep : ∀ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
        Complex.exp ((w : ℂ) * (t : ℂ) * Complex.I) =
      ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) * ((t : ℂ) + ((-w : ℝ) : ℂ) * Complex.I) ^ 2) := by
    intro t
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp_rw [hstep]
  rw [integral_const_mul, hmain]
  have hpi : (Real.pi / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    have hdiv : (Real.pi : ℂ) / (1 / 2 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [hdiv, Real.sqrt_eq_rpow]
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    congr 1
    norm_num
  rw [hpi]
  push_cast
  ring

private lemma gaussian_tail_Ioi {A : ℝ} (hA : 1 ≤ A) :
    ∫ s in Set.Ioi A, Real.exp (-(s ^ 2 / 2)) ≤ Real.exp (-(A ^ 2 / 2)) := by
  have hderiv : ∀ x ∈ Set.Ioi A,
      HasDerivAt (fun s : ℝ => -Real.exp (-(s ^ 2 / 2))) (x * Real.exp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-x) x := by
      have h0 := ((hasDerivAt_pow 2 x).div_const 2).neg
      have hval : -((2 : ℕ) * x ^ (2 - 1) / 2) = -x := by norm_num
      exact hval ▸ h0
    have h2 : HasDerivAt (fun s : ℝ => -Real.exp (-(s ^ 2 / 2)))
        (-(Real.exp (-(x ^ 2 / 2)) * (-x))) x := h1.exp.neg
    have hval2 : -(Real.exp (-(x ^ 2 / 2)) * (-x)) = x * Real.exp (-(x ^ 2 / 2)) := by ring
    exact hval2 ▸ h2
  have htend : Tendsto (fun s : ℝ => -Real.exp (-(s ^ 2 / 2))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun s : ℝ => s ^ 2 / 2) atTop atTop := by
      have h1 : Tendsto (fun s : ℝ => s * s) atTop atTop :=
        tendsto_id.atTop_mul_atTop₀ tendsto_id
      have h2 : Tendsto (fun s : ℝ => s ^ 2) atTop atTop := by
        simpa [sq] using h1
      exact h2.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    have hexp : Tendsto (fun s : ℝ => Real.exp (-(s ^ 2 / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsq)
    simpa using hexp.neg
  have hcont : ContinuousOn (fun s : ℝ => -Real.exp (-(s ^ 2 / 2))) (Set.Ici A) := by
    fun_prop
  have hint_x : IntegrableOn (fun s : ℝ => s * Real.exp (-(s ^ 2 / 2))) (Set.Ioi A) volume := by
    have hdom : Integrable (fun s : ℝ => Real.exp (-(s ^ 2 / 4))) := by
      have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
      convert h using 1; ext s; congr 1; ring
    refine (hdom.integrableOn.const_mul 4).mono' ?_ ?_
    · exact (continuous_id.mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 ≤ s := le_trans (by linarith) (le_of_lt hs)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 (Real.exp_nonneg _))]
      have hsub : -(s ^ 2 / 2) = -(s ^ 2 / 4) + -(s ^ 2 / 4) := by ring
      rw [hsub, Real.exp_add]
      have hle : s * Real.exp (-(s ^ 2 / 4)) ≤ 4 := by
        have h1 : s ^ 2 / 4 + 1 ≤ Real.exp (s ^ 2 / 4) := by
          linarith [Real.add_one_le_exp (s ^ 2 / 4)]
        have h2 : s ≤ s ^ 2 / 4 + 1 := by nlinarith [sq_nonneg (s - 2)]
        have h3 : s ≤ 4 * Real.exp (s ^ 2 / 4) := by
          have : 0 ≤ Real.exp (s ^ 2 / 4) := Real.exp_nonneg _
          linarith
        calc s * Real.exp (-(s ^ 2 / 4))
            ≤ (4 * Real.exp (s ^ 2 / 4)) * Real.exp (-(s ^ 2 / 4)) := by
              gcongr
          _ = 4 := by rw [mul_assoc, ← Real.exp_add]; simp
      calc s * (Real.exp (-(s ^ 2 / 4)) * Real.exp (-(s ^ 2 / 4)))
          = (s * Real.exp (-(s ^ 2 / 4))) * Real.exp (-(s ^ 2 / 4)) := by ring
        _ ≤ 4 * Real.exp (-(s ^ 2 / 4)) := by gcongr
  have heval : ∫ s in Set.Ioi A, s * Real.exp (-(s ^ 2 / 2)) = Real.exp (-(A ^ 2 / 2)) := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (hcont.continuousWithinAt (Set.mem_Ici.mpr le_rfl))
      hderiv hint_x htend
    linarith
  rw [← heval]
  refine setIntegral_mono_on integrable_gauss_half.integrableOn hint_x measurableSet_Ioi ?_
  intro s hs
  have hs1 : 1 ≤ s := le_trans hA (le_of_lt hs)
  calc Real.exp (-(s ^ 2 / 2)) = 1 * Real.exp (-(s ^ 2 / 2)) := (one_mul _).symm
    _ ≤ s * Real.exp (-(s ^ 2 / 2)) := mul_le_mul_of_nonneg_right hs1 (Real.exp_nonneg _)

private lemma gaussian_tail_Iic {A : ℝ} (hA : 1 ≤ A) :
    ∫ s in Set.Iic (-A), Real.exp (-(s ^ 2 / 2)) ≤ Real.exp (-(A ^ 2 / 2)) := by
  have heq : ∫ s in Set.Iic (-A), Real.exp (-(s ^ 2 / 2)) =
      ∫ s in Set.Ioi A, Real.exp (-(s ^ 2 / 2)) := by
    have h := integral_comp_neg_Iic (f := fun s : ℝ => Real.exp (-(s ^ 2 / 2))) (-A)
    simpa using h
  rw [heq]
  exact gaussian_tail_Ioi hA

/- ### Part 2: Smooth approximation `Φ` of `r ↦ r` -/

private noncomputable def phi (D u : ℝ) : ℝ :=
  (Real.exp (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi)) *
    ∫ L in (-D)..D, Real.exp L * Real.exp (-((u - L) ^ 2 / 2))

private lemma phi_eq_shift (D u : ℝ) :
    phi D u = Real.exp u *
      ((∫ w in (-D - u - 1)..(D - u - 1), Real.exp (-(w ^ 2 / 2))) / Real.sqrt (2 * Real.pi)) := by
  unfold phi
  have h1 : ∀ L : ℝ, Real.exp (-(1 / 2 : ℝ)) * (Real.exp L * Real.exp (-((u - L) ^ 2 / 2))) =
      Real.exp u * Real.exp (-(((L - u - 1) ^ 2) / 2)) := by
    intro L
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have h2 : (Real.exp (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi)) *
      ∫ L in (-D)..D, Real.exp L * Real.exp (-((u - L) ^ 2 / 2)) =
      (∫ L in (-D)..D, Real.exp (-(1 / 2 : ℝ)) * (Real.exp L * Real.exp (-((u - L) ^ 2 / 2)))) /
        Real.sqrt (2 * Real.pi) := by
    rw [intervalIntegral.integral_const_mul]; ring
  rw [h2]
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, mul_div_assoc]
  congr 2
  have hsub := intervalIntegral.integral_comp_sub_right
    (fun w : ℝ => Real.exp (-(w ^ 2 / 2))) (u + 1) (a := -D) (b := D)
  have hfun : (fun L : ℝ => Real.exp (-((L - (u + 1)) ^ 2 / 2))) =
      (fun L : ℝ => Real.exp (-((L - u - 1) ^ 2 / 2))) := by
    ext L; congr 3; ring
  rw [hfun] at hsub
  rw [hsub]
  congr 1 <;> ring

private lemma phi_bounds {D : ℝ} (hD : 0 ≤ D) (u : ℝ) :
    0 ≤ phi D u ∧ phi D u ≤ Real.exp u := by
  rw [phi_eq_shift]
  have hle : -D - u - 1 ≤ D - u - 1 := by linarith
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hnonneg : 0 ≤ ∫ w in (-D - u - 1)..(D - u - 1), Real.exp (-(w ^ 2 / 2)) :=
    intervalIntegral.integral_nonneg hle (fun _ _ => Real.exp_nonneg _)
  have hle_full : ∫ w in (-D - u - 1)..(D - u - 1), Real.exp (-(w ^ 2 / 2)) ≤
      Real.sqrt (2 * Real.pi) := by
    rw [intervalIntegral.integral_of_le hle, ← integral_gauss_half]
    exact setIntegral_le_integral integrable_gauss_half (ae_of_all _ fun _ => Real.exp_nonneg _)
  constructor
  · exact mul_nonneg (Real.exp_nonneg _) (div_nonneg hnonneg hsqrt.le)
  · calc Real.exp u * ((∫ w in (-D - u - 1)..(D - u - 1), Real.exp (-(w ^ 2 / 2))) /
            Real.sqrt (2 * Real.pi))
        ≤ Real.exp u * (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi)) := by gcongr
      _ = Real.exp u := by rw [div_self hsqrt.ne', mul_one]

private lemma phi_approx_mid {D u : ℝ} (hD : 9 ≤ D) (hu : |u| ≤ D / 2) :
    Real.exp u - phi D u ≤ Real.exp (-(D / 2)) * Real.exp u := by
  rw [phi_eq_shift]
  set a := -D - u - 1
  set b := D - u - 1
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hA : 1 ≤ D / 2 - 1 := by linarith
  have ha_le : a ≤ -(D / 2 - 1) := by
    have := (abs_le.mp hu).1
    dsimp [a]; linarith
  have hb_ge : D / 2 - 1 ≤ b := by
    have := (abs_le.mp hu).2
    dsimp [b]; linarith
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_ge2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ^ 2 ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hsplit : ∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) =
      (∫ w in Set.Iic a, Real.exp (-(w ^ 2 / 2))) +
      (∫ w in Set.Ioc a b, Real.exp (-(w ^ 2 / 2))) +
      (∫ w in Set.Ioi b, Real.exp (-(w ^ 2 / 2))) := by
    have h1 := MeasureTheory.integral_add_compl (s := Set.Iic a) measurableSet_Iic integrable_gauss_half
    have hIoi : (Set.Iic a)ᶜ = Set.Ioi a := Set.compl_Iic
    rw [hIoi] at h1
    have h2 : Set.Ioi a = Set.Ioc a b ∪ Set.Ioi b := (Set.Ioc_union_Ioi_eq_Ioi hab).symm
    have hdisj : Disjoint (Set.Ioc a b) (Set.Ioi b) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2
    rw [h2, setIntegral_union hdisj measurableSet_Ioi
      integrable_gauss_half.integrableOn integrable_gauss_half.integrableOn] at h1
    linarith
  have hdiff : Real.sqrt (2 * Real.pi) - ∫ w in a..b, Real.exp (-(w ^ 2 / 2)) =
      (∫ w in Set.Iic a, Real.exp (-(w ^ 2 / 2))) +
      (∫ w in Set.Ioi b, Real.exp (-(w ^ 2 / 2))) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_gauss_half]
    linarith
  have hleft : ∫ w in Set.Iic a, Real.exp (-(w ^ 2 / 2)) ≤ Real.exp (-((D / 2 - 1) ^ 2 / 2)) := by
    calc ∫ w in Set.Iic a, Real.exp (-(w ^ 2 / 2))
        ≤ ∫ w in Set.Iic (-(D / 2 - 1)), Real.exp (-(w ^ 2 / 2)) :=
          setIntegral_mono_set integrable_gauss_half.integrableOn
            (ae_of_all _ fun _ => Real.exp_nonneg _)
            (Eventually.of_forall (Set.Iic_subset_Iic.mpr ha_le))
      _ ≤ Real.exp (-((D / 2 - 1) ^ 2 / 2)) := gaussian_tail_Iic hA
  have hright : ∫ w in Set.Ioi b, Real.exp (-(w ^ 2 / 2)) ≤ Real.exp (-((D / 2 - 1) ^ 2 / 2)) := by
    calc ∫ w in Set.Ioi b, Real.exp (-(w ^ 2 / 2))
        ≤ ∫ w in Set.Ioi (D / 2 - 1), Real.exp (-(w ^ 2 / 2)) :=
          setIntegral_mono_set integrable_gauss_half.integrableOn
            (ae_of_all _ fun _ => Real.exp_nonneg _)
            (Eventually.of_forall (Set.Ioi_subset_Ioi hb_ge))
      _ ≤ Real.exp (-((D / 2 - 1) ^ 2 / 2)) := gaussian_tail_Ioi hA
  have hexp_le : Real.exp (-((D / 2 - 1) ^ 2 / 2)) ≤ Real.exp (-(D / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfrac : (Real.sqrt (2 * Real.pi) - ∫ w in a..b, Real.exp (-(w ^ 2 / 2))) /
      Real.sqrt (2 * Real.pi) ≤ Real.exp (-(D / 2)) := by
    rw [hdiff]
    calc ((∫ w in Set.Iic a, Real.exp (-(w ^ 2 / 2))) +
            (∫ w in Set.Ioi b, Real.exp (-(w ^ 2 / 2)))) / Real.sqrt (2 * Real.pi)
        ≤ (2 * Real.exp (-(D / 2))) / Real.sqrt (2 * Real.pi) := by
          gcongr; linarith
      _ ≤ (2 * Real.exp (-(D / 2))) / 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hsqrt_ge2
      _ = Real.exp (-(D / 2)) := by ring
  have hrew : Real.exp u - Real.exp u * ((∫ w in a..b, Real.exp (-(w ^ 2 / 2))) /
      Real.sqrt (2 * Real.pi)) =
      ((Real.sqrt (2 * Real.pi) - ∫ w in a..b, Real.exp (-(w ^ 2 / 2))) /
        Real.sqrt (2 * Real.pi)) * Real.exp u := by
    field_simp [hsqrt_pos.ne']
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)

private lemma phi_approx_all {D r : ℝ} (hD : 9 ≤ D) (hr : 0 < r) :
    |r - phi D (Real.log r)| ≤ Real.exp (-(D / 2)) * (1 + r ^ 2) := by
  have hb := phi_bounds (D := D) (by linarith) (Real.log r)
  rw [Real.exp_log hr] at hb
  rw [abs_of_nonneg (sub_nonneg.mpr hb.2)]
  by_cases hlow : r ≤ Real.exp (-(D / 2))
  · calc r - phi D (Real.log r) ≤ r := by linarith [hb.1]
      _ ≤ Real.exp (-(D / 2)) := hlow
      _ ≤ Real.exp (-(D / 2)) * (1 + r ^ 2) := by nlinarith [Real.exp_nonneg (-(D / 2)), sq_nonneg r]
  · push Not at hlow
    by_cases hhigh : Real.exp (D / 2) ≤ r
    · have h1 : r ≤ Real.exp (-(D / 2)) * r ^ 2 := by
        have hmul : Real.exp (-(D / 2)) * Real.exp (D / 2) = 1 := by rw [← Real.exp_add]; simp
        calc r = (Real.exp (-(D / 2)) * Real.exp (D / 2)) * r := by rw [hmul, one_mul]
          _ = Real.exp (-(D / 2)) * (Real.exp (D / 2) * r) := by ring
          _ ≤ Real.exp (-(D / 2)) * (r * r) := by gcongr
          _ = Real.exp (-(D / 2)) * r ^ 2 := by ring
      calc r - phi D (Real.log r) ≤ r := by linarith [hb.1]
        _ ≤ Real.exp (-(D / 2)) * r ^ 2 := h1
        _ ≤ Real.exp (-(D / 2)) * (1 + r ^ 2) := by nlinarith [Real.exp_nonneg (-(D / 2))]
    · push Not at hhigh
      have hu : |Real.log r| ≤ D / 2 := by
        rw [abs_le]
        constructor
        · have := Real.log_le_log (Real.exp_pos _) hlow.le
          rwa [Real.log_exp] at this
        · have := Real.log_le_log hr hhigh.le
          rwa [Real.log_exp] at this
      have hmid := phi_approx_mid hD hu
      rw [Real.exp_log hr] at hmid
      have hrle : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
      calc r - phi D (Real.log r) ≤ Real.exp (-(D / 2)) * r := hmid
        _ ≤ Real.exp (-(D / 2)) * (1 + r ^ 2) :=
          mul_le_mul_of_nonneg_left hrle (Real.exp_nonneg _)

/- ### Part 3: Fourier expansion of `phi` -/

private lemma phi_fourier_eq (D u : ℝ) :
    ((phi D u : ℝ) : ℂ) =
      ((Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ L in (-D)..D, ((Real.exp L : ℝ) : ℂ) *
          ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
            Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
            Complex.exp ((u : ℂ) * (t : ℂ) * Complex.I) := by
  have hinner : ∀ L : ℝ,
      ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
        Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
        Complex.exp ((u : ℂ) * (t : ℂ) * Complex.I) =
      ((Real.sqrt (2 * Real.pi) * Real.exp (-((u - L) ^ 2 / 2)) : ℝ) : ℂ) := by
    intro L
    have hfun : (fun t : ℝ => ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
          Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
          Complex.exp ((u : ℂ) * (t : ℂ) * Complex.I)) =
        (fun t : ℝ => ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
          Complex.exp (((u - L : ℝ) : ℂ) * (t : ℂ) * Complex.I)) := by
      ext t
      rw [mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hfun]
    exact gaussian_fourier_half (u - L)
  simp_rw [hinner]
  have hcast : ∀ L : ℝ, ((Real.exp L : ℝ) : ℂ) *
      ((Real.sqrt (2 * Real.pi) * Real.exp (-((u - L) ^ 2 / 2)) : ℝ) : ℂ) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        ((Real.exp L * Real.exp (-((u - L) ^ 2 / 2)) : ℝ) : ℂ) := by
    intro L; push_cast; ring
  simp_rw [hcast]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  unfold phi
  push_cast
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt hpi.le
  have hsqC : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) := by exact_mod_cast hsq
  have hne : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpi).ne'
  rw [← hsqC]
  field_simp [hne]

/- ### Part 4: Main proof of `H2` -/

private lemma prod_norm_sq_avg {m : ℕ} (P : Fin m → ZMod 3 → ℂ)
    (hP : ∀ i, ∑ a : ZMod 3, ‖P i a‖ ^ 2 ≤ 3) :
    (∑ x : Fin m → ZMod 3, (∏ i : Fin m, ‖P i (x i)‖) ^ 2) / (3 : ℝ) ^ m ≤ 1 := by
  have hsum : (∑ x : Fin m → ZMod 3, (∏ i : Fin m, ‖P i (x i)‖) ^ 2) =
      ∏ i : Fin m, ∑ a : ZMod 3, ‖P i a‖ ^ 2 := by
    simp_rw [← Finset.prod_pow]
    exact (Fintype.prod_sum (fun i a => ‖P i a‖ ^ 2)).symm
  rw [hsum, div_le_one (by positivity)]
  calc ∏ i : Fin m, ∑ a : ZMod 3, ‖P i a‖ ^ 2
      ≤ ∏ _i : Fin m, (3 : ℝ) :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun i _ => hP i)
    _ = (3 : ℝ) ^ m := by simp

theorem h2_proof : OMA.R_Green17_green_17_variants_bklm_R1.H2 := by
  refine ⟨17, by norm_num, ?_⟩
  intro m f P δ hδ0 hδhalf hf hP hcorr
  -- Polar decomposition on each coordinate
  let Ucoord : Fin m → ZMod 3 → ℂ := fun i a =>
    if P i a = 0 then 0 else P i a / ((‖P i a‖ : ℝ) : ℂ)
  let Qt : ℝ → Fin m → ZMod 3 → ℂ := fun t i a =>
    if P i a = 0 then 0
    else (P i a / ((‖P i a‖ : ℝ) : ℂ)) * Complex.exp ((Real.log ‖P i a‖ : ℂ) * (t : ℂ) * Complex.I)
  have hQt_bdd : ∀ t i a, ‖Qt t i a‖ ≤ 1 := by
    intro t i a
    dsimp only [Qt]
    split_ifs with h0
    · simp
    · have hnpos : 0 < ‖P i a‖ := norm_pos_iff.mpr h0
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hnpos.le, div_self hnpos.ne',
        one_mul]
      have hre : ((Real.log ‖P i a‖ : ℂ) * (t : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre, Real.exp_zero]
  by_contra hno
  push Not at hno
  have hsmall : ∀ t : ℝ,
      ‖(∑ x : Fin m → ZMod 3, (f x : ℂ) * ∏ i : Fin m, Qt t i (x i)) / (3 : ℂ) ^ m‖ <
        δ ^ (17 : ℝ) := fun t => hno (Qt t) (hQt_bdd t)
  let R : (Fin m → ZMod 3) → ℝ := fun x => ∏ i : Fin m, ‖P i (x i)‖
  let U : (Fin m → ZMod 3) → ℂ := fun x => ∏ i : Fin m, Ucoord i (x i)
  have hR_nn : ∀ x, 0 ≤ R x := fun x => Finset.prod_nonneg fun i _ => norm_nonneg _
  have hU_bdd : ∀ x, ‖U x‖ ≤ 1 := by
    intro x
    dsimp only [U]
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
    dsimp only [Ucoord]
    split_ifs with h0
    · simp
    · have hnpos : 0 < ‖P i (x i)‖ := norm_pos_iff.mpr h0
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hnpos.le, div_self hnpos.ne']
  have hP_polar : ∀ x, (∏ i : Fin m, P i (x i)) = U x * ((R x : ℝ) : ℂ) := by
    intro x
    dsimp only [U, R, Ucoord]
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with h0
    · simp [h0]
    · have hne : ((‖P i (x i)‖ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (norm_pos_iff.mpr h0).ne'
      exact (div_mul_cancel₀ _ hne).symm
  have hQt_prod : ∀ t x, (∏ i : Fin m, Qt t i (x i)) =
      if R x = 0 then 0 else U x * Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I) := by
    intro t x
    by_cases hR0 : R x = 0
    · rw [if_pos hR0]
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hR0
      have hPi0 : P i (x i) = 0 := norm_eq_zero.mp hi
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [Qt, hPi0]
    · rw [if_neg hR0]
      have hne_all : ∀ i : Fin m, P i (x i) ≠ 0 := by
        intro i hi
        apply hR0
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      have hnorm_ne : ∀ i : Fin m, ‖P i (x i)‖ ≠ 0 := fun i => norm_ne_zero_iff.mpr (hne_all i)
      have hprod_eq : (∏ i : Fin m, Qt t i (x i)) =
          (∏ i : Fin m, Ucoord i (x i)) *
            ∏ i : Fin m, Complex.exp ((Real.log ‖P i (x i)‖ : ℂ) * (t : ℂ) * Complex.I) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [Qt, Ucoord, hne_all i]
      rw [hprod_eq, ← Complex.exp_sum]
      congr 2
      have hlog : Real.log (R x) = ∑ i : Fin m, Real.log ‖P i (x i)‖ := by
        dsimp only [R]
        exact Real.log_prod fun i _ => hnorm_ne i
      rw [hlog, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
  let D : ℝ := 2 * Real.log (64 / δ)
  have hD_ge9 : 9 ≤ D := by
    have h64 : (128 : ℝ) ≤ 64 / δ := by
      rw [le_div_iff₀ hδ0]; linarith
    have hlog128 : Real.log (128 : ℝ) ≤ Real.log (64 / δ) :=
      Real.log_le_log (by norm_num) h64
    have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      have : (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) := by norm_num
      rw [this, Real.log_pow]; norm_num
    have hlog2 := Real.log_two_gt_d9
    dsimp only [D]
    linarith
  have hexp_neg : Real.exp (-(D / 2)) = δ / 64 := by
    have h1 : -(D / 2) = -Real.log (64 / δ) := by dsimp [D]; ring
    rw [h1, Real.exp_neg, Real.exp_log (by positivity : 0 < 64 / δ)]
    field_simp
  have hexp_pos : Real.exp D = 4096 / δ ^ 2 := by
    have h1 : D = Real.log ((64 / δ) ^ 2) := by
      dsimp [D]; rw [Real.log_pow]; push_cast; ring
    rw [h1, Real.exp_log (by positivity)]
    ring
  let orig : ℂ := (∑ x : Fin m → ZMod 3, (f x : ℂ) * ∏ i : Fin m, P i (x i)) / (3 : ℂ) ^ m
  let lhs : ℂ :=
    (∑ x : Fin m → ZMod 3,
      (f x : ℂ) * (if R x = 0 then 0 else U x * ((phi D (Real.log (R x)) : ℝ) : ℂ))) / (3 : ℂ) ^ m
  let g : ℝ → ℂ := fun t =>
    (∑ x : Fin m → ZMod 3, (f x : ℂ) * ∏ i : Fin m, Qt t i (x i)) / (3 : ℂ) ^ m
  -- Step A: `‖orig - lhs‖ ≤ δ / 32`, hence `31 / 32 * δ ≤ ‖lhs‖`
  have hdiff_le : ‖orig - lhs‖ ≤ δ / 32 := by
    have hsub : orig - lhs =
        (∑ x : Fin m → ZMod 3,
          (f x : ℂ) * (if R x = 0 then 0 else U x * (((R x - phi D (Real.log (R x)) : ℝ) : ℂ)))) /
          (3 : ℂ) ^ m := by
      dsimp only [orig, lhs]
      rw [← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hP_polar x]
      by_cases hR0 : R x = 0
      · simp [hR0]
      · simp only [if_neg hR0, Complex.ofReal_sub]
        ring
    rw [hsub, norm_div, norm_pow, Complex.norm_ofNat]
    calc ‖∑ x : Fin m → ZMod 3,
            (f x : ℂ) * (if R x = 0 then 0 else U x * (((R x - phi D (Real.log (R x)) : ℝ) : ℂ)))‖ /
            (3 : ℝ) ^ m
        ≤ (∑ x : Fin m → ZMod 3,
            ‖(f x : ℂ) * (if R x = 0 then 0 else U x * (((R x - phi D (Real.log (R x)) : ℝ) : ℂ)))‖) /
            (3 : ℝ) ^ m := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (∑ x : Fin m → ZMod 3, (δ / 64) * (1 + (R x) ^ 2)) / (3 : ℝ) ^ m := by
          gcongr with x _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          by_cases hR0 : R x = 0
          · simp only [if_pos hR0, norm_zero, mul_zero]; positivity
          · simp only [if_neg hR0, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hRpos : 0 < R x := lt_of_le_of_ne (hR_nn x) (Ne.symm hR0)
            have happrox := phi_approx_all hD_ge9 hRpos
            rw [hexp_neg] at happrox
            calc |f x| * (‖U x‖ * |R x - phi D (Real.log (R x))|)
                ≤ 1 * (1 * ((δ / 64) * (1 + (R x) ^ 2))) := by
                  gcongr
                  · exact hf x
                  · exact hU_bdd x
              _ = (δ / 64) * (1 + (R x) ^ 2) := by ring
      _ = (δ / 64) * (1 + (∑ x : Fin m → ZMod 3, (R x) ^ 2) / (3 : ℝ) ^ m) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_pi, Finset.prod_const, Finset.card_univ, ZMod.card, Fintype.card_fin]
          simp only [nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
          field_simp
      _ ≤ (δ / 64) * (1 + 1) := by
          gcongr
          exact prod_norm_sq_avg P hP
      _ = δ / 32 := by ring
  have hlhs_ge : 31 / 32 * δ ≤ ‖lhs‖ := by
    have htri := norm_sub_le orig lhs
    have h1 : δ ≤ ‖orig‖ := hcorr
    have h2 : ‖orig‖ ≤ ‖lhs‖ + ‖orig - lhs‖ := by
      have := norm_add_le lhs (orig - lhs)
      simpa using this
    linarith
  -- Step B: Express `lhs` as the double integral of `g(t)`
  have hlhs_eq : lhs =
      ((Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ L in (-D)..D, ((Real.exp L : ℝ) : ℂ) *
          ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
            Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t := by
    have hg_eq : ∀ t : ℝ, g t =
        (∑ x : Fin m → ZMod 3,
          (f x : ℂ) * (if R x = 0 then 0 else
            U x * Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I))) / (3 : ℂ) ^ m := by
      intro t; dsimp only [g]; simp_rw [hQt_prod t]
    have hterm_int : ∀ (L : ℝ) (x : Fin m → ZMod 3),
        Integrable (fun t : ℝ =>
          ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
            Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
            ((f x : ℂ) * (if R x = 0 then 0 else
              U x * Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I)))) := by
      intro L x
      refine integrable_gauss_half.mono' ?_ ?_
      · by_cases hR0 : R x = 0
        · simp only [if_pos hR0, mul_zero]; exact aestronglyMeasurable_const
        · simp only [if_neg hR0]; fun_prop
      · refine ae_of_all _ fun t => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
        have hre1 : (-((L : ℂ) * (t : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
        rw [Complex.norm_exp, hre1, Real.exp_zero, mul_one]
        by_cases hR0 : R x = 0
        · simp only [if_pos hR0, mul_zero, norm_zero, mul_zero]; exact Real.exp_nonneg _
        · simp only [if_neg hR0, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hre2 : ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I).re = 0 := by
            simp [Complex.mul_re]
          rw [Complex.norm_exp, hre2, Real.exp_zero, mul_one]
          calc Real.exp (-(t ^ 2 / 2)) * (|f x| * ‖U x‖)
              ≤ Real.exp (-(t ^ 2 / 2)) * (1 * 1) := by
                gcongr
                · exact hf x
                · exact hU_bdd x
            _ = Real.exp (-(t ^ 2 / 2)) := by ring
    have hinner_swap : ∀ L : ℝ,
        ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
          Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t =
        (∑ x : Fin m → ZMod 3,
          (f x : ℂ) * (if R x = 0 then 0 else
            U x * ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
              Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
              Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I))) / (3 : ℂ) ^ m := by
      intro L
      simp_rw [hg_eq, mul_div_assoc', Finset.mul_sum]
      rw [integral_div, integral_finsetSum _ fun x _ => hterm_int L x]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hR0 : R x = 0
      · simp [hR0]
      · simp only [if_neg hR0]
        have hrew : (fun t : ℝ => ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
              Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
              ((f x : ℂ) * (U x * Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I)))) =
            (fun t : ℝ => ((f x : ℂ) * U x) *
              (((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
                Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
                Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I))) := by
          ext t; ring
        rw [hrew, integral_const_mul, mul_assoc]
    simp_rw [hinner_swap]
    have houter_int : ∀ x : Fin m → ZMod 3,
        IntervalIntegrable (fun L : ℝ => ((Real.exp L : ℝ) : ℂ) *
          ((f x : ℂ) * (if R x = 0 then 0 else
            U x * ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
              Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
              Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I)))) volume (-D) D := by
      intro x
      by_cases hR0 : R x = 0
      · simp [hR0]
      · simp only [if_neg hR0]
        have hcont_fn : (fun L : ℝ => ((Real.exp L : ℝ) : ℂ) *
              ((f x : ℂ) * (U x * ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
                Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
                Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I)))) =
            (fun L : ℝ => ((Real.exp L : ℝ) : ℂ) *
              ((f x : ℂ) * (U x *
                ((Real.sqrt (2 * Real.pi) * Real.exp (-((Real.log (R x) - L) ^ 2 / 2)) : ℝ) : ℂ)))) := by
          ext L
          congr 3
          have hfun : (fun t : ℝ => ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
                Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
                Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I)) =
              (fun t : ℝ => ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
                Complex.exp (((Real.log (R x) - L : ℝ) : ℂ) * (t : ℂ) * Complex.I)) := by
            ext t; rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
          rw [hfun]
          exact gaussian_fourier_half (Real.log (R x) - L)
        rw [hcont_fn]
        exact (by fun_prop : Continuous _).intervalIntegrable _ _
    simp_rw [mul_div_assoc', Finset.mul_sum]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_finsetSum fun x _ => houter_int x]
    rw [mul_div_assoc', Finset.mul_sum]
    dsimp only [lhs]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hR0 : R x = 0
    · simp [hR0]
    · simp only [if_neg hR0]
      rw [phi_fourier_eq D (Real.log (R x))]
      have hrew : (fun L : ℝ => ((Real.exp L : ℝ) : ℂ) *
            ((f x : ℂ) * (U x * ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
              Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
              Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I)))) =
          (fun L : ℝ => ((f x : ℂ) * U x) *
            (((Real.exp L : ℝ) : ℂ) * ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
              Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) *
              Complex.exp ((Real.log (R x) : ℂ) * (t : ℂ) * Complex.I))) := by
        ext L; ring
      rw [hrew, intervalIntegral.integral_const_mul]
      ring
  -- Step C: Upper bound `‖lhs‖ ≤ δ / 4` using `‖g t‖ < δ^17`
  have hinner_le : ∀ L : ℝ,
      ‖∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
          Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t‖ ≤
        Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ) := by
    intro L
    calc ‖∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
            Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t‖
        ≤ ∫ t : ℝ, ‖((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
            Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, Real.exp (-(t ^ 2 / 2)) * δ ^ (17 : ℝ) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            (integrable_gauss_half.mul_const _) (ae_of_all _ fun t => ?_)
          dsimp only
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
          have hre1 : (-((L : ℂ) * (t : ℂ) * Complex.I)).re = 0 := by simp [Complex.mul_re]
          rw [Complex.norm_exp, hre1, Real.exp_zero, mul_one]
          exact mul_le_mul_of_nonneg_left (hsmall t).le (Real.exp_nonneg _)
      _ = Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ) := by
          rw [integral_mul_const, integral_gauss_half]
  have houter_le :
      ‖∫ L in (-D)..D, ((Real.exp L : ℝ) : ℂ) *
          ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
            Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t‖ ≤
        Real.exp D * (Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ)) := by
    have hDle : -D ≤ D := by linarith
    have h1 := intervalIntegral.norm_integral_le_of_norm_le
      (a := -D) (b := D) hDle
      (f := fun L : ℝ => ((Real.exp L : ℝ) : ℂ) *
        ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
          Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t)
      (g := fun L : ℝ => Real.exp L * (Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ)))
      (ae_of_all _ fun L _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hinner_le L) (Real.exp_nonneg _))
      ((Real.continuous_exp.mul continuous_const).intervalIntegrable (μ := volume) (-D) D)
    calc _ ≤ ∫ L in (-D)..D, Real.exp L * (Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ)) := h1
      _ = (Real.exp D - Real.exp (-D)) * (Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ)) := by
          rw [intervalIntegral.integral_mul_const, integral_exp]
      _ ≤ Real.exp D * (Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ)) := by
          have hnn : 0 ≤ Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ) := by positivity
          nlinarith [Real.exp_nonneg (-D)]
  have hlhs_le : ‖lhs‖ ≤ δ / 4 := by
    rw [hlhs_eq, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi))]
    have hcoeff : Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) * Real.sqrt (2 * Real.pi) ≤ 1 := by
      have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
        Real.mul_self_sqrt (by positivity)
      have hge1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      have hexp1 : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have hpos : 0 < Real.sqrt (2 * Real.pi) := by linarith
      have hrew : Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) * Real.sqrt (2 * Real.pi) =
          Real.exp (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi) := by
        rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) hpos.ne']
        calc Real.exp (-(1 / 2 : ℝ)) * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)
            = Real.exp (-(1 / 2 : ℝ)) * (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) := by ring
          _ = Real.exp (-(1 / 2 : ℝ)) * (2 * Real.pi) := by rw [hsq]
      rw [hrew, div_le_one hpos]
      exact hexp1.trans hge1
    have hpow : 4096 / δ ^ 2 * δ ^ (17 : ℝ) ≤ δ / 4 := by
      have hnat : δ ^ (17 : ℝ) = δ ^ (17 : ℕ) := by exact_mod_cast Real.rpow_natCast δ 17
      rw [hnat]
      have h1 : 4096 / δ ^ 2 * δ ^ (17 : ℕ) = 4096 * δ ^ (14 : ℕ) * δ := by
        field_simp [hδ0.ne']
      rw [h1]
      have h14 : δ ^ (14 : ℕ) ≤ (1 / 2 : ℝ) ^ (14 : ℕ) :=
        pow_le_pow_left₀ hδ0.le hδhalf 14
      have hnum : 4096 * (1 / 2 : ℝ) ^ (14 : ℕ) = 1 / 4 := by norm_num
      nlinarith
    calc Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) *
            ‖∫ L in (-D)..D, ((Real.exp L : ℝ) : ℂ) *
              ∫ t : ℝ, ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) *
                Complex.exp (-((L : ℂ) * (t : ℂ) * Complex.I)) * g t‖
        ≤ Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) *
            (Real.exp D * (Real.sqrt (2 * Real.pi) * δ ^ (17 : ℝ))) :=
          mul_le_mul_of_nonneg_left houter_le (by positivity)
      _ = (Real.exp (-(1 / 2 : ℝ)) / (2 * Real.pi) * Real.sqrt (2 * Real.pi)) *
            (Real.exp D * δ ^ (17 : ℝ)) := by ring
      _ ≤ 1 * (Real.exp D * δ ^ (17 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = 4096 / δ ^ 2 * δ ^ (17 : ℝ) := by rw [one_mul, hexp_pos]
      _ ≤ δ / 4 := hpow
  linarith

end Green17H2

theorem OMA.solution : OMA.R_Green17_green_17_variants_bklm_R1.H2 :=
  Green17H2.h2_proof
