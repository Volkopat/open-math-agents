import OMAReductions.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2
import Mathlib

-- Step: HardyLittlewood.first_hardy_littlewood_conjecture.R2.H1
-- Credit: @hoodbroskillson
-- Proves Chebyshev PNT (k = 0 case of R2) via the self-contained OMAPNT kit.
section kitPNT
/-!
# Prime Number Theorem kit (namespace `OMAPNT`), self-contained, pinned Mathlib

Route: Newman's analytic theorem (Zagier's version) in Mellin form, with the contour replaced by
rectangles, so only Mathlib's Cauchy-Goursat for rectangles is needed.

* `RI_pole`: rectangle Cauchy formula `∮ H(z)/z dz = 2πi H(0)` for `[-a,c]×[-b,b]`, `0<a≤c`.
* `newman` / `newman_real`: if `a` is bounded measurable on `[1,∞)` and `∫_1^∞ a(x)x^{-z-1}dx`
  extends holomorphically to an open set containing `Re z ≥ 0`, then `∫_1^X a(x)/x dx` converges.
* `taub`: monotone `S` with convergent `∫_1^X (S(x)/x - c)/x dx` has `S(x)/x → c`.
* `tendsto_psiAP`: PNT in arithmetic progressions, `ψ(x;q,b)/x → 1/φ(q)` for `b` a unit
  (input: Mathlib's `LFunctionResidueClassAux` and non-vanishing of Dirichlet L-functions).
* `tendsto_psi_div`, `tendsto_theta_div`, `tendsto_primeCounting_div`,
  `primeCounting_isEquivalent`, `tendsto_primeCounting_nat`: the PNT.
-/

open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Interval

namespace OMAPNT

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

/-! ## Newman's analytic theorem, Mellin form -/

/-- Truncated Mellin transform `∫_1^X a(x) x^{-z-1} dx`. -/
noncomputable def GX (a : ℝ → ℝ) (X : ℝ) (z : ℂ) : ℂ :=
  ∫ x in (1 : ℝ)..X, (a x : ℂ) * (x : ℂ) ^ (-z - 1)

/-- Mellin transform `∫_1^∞ a(x) x^{-z-1} dx`. -/
noncomputable def Gint (a : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (a x : ℂ) * (x : ℂ) ^ (-z - 1)

section analytic

variable {a : ℝ → ℝ} {B : ℝ}

theorem norm_integrand_le (hbd : ∀ x, 1 ≤ x → |a x| ≤ B) (z : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖(a x : ℂ) * (x : ℂ) ^ (-z - 1)‖ ≤ B * x ^ (-z.re - 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [sub_re, neg_re, one_re]
  exact mul_le_mul_of_nonneg_right (hbd x hx) (Real.rpow_nonneg (by linarith) _)

theorem aesm_integrand (hmeas : Measurable a) (z : ℂ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun x : ℝ => (a x : ℂ) * (x : ℂ) ^ (-z - 1)) μ := by
  apply Measurable.aestronglyMeasurable
  exact (Complex.measurable_ofReal.comp hmeas).mul (Complex.measurable_ofReal.pow_const _)

theorem integrableOn_integrand (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 1 ≤ c) :
    IntegrableOn (fun x : ℝ => (a x : ℂ) * (x : ℂ) ^ (-z - 1)) (Ioi c) := by
  refine Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -z.re - 1 < -1) (by linarith)).const_mul B)
    (aesm_integrand hmeas z _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  exact norm_integrand_le hbd z (le_trans hc (le_of_lt hx))

theorem tail_eq (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {X : ℝ} (hX : 1 ≤ X) :
    Gint a z - GX a X z = ∫ x in Ioi X, (a x : ℂ) * (x : ℂ) ^ (-z - 1) := by
  unfold Gint GX
  rw [intervalIntegral.integral_of_le hX, ← Ioc_union_Ioi_eq_Ioi hX,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_integrand hmeas hbd hz le_rfl).mono_set Ioc_subset_Ioi_self)
      (integrableOn_integrand hmeas hbd hz hX)]
  ring

theorem tail_bound (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {X : ℝ} (hX : 1 ≤ X) :
    ‖Gint a z - GX a X z‖ ≤ B * (X ^ (-z.re) / z.re) := by
  rw [tail_eq hmeas hbd hz hX]
  have hint := (integrableOn_Ioi_rpow_of_lt (by linarith : -z.re - 1 < -1)
    (by linarith : (0 : ℝ) < X)).const_mul B
  calc _ ≤ ∫ x in Ioi X, B * x ^ (-z.re - 1) := by
        refine norm_integral_le_of_norm_le hint ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        exact norm_integrand_le hbd z (le_trans hX (le_of_lt hx))
    _ = B * (X ^ (-z.re) / z.re) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (by linarith)]
        congr 1
        rw [show -z.re - 1 + 1 = -z.re by ring, neg_div, div_neg, neg_neg]

theorem head_bound (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : z.re < 0) {X : ℝ} (hX : 1 ≤ X) :
    ‖GX a X z‖ ≤ B * (X ^ (-z.re) / (-z.re)) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 le_rfl)
  have h0 : (0 : ℝ) ∉ [[1, X]] := by
    rw [uIcc_of_le hX]; intro h; linarith [h.1]
  unfold GX
  calc _ ≤ ∫ x in (1 : ℝ)..X, B * x ^ (-z.re - 1) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hX
          (Eventually.of_forall fun x hx => norm_integrand_le hbd z (le_of_lt hx.1)) ?_
        exact (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul B
    _ = B * ((X ^ (-z.re) - 1) / (-z.re)) := by
        rw [intervalIntegral.integral_const_mul,
          integral_rpow (Or.inr ⟨by intro h; linarith, h0⟩)]
        congr 1
        rw [show -z.re - 1 + 1 = -z.re by ring, Real.one_rpow]
    _ ≤ B * (X ^ (-z.re) / (-z.re)) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith

theorem rpow_neg_mul_exp {X σ : ℝ} (hX : 0 < X) :
    X ^ (-σ) * Real.exp (σ * Real.log X) = 1 := by
  rw [Real.rpow_def_of_pos hX, ← Real.exp_add]
  simp only [mul_neg, Real.exp_eq_one_iff]
  ring

theorem tail_bound_exp (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {X : ℝ} (hX : 1 ≤ X) :
    ‖Gint a z - GX a X z‖ * Real.exp (z.re * Real.log X) ≤ B / z.re := by
  have h := mul_le_mul_of_nonneg_right (tail_bound hmeas hbd hz hX)
    (Real.exp_pos (z.re * Real.log X)).le
  calc _ ≤ _ := h
    _ = B / z.re * (X ^ (-z.re) * Real.exp (z.re * Real.log X)) := by ring
    _ = B / z.re := by rw [rpow_neg_mul_exp (by linarith), mul_one]

theorem head_bound_exp (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : z.re < 0) {X : ℝ} (hX : 1 ≤ X) :
    ‖GX a X z‖ * Real.exp (z.re * Real.log X) ≤ B / (-z.re) := by
  have h := mul_le_mul_of_nonneg_right (head_bound hbd hz hX)
    (Real.exp_pos (z.re * Real.log X)).le
  calc _ ≤ _ := h
    _ = B / (-z.re) * (X ^ (-z.re) * Real.exp (z.re * Real.log X)) := by ring
    _ = B / (-z.re) := by rw [rpow_neg_mul_exp (by linarith), mul_one]

theorem GX_differentiable (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {X : ℝ} (hX : 1 ≤ X) : Differentiable ℂ (GX a X) := by
  set f : ℝ → ℂ := (Ioc 1 X).indicator (fun t => (a t : ℂ)) with hf
  have hfe : ∀ z, GX a X z = mellin f (-z) := by
    intro z
    unfold GX mellin
    rw [intervalIntegral.integral_of_le hX]
    have : ∀ t : ℝ, (t : ℂ) ^ (-z - 1) • f t =
        (Ioc 1 X).indicator (fun t => (a t : ℂ) * (t : ℂ) ^ (-z - 1)) t := by
      intro t; by_cases ht : t ∈ Ioc 1 X <;> simp [f, ht, mul_comm]
    simp_rw [this]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hsub : Ioi (0 : ℝ) ∩ Ioc 1 X = Ioc 1 X := inter_eq_right.mpr
      (fun t (ht : t ∈ Ioc 1 X) => show t ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith [ht.1])
    rw [hsub]
  have hfeq : GX a X = fun z => mellin f (-z) := funext hfe
  rw [hfeq]
  intro z
  have hm : DifferentiableAt ℂ (mellin f) (-z) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -z.re + 1) (b := -z.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn (Integrable.locallyIntegrable ?_) _
      rw [hf, integrable_indicator_iff measurableSet_Ioc]
      refine Measure.integrableOn_of_bounded (M := B) (by simp [Real.volume_Ioc])
        (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
      simpa using hbd x (le_of_lt hx.1)
    · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop X] with t ht
      simp [f, ht.not_ge]
    · simp
    · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have : t ∉ Ioc 1 X := fun h => by linarith [h.1, ht.2]
      simp [f, this]
    · simp

  exact hm.comp z differentiableAt_id.neg

end analytic

/-! ## Kernel estimates -/

/-- Newman's kernel numerator `X^z (1 + z^2/R^2)` with `L = log X`. -/
noncomputable def KN (L R : ℝ) (z : ℂ) : ℂ := Complex.exp (z * L) * (1 + z ^ 2 / (R : ℂ) ^ 2)

theorem KN_zero (L R : ℝ) : KN L R 0 = 1 := by simp [KN]

theorem KN_differentiable (L R : ℝ) : Differentiable ℂ (KN L R) := by
  unfold KN; fun_prop

theorem norm_PK (P z : ℂ) (L R : ℝ) :
    ‖P * KN L R z / z‖ = ‖P‖ * Real.exp (z.re * L) * ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ / ‖z‖ := by
  unfold KN
  rw [norm_div, norm_mul, norm_mul, Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

theorem pt_gen {P z : ℂ} {L R c d e : ℝ} (hP : ‖P‖ * Real.exp (z.re * L) ≤ c)
    (hq : ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ d) (hz : e ≤ ‖z‖) (he : 0 < e) (hd : 0 ≤ d) :
    ‖P * KN L R z / z‖ ≤ c * d / e := by
  rw [norm_PK]
  have h1 : 0 ≤ ‖P‖ * Real.exp (z.re * L) := by positivity
  have hc : 0 ≤ c := le_trans h1 hP
  apply div_le_div₀ (mul_nonneg hc hd) (mul_le_mul hP hq (norm_nonneg _) hc) he hz

theorem q_top {z : ℂ} {R : ℝ} (hR : 0 < R) (hy : |z.im| = R) (hx : |z.re| ≤ R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 * |z.re| / R := by
  set x := z.re
  set y := z.im
  have hz : z = x + y * I := (re_add_im z).symm
  have hy2 : (y : ℂ) ^ 2 = (R : ℂ) ^ 2 := by
    have : y ^ 2 = R ^ 2 := by rw [← sq_abs y, hy]
    exact_mod_cast this
  have hR2 : (R : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hR 2).ne'
  have e : 1 + z ^ 2 / (R : ℂ) ^ 2 = ((x : ℂ) ^ 2 + 2 * x * y * I) / (R : ℂ) ^ 2 := by
    rw [eq_div_iff hR2, add_mul, div_mul_cancel₀ _ hR2, hz]
    linear_combination (-1 : ℂ) * hy2 + (y : ℂ) ^ 2 * I_sq
  rw [e, norm_div]
  have hn : ‖(x : ℂ) ^ 2 + 2 * x * y * I‖ ≤ |x| ^ 2 + 2 * |x| * |y| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp [Complex.norm_real]
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    div_le_div_iff₀ (by positivity) hR]
  have hx0 := abs_nonneg x
  rw [hy] at hn
  nlinarith [mul_le_mul_of_nonneg_left hx hx0]

theorem q_box {z : ℂ} {R : ℝ} (hR : 0 < R) (hx : |z.re| ≤ R) (hy : |z.im| ≤ R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ 5 := by
  have hzn : ‖z‖ ≤ 2 * R := by
    calc ‖z‖ = ‖(z.re : ℂ) + z.im * I‖ := by rw [re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp [Complex.norm_real]
      _ ≤ 2 * R := by linarith
  calc ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 / (R : ℂ) ^ 2‖ := norm_add_le _ _
    _ = 1 + ‖z‖ ^ 2 / R ^ 2 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
          norm_one]
    _ ≤ 1 + (2 * R) ^ 2 / R ^ 2 := by
        gcongr
    _ = 5 := by field_simp; ring

theorem abs_mul_exp_le {x L : ℝ} (hx : x ≤ 0) (hL : 0 < L) :
    |x| * Real.exp (x * L) ≤ 1 / L := by
  rw [abs_of_nonpos hx, le_div_iff₀ hL]
  have h1 := Real.add_one_le_exp (-(x * L))
  have h2 : Real.exp (-(x * L)) * Real.exp (x * L) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (x * L)
  nlinarith

/-! ## Newman's contour estimate -/

theorem ii_h {F : ℂ → ℂ} {S : Set ℂ} (hF : ContinuousOn F S) {c p q : ℝ}
    (h : ∀ x ∈ [[p, q]], (x : ℂ) + c * I ∈ S) :
    IntervalIntegrable (fun x : ℝ => F (x + c * I)) volume p q :=
  (hF.comp (Continuous.continuousOn (by fun_prop)) h).intervalIntegrable

theorem ii_v {F : ℂ → ℂ} {S : Set ℂ} (hF : ContinuousOn F S) {c p q : ℝ}
    (h : ∀ y ∈ [[p, q]], (c : ℂ) + y * I ∈ S) :
    IntervalIntegrable (fun y : ℝ => F (c + y * I)) volume p q :=
  (hF.comp (Continuous.continuousOn (by fun_prop)) h).intervalIntegrable

theorem memh {x c x0 x1 y0 y1 : ℝ} (hx : x ∈ [[x0, x1]]) (hc : c ∈ [[y0, y1]]) (hc0 : c ≠ 0) :
    (x : ℂ) + c * I ∈ [[x0, x1]] ×ℂ [[y0, y1]] \ {0} := by
  refine ⟨by simp [mem_reProdIm, hx, hc], fun h => ?_⟩
  have := congrArg Complex.im (mem_singleton_iff.mp h); simp at this; exact hc0 this

theorem memv {c y x0 x1 y0 y1 : ℝ} (hc : c ∈ [[x0, x1]]) (hy : y ∈ [[y0, y1]]) (hc0 : c ≠ 0) :
    (c : ℂ) + y * I ∈ [[x0, x1]] ×ℂ [[y0, y1]] \ {0} := by
  refine ⟨by simp [mem_reProdIm, hy, hc], fun h => ?_⟩
  have := congrArg Complex.re (mem_singleton_iff.mp h); simp at this; exact hc0 this

theorem uIcc_sub {x a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a) (hbd : b ≤ d)
    (hx : x ∈ [[a, b]]) : x ∈ [[c, d]] := by
  rw [uIcc_of_le hab] at hx; rw [uIcc_of_le hcd]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem nb {F : ℝ → ℂ} {C a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Ioc a b, ‖F x‖ ≤ C) :
    ‖∫ x in a..b, F x‖ ≤ C * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (f := F) (C := C)
    (fun x hx => h x (by rwa [uIoc_of_le hab] at hx))
  rwa [abs_of_nonneg (by linarith)] at this

theorem norm9 (a1 a2 a3 f1 f2 f3 h1 h2 h3 : ℂ) :
    ‖(a1 - a2 + I * a3) + (f1 - f2 - I * f3) - (h1 - h2 - I * h3)‖ ≤
      ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖f1‖ + ‖f2‖ + ‖f3‖ + ‖h1‖ + ‖h2‖ + ‖h3‖ := by
  have hI : ∀ w : ℂ, ‖I * w‖ = ‖w‖ := fun w => by rw [norm_mul, Complex.norm_I, one_mul]
  have e1 := norm_sub_le ((a1 - a2 + I * a3) + (f1 - f2 - I * f3)) (h1 - h2 - I * h3)
  have e2 := norm_add_le (a1 - a2 + I * a3) (f1 - f2 - I * f3)
  have e3 := norm_add_le (a1 - a2) (I * a3)
  have e4 := norm_sub_le a1 a2
  have e5 := norm_sub_le (f1 - f2) (I * f3)
  have e6 := norm_sub_le f1 f2
  have e7 := norm_sub_le (h1 - h2) (I * h3)
  have e8 := norm_sub_le h1 h2
  rw [hI] at e3 e5 e7
  linarith

section core

variable {a : ℝ → ℝ} {B : ℝ}

theorem newman_core (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hHP : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGeq : ∀ z : ℂ, 0 < z.re → G z = Gint a z)
    {R : ℝ} (hR : 0 < R) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 1 < X →
      2 * Real.pi * ‖G 0 - GX a X 0‖ ≤
        32 * B / R + C / Real.log X + C * Real.exp (-(δ * Real.log X)) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 le_rfl)
  have hK0 : IsCompact ([[0, R]] ×ℂ [[-R, R]]) := isCompact_uIcc.reProdIm isCompact_uIcc
  have hK0U : [[0, R]] ×ℂ [[-R, R]] ⊆ U := fun z hz => hHP z (by
    rw [mem_reProdIm, uIcc_of_le hR.le] at hz; exact hz.1.1)
  obtain ⟨δ0, hδ0, hthick⟩ := hK0.exists_cthickening_subset_open hU hK0U
  set δ := min δ0 R with hδdef
  have hδ : 0 < δ := lt_min hδ0 hR
  have hδR : δ ≤ R := min_le_right _ _
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hDU : [[-δ, R]] ×ℂ [[-R, R]] ⊆ U := by
    intro z hz
    rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hz
    by_cases h0 : 0 ≤ z.re
    · exact hK0U (by
        rw [mem_reProdIm, uIcc_of_le hR.le, uIcc_of_le (by linarith)]
        exact ⟨⟨h0, hz.1.2⟩, hz.2⟩)
    · apply hthick
      refine Metric.mem_cthickening_of_dist_le z ((z.im : ℂ) * I) δ0 _ ?_ ?_
      · rw [mem_reProdIm, uIcc_of_le hR.le, uIcc_of_le (by linarith)]
        simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          mul_im, add_zero]
        exact ⟨⟨le_rfl, hR.le⟩, hz.2⟩
      · rw [Complex.dist_eq]
        have : z - (z.im : ℂ) * I = (z.re : ℂ) := by
          apply Complex.ext <;> simp
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith [hz.1.1]
  have hDc : IsCompact ([[-δ, R]] ×ℂ [[-R, R]]) := isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨M0, hM0⟩ := hDc.exists_bound_of_continuousOn (hG.continuousOn.mono hDU)
  set M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hGM : ∀ z ∈ [[-δ, R]] ×ℂ [[-R, R]], ‖G z‖ ≤ M :=
    fun z hz => (hM0 z hz).trans (le_max_left _ _)
  refine ⟨6 * M * δ / R ^ 2 + 10 * M * R / δ, δ, hδ, fun X hX => ?_⟩
  set L := Real.log X with hLdef
  have hL : 0 < L := Real.log_pos hX
  have hX1 : 1 ≤ X := hX.le
  set f : ℂ → ℂ := fun z => G z * KN L R z / z with hfdef
  set g : ℂ → ℂ := fun z => GX a X z * KN L R z / z with hgdef
  have hP1 : RI f (-δ) R (-R) R = 2 * Real.pi * I * G 0 := by
    have := RI_pole (H := fun z => G z * KN L R z) hδ hR hδR hU hDU
      (hG.mul (KN_differentiable L R).differentiableOn)
    rw [KN_zero, mul_one] at this
    exact this
  have hP2 : RI g (-R) R (-R) R = 2 * Real.pi * I * GX a X 0 := by
    have := RI_pole (H := fun z => GX a X z * KN L R z) hR hR le_rfl isOpen_univ (subset_univ _)
      ((GX_differentiable hmeas hbd hX1).mul (KN_differentiable L R)).differentiableOn
    rw [KN_zero, mul_one] at this
    exact this
  have hfc : ContinuousOn f ([[-δ, R]] ×ℂ [[-R, R]] \ {0}) := by
    apply ContinuousOn.div ((hG.continuousOn.mono (sdiff_subset.trans hDU)).mul
      (KN_differentiable L R).continuous.continuousOn) continuousOn_id
    intro z hz; exact hz.2
  have hgc : ContinuousOn g ([[-R, R]] ×ℂ [[-R, R]] \ {0}) := by
    apply ContinuousOn.div ((GX_differentiable hmeas hbd hX1).continuous.continuousOn.mul
      (KN_differentiable L R).continuous.continuousOn) continuousOn_id
    intro z hz; exact hz.2
  have hR0 : R ≠ 0 := hR.ne'
  have hmR0 : (-R) ≠ 0 := by linarith
  have hmRm : (-R) ∈ [[-R, R]] := left_mem_uIcc
  have hRm : R ∈ [[-R, R]] := right_mem_uIcc
  have hRmD : R ∈ [[-δ, R]] := right_mem_uIcc
  have hRδ : -R ≤ -δ := by linarith
  -- integrability
  have fb1 : IntervalIntegrable (fun x : ℝ => f (x + ((-R : ℝ) : ℂ) * I)) volume (-δ) 0 :=
    ii_h hfc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hmRm hmR0)
  have fb2 : IntervalIntegrable (fun x : ℝ => f (x + ((-R : ℝ) : ℂ) * I)) volume 0 R :=
    ii_h hfc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hmRm hmR0)
  have ft1 : IntervalIntegrable (fun x : ℝ => f (x + (R : ℂ) * I)) volume (-δ) 0 :=
    ii_h hfc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hRm hR0)
  have ft2 : IntervalIntegrable (fun x : ℝ => f (x + (R : ℂ) * I)) volume 0 R :=
    ii_h hfc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hRm hR0)
  have gb1 : IntervalIntegrable (fun x : ℝ => g (x + ((-R : ℝ) : ℂ) * I)) volume (-R) 0 :=
    ii_h hgc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hmRm hmR0)
  have gb2 : IntervalIntegrable (fun x : ℝ => g (x + ((-R : ℝ) : ℂ) * I)) volume 0 R :=
    ii_h hgc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hmRm hmR0)
  have gt1 : IntervalIntegrable (fun x : ℝ => g (x + (R : ℂ) * I)) volume (-R) 0 :=
    ii_h hgc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hRm hR0)
  have gt2 : IntervalIntegrable (fun x : ℝ => g (x + (R : ℂ) * I)) volume 0 R :=
    ii_h hgc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hRm hR0)
  have fr : IntervalIntegrable (fun y : ℝ => f ((R : ℂ) + y * I)) volume (-R) R :=
    ii_v hfc (fun y hy => memv hRmD hy hR0)
  have gr : IntervalIntegrable (fun y : ℝ => g ((R : ℂ) + y * I)) volume (-R) R :=
    ii_v hgc (fun y hy => memv hRm hy hR0)
  -- decomposition
  unfold RI at hP1 hP2
  rw [← intervalIntegral.integral_add_adjacent_intervals fb1 fb2,
    ← intervalIntegral.integral_add_adjacent_intervals ft1 ft2] at hP1
  rw [← intervalIntegral.integral_add_adjacent_intervals gb1 gb2,
    ← intervalIntegral.integral_add_adjacent_intervals gt1 gt2] at hP2
  have hA1 := intervalIntegral.integral_sub fb2 gb2
  have hA2 := intervalIntegral.integral_sub ft2 gt2
  have hA3 := intervalIntegral.integral_sub fr gr
  have key : 2 * Real.pi * I * (G 0 - GX a X 0) =
      ((∫ x in (0 : ℝ)..R, (f (x + ((-R : ℝ) : ℂ) * I) - g (x + ((-R : ℝ) : ℂ) * I))) -
        (∫ x in (0 : ℝ)..R, (f (x + (R : ℂ) * I) - g (x + (R : ℂ) * I))) +
        I * (∫ y in (-R)..R, (f ((R : ℂ) + y * I) - g ((R : ℂ) + y * I)))) +
      ((∫ x in (-δ)..0, f (x + ((-R : ℝ) : ℂ) * I)) - (∫ x in (-δ)..0, f (x + (R : ℂ) * I)) -
        I * (∫ y in (-R)..R, f (((-δ : ℝ) : ℂ) + y * I))) -
      ((∫ x in (-R)..0, g (x + ((-R : ℝ) : ℂ) * I)) - (∫ x in (-R)..0, g (x + (R : ℂ) * I)) -
        I * (∫ y in (-R)..R, g (((-R : ℝ) : ℂ) + y * I))) := by
    rw [mul_sub, ← hP1, ← hP2, hA1, hA2, hA3]
    ring
  -- pointwise bounds
  have hRpos2 : 0 < R ^ 2 := by positivity
  have pA : ∀ z : ℂ, 0 < z.re → z.re ≤ R → |z.im| = R → ‖f z - g z‖ ≤ 3 * B / R ^ 2 := by
    intro z h1 h2 h3
    have e : f z - g z = (Gint a z - GX a X z) * KN L R z / z := by
      simp only [hfdef, hgdef, hGeq z h1]; ring
    rw [e]
    have := pt_gen (L := L) (R := R) (P := Gint a z - GX a X z) (z := z)
      (tail_bound_exp hmeas hbd h1 hX1) (q_top hR h3 (by rw [abs_of_pos h1]; exact h2))
      (by rw [← h3]; exact abs_im_le_norm z) hR (by positivity)
    calc _ ≤ _ := this
      _ = 3 * B / R ^ 2 := by rw [abs_of_pos h1]; have := h1.ne'; field_simp
  have pAv : ∀ z : ℂ, z.re = R → |z.im| ≤ R → ‖f z - g z‖ ≤ 5 * B / R ^ 2 := by
    intro z h1 h3
    have h1' : 0 < z.re := h1 ▸ hR
    have e : f z - g z = (Gint a z - GX a X z) * KN L R z / z := by
      simp only [hfdef, hgdef, hGeq z h1']; ring
    rw [e]
    have := pt_gen (L := L) (R := R) (P := Gint a z - GX a X z) (z := z)
      (tail_bound_exp hmeas hbd h1' hX1) (q_box hR (by rw [h1, abs_of_pos hR]) h3)
      (by have := abs_re_le_norm z; rw [h1, abs_of_pos hR] at this; exact this) hR (by norm_num)
    calc _ ≤ _ := this
      _ = 5 * B / R ^ 2 := by rw [h1]; field_simp
  have pH : ∀ z : ℂ, -R ≤ z.re → z.re ≤ 0 → |z.im| = R → ‖g z‖ ≤ 3 * B / R ^ 2 := by
    intro z h1 h2 h3
    have hzR : |z.re| ≤ R := abs_le.mpr ⟨h1, by linarith⟩
    have hzn : R ≤ ‖z‖ := by rw [← h3]; exact abs_im_le_norm z
    rcases lt_or_eq_of_le h2 with h2 | h2
    · have := pt_gen (L := L) (R := R) (P := GX a X z) (z := z)
        (head_bound_exp hbd h2 hX1) (q_top hR h3 hzR) hzn hR (by positivity)
      calc _ ≤ _ := this
        _ = 3 * B / R ^ 2 := by
          rw [abs_of_neg h2]; have : z.re ≠ 0 := by linarith
          field_simp
    · have := pt_gen (L := L) (R := R) (P := GX a X z) (z := z) le_rfl (q_top hR h3 hzR) hzn hR
        (by positivity)
      rw [h2] at this
      simp only [abs_zero, mul_zero, zero_div] at this
      exact this.trans (by positivity)
  have pHv : ∀ z : ℂ, z.re = -R → |z.im| ≤ R → ‖g z‖ ≤ 5 * B / R ^ 2 := by
    intro z h1 h3
    have h1' : z.re < 0 := by linarith
    have := pt_gen (L := L) (R := R) (P := GX a X z) (z := z)
      (head_bound_exp hbd h1' hX1) (q_box hR (by rw [h1, abs_neg, abs_of_pos hR]) h3)
      (by have := abs_re_le_norm z; rw [h1, abs_neg, abs_of_pos hR] at this; exact this) hR
      (by norm_num)
    calc _ ≤ _ := this
      _ = 5 * B / R ^ 2 := by rw [h1, neg_neg]; field_simp
  have pF : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| = R → ‖f z‖ ≤ 3 * M / (R ^ 2 * L) := by
    intro z h1 h2 h3
    have hzR : |z.re| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
    have hzD : z ∈ [[-δ, R]] ×ℂ [[-R, R]] := by
      rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact ⟨⟨h1, by linarith⟩, abs_le.mp h3.le⟩
    have hP : ‖G z‖ * Real.exp (z.re * L) ≤ M * Real.exp (z.re * L) :=
      mul_le_mul_of_nonneg_right (hGM z hzD) (Real.exp_pos _).le
    have := pt_gen (L := L) (R := R) (P := G z) (z := z) hP (q_top hR h3 hzR)
      (by rw [← h3]; exact abs_im_le_norm z) hR (by positivity)
    have hk := abs_mul_exp_le h2 hL
    calc ‖f z‖ = ‖G z * KN L R z / z‖ := rfl
      _ ≤ _ := this
      _ = 3 * M / R ^ 2 * (|z.re| * Real.exp (z.re * L)) := by field_simp
      _ ≤ 3 * M / R ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 3 * M / (R ^ 2 * L) := by field_simp
  have pFv : ∀ z : ℂ, z.re = -δ → |z.im| ≤ R → ‖f z‖ ≤ 5 * M * Real.exp (-(δ * L)) / δ := by
    intro z h1 h3
    have hzD : z ∈ [[-δ, R]] ×ℂ [[-R, R]] := by
      rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact ⟨⟨by linarith, by linarith⟩, abs_le.mp h3⟩
    have hP : ‖G z‖ * Real.exp (z.re * L) ≤ M * Real.exp (-(δ * L)) := by
      rw [h1, neg_mul]
      exact mul_le_mul_of_nonneg_right (hGM z hzD) (Real.exp_pos _).le
    have := pt_gen (L := L) (R := R) (P := G z) (z := z) hP
      (q_box hR (by rw [h1, abs_neg, abs_of_pos hδ]; exact hδR) h3)
      (by have := abs_re_le_norm z; rw [h1, abs_neg, abs_of_pos hδ] at this; exact this) hδ
      (by norm_num)
    calc ‖f z‖ = ‖G z * KN L R z / z‖ := rfl
      _ ≤ _ := this
      _ = 5 * M * Real.exp (-(δ * L)) / δ := by ring
  -- integral bounds
  have habsR : |(-R)| = R := by rw [abs_neg, abs_of_pos hR]
  have n1 : ‖∫ x in (0 : ℝ)..R, (f (x + ((-R : ℝ) : ℂ) * I) - g (x + ((-R : ℝ) : ℂ) * I))‖ ≤
      3 * B / R ^ 2 * (R - 0) :=
    nb hR.le (fun x hx => pA _ (by simpa using hx.1) (by simpa using hx.2) (by simpa using habsR))
  have n2 : ‖∫ x in (0 : ℝ)..R, (f (x + (R : ℂ) * I) - g (x + (R : ℂ) * I))‖ ≤
      3 * B / R ^ 2 * (R - 0) :=
    nb hR.le (fun x hx => pA _ (by simpa using hx.1) (by simpa using hx.2)
      (by simp [abs_of_pos hR]))
  have n3 : ‖∫ y in (-R)..R, (f ((R : ℂ) + y * I) - g ((R : ℂ) + y * I))‖ ≤
      5 * B / R ^ 2 * (R - -R) :=
    nb (by linarith) (fun y hy => pAv _ (by simp) (by simpa using abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have n4 : ‖∫ x in (-δ)..0, f (x + ((-R : ℝ) : ℂ) * I)‖ ≤ 3 * M / (R ^ 2 * L) * (0 - -δ) :=
    nb (by linarith) (fun x hx => pF _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simpa using habsR))
  have n5 : ‖∫ x in (-δ)..0, f (x + (R : ℂ) * I)‖ ≤ 3 * M / (R ^ 2 * L) * (0 - -δ) :=
    nb (by linarith) (fun x hx => pF _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simp [abs_of_pos hR]))
  have n6 : ‖∫ y in (-R)..R, f (((-δ : ℝ) : ℂ) + y * I)‖ ≤
      5 * M * Real.exp (-(δ * L)) / δ * (R - -R) :=
    nb (by linarith) (fun y hy => pFv _ (by simp) (by simpa using abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have n7 : ‖∫ x in (-R)..0, g (x + ((-R : ℝ) : ℂ) * I)‖ ≤ 3 * B / R ^ 2 * (0 - -R) :=
    nb (by linarith) (fun x hx => pH _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simpa using habsR))
  have n8 : ‖∫ x in (-R)..0, g (x + (R : ℂ) * I)‖ ≤ 3 * B / R ^ 2 * (0 - -R) :=
    nb (by linarith) (fun x hx => pH _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simp [abs_of_pos hR]))
  have n9 : ‖∫ y in (-R)..R, g (((-R : ℝ) : ℂ) + y * I)‖ ≤ 5 * B / R ^ 2 * (R - -R) :=
    nb (by linarith) (fun y hy => pHv _ (by simp) (by simpa using abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have hnorm : ‖2 * Real.pi * I * (G 0 - GX a X 0)‖ = 2 * Real.pi * ‖G 0 - GX a X 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  rw [← hnorm, key]
  refine (norm9 _ _ _ _ _ _ _ _ _).trans ?_
  set e := Real.exp (-(δ * L)) with hedef
  have he : 0 ≤ e := (Real.exp_pos _).le
  have c1 : 3 * B / R ^ 2 * (R - 0) = 3 * B / R := by field_simp; ring
  have c3 : 5 * B / R ^ 2 * (R - -R) = 10 * B / R := by field_simp; ring
  have c7 : 3 * B / R ^ 2 * (0 - -R) = 3 * B / R := by field_simp; ring
  have c4 : 3 * M / (R ^ 2 * L) * (0 - -δ) = 3 * M * δ / R ^ 2 / L := by field_simp; ring
  have c6 : 5 * M * e / δ * (R - -R) = 10 * M * R / δ * e := by field_simp; ring
  have hCL : (6 * M * δ / R ^ 2 + 10 * M * R / δ) / L =
      6 * M * δ / R ^ 2 / L + 10 * M * R / δ / L := add_div _ _ _
  have hCe : (6 * M * δ / R ^ 2 + 10 * M * R / δ) * e =
      6 * M * δ / R ^ 2 * e + 10 * M * R / δ * e := add_mul _ _ _
  have p1 : 0 ≤ 10 * M * R / δ / L := by positivity
  have p2 : 0 ≤ 6 * M * δ / R ^ 2 * e := by positivity
  have c32 : 32 * B / R = 3 * B / R + 3 * B / R + 10 * B / R + 3 * B / R + 3 * B / R +
      10 * B / R := by ring
  have c44 : 6 * M * δ / R ^ 2 / L = 3 * M * δ / R ^ 2 / L + 3 * M * δ / R ^ 2 / L := by ring
  linarith

end core

section newmanthm

variable {a : ℝ → ℝ} {B : ℝ}

/-- **Newman's analytic theorem** (Mellin form): if `a` is bounded and measurable on `[1,∞)` and
its Mellin transform `∫_1^∞ a(x) x^{-z-1} dx` extends holomorphically to an open set containing
`Re z ≥ 0`, then `∫_1^X a(x)/x dx` converges to the value at `0`. -/
theorem newman (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hHP : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGeq : ∀ z : ℂ, 0 < z.re → G z = Gint a z) :
    Tendsto (fun X => GX a X 0) atTop (𝓝 (G 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 le_rfl)
  have hpe : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
  set R := 32 * (B + 1) / (Real.pi * ε) with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨C, δ, hδ, hb⟩ := newman_core hmeas hbd hU hHP hG hGeq hR
  have hT : Tendsto (fun X => C / Real.log X + C * Real.exp (-(δ * Real.log X))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X => C / Real.log X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 : Tendsto (fun X => Real.exp (-(δ * Real.log X))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_log_atTop.const_mul_atTop hδ)
    simpa using h1.add (h2.const_mul C)
  have hev := (hT.eventually (gt_mem_nhds hpe)).and (eventually_gt_atTop (1 : ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun X hX => ?_⟩
  obtain ⟨hE, hX1⟩ := hN X hX
  have h32 : 32 * B / R < Real.pi * ε := by
    rw [hRdef, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have := hb X hX1
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [Real.pi_pos]

/-- Real form of Newman's theorem. -/
theorem newman_real (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hHP : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGeq : ∀ z : ℂ, 0 < z.re → G z = Gint a z) :
    Tendsto (fun X => ∫ x in (1 : ℝ)..X, a x / x) atTop (𝓝 (G 0).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (newman hmeas hbd hU hHP hG hGeq)
  refine h.congr (fun X => ?_)
  simp only [Function.comp, GX]
  have : ∀ x : ℝ, (a x : ℂ) * (x : ℂ) ^ (-(0 : ℂ) - 1) = ((a x / x : ℝ) : ℂ) := by
    intro x
    rw [neg_zero, zero_sub, cpow_neg_one]
    push_cast
    ring
  simp_rw [this, intervalIntegral.integral_ofReal, ofReal_re]

end newmanthm

/-! ## Tauberian step: convergence of `∫ (S(x)/x - c)/x` forces `S(x)/x → c` -/

section tauberian

theorem taub {S : ℝ → ℝ} {c l : ℝ} (hc : 0 < c) (hmono : Monotone S)
    (hI : Tendsto (fun X => ∫ x in (1 : ℝ)..X, (S x / x - c) / x) atTop (𝓝 l)) :
    Tendsto (fun x => S x / x) atTop (𝓝 c) := by
  set F : ℝ → ℝ := fun x => (S x / x - c) / x with hF
  set I : ℝ → ℝ := fun X => ∫ x in (1 : ℝ)..X, F x with hIdef
  have hii : ∀ p q : ℝ, 0 < p → 0 < q → IntervalIntegrable F volume p q := by
    intro p q hp hq
    have h0 : ∀ x ∈ [[p, q]], x ≠ 0 := by
      intro x hx
      rcases le_total p q with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.1]
      · rw [uIcc_of_ge h] at hx; linarith [hx.1]
    have h1 : IntervalIntegrable (fun x => S x * (x⁻¹ * x⁻¹)) volume p q :=
      (hmono.intervalIntegrable).mul_continuousOn
        ((continuousOn_inv₀.mono (fun x hx => h0 x hx)).mul
          (continuousOn_inv₀.mono (fun x hx => h0 x hx)))
    have h2 : IntervalIntegrable (fun x : ℝ => c * x⁻¹) volume p q :=
      (ContinuousOn.intervalIntegrable
        (continuousOn_const.mul (continuousOn_inv₀.mono (fun x hx => h0 x hx))))
    refine (h1.sub h2).congr ?_
    intro x _
    simp only [hF]
    ring
  have hdiff : ∀ p q : ℝ, 1 ≤ p → 1 ≤ q → I q - I p = ∫ x in p..q, F x := by
    intro p q hp hq
    exact intervalIntegral.integral_interval_sub_left (hii 1 q one_pos (by linarith))
      (hii 1 p one_pos (by linarith))
  have hC : ∀ μ : ℝ, 0 < μ → Tendsto (fun x => I (μ * x) - I x) atTop (𝓝 0) := by
    intro μ hμ
    have := (hI.comp (tendsto_id.const_mul_atTop hμ)).sub hI
    simpa using this
  -- upper bound
  have up : ∀ ε > 0, ∀ᶠ x in atTop, S x / x ≤ c + ε := by
    intro ε hε
    by_contra h
    rw [not_eventually] at h
    set μ := 1 + ε / (2 * c) with hμ
    have hμ1 : 1 < μ := by have : 0 < ε / (2 * c) := by positivity
                           linarith
    have hμ0 : 0 < μ := by linarith
    set d := (c + ε) / μ - c with hd
    have hdpos : 0 < d := by
      rw [hd, sub_pos, lt_div_iff₀ hμ0, hμ]
      field_simp
      nlinarith
    set κ := d * (μ - 1) / μ with hκ
    have hκpos : 0 < κ := by positivity
    obtain ⟨x, hxS, hxC, hx1⟩ :=
      (h.and_eventually (((hC μ hμ0).eventually (eventually_lt_nhds hκpos)).and
        (eventually_ge_atTop 1))).exists
    have hx0 : 0 < x := by linarith
    have hxS' : (c + ε) * x < S x := by
      rw [not_le, lt_div_iff₀ hx0] at hxS; exact hxS
    have hxle : x ≤ μ * x := by nlinarith
    have hge : κ ≤ ∫ t in x..μ * x, F t := by
      have hm := intervalIntegral.integral_mono_on hxle
        (intervalIntegrable_const (c := d / (μ * x))) (hii x (μ * x) hx0 (by positivity)) ?_
      · rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        refine le_trans (le_of_eq ?_) hm
        rw [hκ]; field_simp
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hSt : (c + ε) * x < S t := lt_of_lt_of_le hxS' (hmono ht.1)
        have h2 : d ≤ S t / t - c := by
          rw [hd, sub_le_sub_iff_right, div_le_div_iff₀ hμ0 ht0]
          have : (c + ε) * t ≤ (c + ε) * (μ * x) := by
            apply mul_le_mul_of_nonneg_left ht.2; linarith
          nlinarith
        have h3 : d / (μ * x) ≤ d / t := div_le_div_of_nonneg_left hdpos.le ht0 ht.2
        have h4 : d / t ≤ (S t / t - c) / t := div_le_div_of_nonneg_right h2 ht0.le
        simp only [hF]
        linarith
    have := hdiff x (μ * x) hx1 (by nlinarith)
    simp only [hIdef] at hxC this
    linarith
  -- lower bound
  have lo : ∀ ε > 0, ε < c → ∀ᶠ x in atTop, c - ε ≤ S x / x := by
    intro ε hε hεc
    by_contra h
    rw [not_eventually] at h
    set μ := 1 + ε / (2 * c) with hμ
    have hμ1 : 1 < μ := by have : 0 < ε / (2 * c) := by positivity
                           linarith
    have hμ0 : 0 < μ := by linarith
    set d := c - (c - ε) * μ with hd
    have hdpos : 0 < d := by
      rw [hd, hμ]
      have : (c - ε) * (1 + ε / (2 * c)) = c - ε / 2 - ε ^ 2 / (2 * c) := by field_simp; ring
      rw [this]
      have : 0 < ε ^ 2 / (2 * c) := by positivity
      linarith
    set κ := d * (1 - μ⁻¹) with hκ
    have hκpos : 0 < κ := by
      have : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ1
      have : 0 < 1 - μ⁻¹ := by linarith
      positivity
    have hC' : Tendsto (fun y => I (μ⁻¹ * y) - I y) atTop (𝓝 0) := hC μ⁻¹ (inv_pos.mpr hμ0)
    obtain ⟨y, hyS, hyC, hy1⟩ :=
      (h.and_eventually ((hC'.eventually (eventually_lt_nhds hκpos)).and
        (eventually_ge_atTop μ))).exists
    have hy0 : 0 < y := by linarith
    set x := μ⁻¹ * y with hxdef
    have hx0 : 0 < x := by positivity
    have hx1 : 1 ≤ x := by
      rw [hxdef, ← div_eq_inv_mul, le_div_iff₀ hμ0]; linarith
    have hyx : y = μ * x := by rw [hxdef]; field_simp
    have hyS' : S y < (c - ε) * y := by
      rw [not_le, div_lt_iff₀ hy0] at hyS; exact hyS
    have hxle : x ≤ y := by rw [hyx]; nlinarith
    have hle : ∫ t in x..y, F t ≤ -κ := by
      have hm := intervalIntegral.integral_mono_on hxle (hii x y hx0 hy0)
        (intervalIntegrable_const (c := -d / y)) ?_
      · rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        refine le_trans hm (le_of_eq ?_)
        rw [hκ, hyx]; field_simp
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hSt : S t < (c - ε) * y := lt_of_le_of_lt (hmono ht.2) hyS'
        have hyt : y ≤ μ * t := by rw [hyx]; nlinarith [ht.1]
        have h2 : S t / t - c ≤ -d := by
          rw [hd, div_sub' ht0.ne', div_le_iff₀ ht0]
          have : (c - ε) * y ≤ (c - ε) * (μ * t) :=
            mul_le_mul_of_nonneg_left hyt (by linarith)
          nlinarith
        have h3 : (S t / t - c) / t ≤ -d / t := div_le_div_of_nonneg_right h2 ht0.le
        have h4 : -d / t ≤ -d / y := by
          rw [neg_div, neg_div, neg_le_neg_iff]
          exact div_le_div_of_nonneg_left hdpos.le ht0 ht.2
        simp only [hF]
        linarith
    have := hdiff x y hx1 (by linarith)
    simp only [hIdef] at hyC this
    linarith
  rw [tendsto_order]
  constructor
  · intro a' ha'
    set ε := min ((c - a') / 2) (c / 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    have hεc : ε < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hεa : ε < c - a' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    filter_upwards [lo ε hε0 hεc] with x hx
    linarith
  · intro a' ha'
    filter_upwards [up ((a' - c) / 2) (by linarith)] with x hx
    linarith

end tauberian

/-! ## Primes in arithmetic progressions and the Prime Number Theorem -/

section application

open ArithmeticFunction ArithmeticFunction.vonMangoldt DirichletCharacter

variable {q : ℕ}

/-- Chebyshev's `ψ` restricted to the residue class `b` mod `q`. -/
noncomputable def psiAP (b : ZMod q) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, residueClass b k

theorem psiAP_nonneg (b : ZMod q) (x : ℝ) : 0 ≤ psiAP b x :=
  Finset.sum_nonneg fun k _ => residueClass_nonneg b k

theorem psiAP_mono (b : ZMod q) : Monotone (psiAP b) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy))
  intro k _ _; exact residueClass_nonneg b k

theorem Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

theorem psiAP_le (b : ZMod q) {x : ℝ} (hx : 0 ≤ x) : psiAP b x ≤ (Real.log 4 + 4) * x := by
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self hx)
  rw [Chebyshev.psi, psiAP, Icc_one_eq_Ioc_zero]
  exact Finset.sum_le_sum fun k _ => residueClass_le b k

theorem psiAP_measurable (b : ZMod q) : Measurable (psiAP b) :=
  (measurable_from_nat (f := fun n => ∑ k ∈ Finset.Icc 1 n, residueClass b k)).comp
    Nat.measurable_floor

theorem psiAP_div_bound (b : ZMod q) {x : ℝ} (hx : 1 ≤ x) :
    |psiAP b x / x| ≤ Real.log 4 + 4 := by
  have hx0 : 0 < x := by linarith
  rw [abs_of_nonneg (div_nonneg (psiAP_nonneg b x) hx0.le), div_le_iff₀ hx0]
  exact psiAP_le b hx0.le

theorem A_bound (b : ZMod q) {x : ℝ} (hx : 1 ≤ x) :
    |psiAP b x / x - (q.totient : ℝ)⁻¹| ≤ Real.log 4 + 4 + (q.totient : ℝ)⁻¹ := by
  have h1 := psiAP_div_bound b hx
  have h2 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc _ ≤ |psiAP b x / x| + |(q.totient : ℝ)⁻¹| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg h2]; linarith

theorem A_measurable (b : ZMod q) :
    Measurable (fun x => psiAP b x / x - (q.totient : ℝ)⁻¹) :=
  ((psiAP_measurable b).div measurable_id).sub measurable_const

variable [NeZero q]

/-- The open set on which the auxiliary function is holomorphic (shifted by one). -/
def Uq (q : ℕ) [NeZero q] : Set ℂ :=
  {z | z + 1 ≠ 0} ∩ {z | LFunctionTrivChar₁ q (z + 1) ≠ 0} ∩
    ⋂ χ ∈ {χ : DirichletCharacter ℂ q | χ ≠ 1}, {z | LFunction χ (z + 1) ≠ 0}

theorem Uq_open : IsOpen (Uq q) := by
  refine ((isOpen_ne_fun (by fun_prop) continuous_const).inter
    (isOpen_ne_fun ((differentiable_LFunctionTrivChar₁ q).continuous.comp (by fun_prop))
      continuous_const)).inter ?_
  refine Set.Finite.isOpen_biInter (Set.toFinite _) fun χ hχ => ?_
  exact isOpen_ne_fun ((differentiable_LFunction hχ).continuous.comp (by fun_prop))
    continuous_const

theorem LFunctionTrivChar₁_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : LFunctionTrivChar₁ q s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · exact LFunctionTrivChar₁_apply_one_ne_zero q
  · simp only [LFunctionTrivChar₁, Function.update_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (LFunction_ne_zero_of_one_le_re 1 (.inr h1) hs)

theorem mem_Uq {z : ℂ} (hz : 0 ≤ z.re) : z ∈ Uq q := by
  have hs : 1 ≤ (z + 1).re := by simp; linarith
  refine ⟨⟨?_, LFunctionTrivChar₁_ne_zero hs⟩, ?_⟩
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · simp only [mem_iInter₂, mem_ofPred_eq]
    intro χ hχ
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

/-- The shifted auxiliary function `(Aux(z+1) - 1/φ(q)) / (z+1)`. -/
noncomputable def Gq (b : ZMod q) (z : ℂ) : ℂ :=
  (LFunctionResidueClassAux b (z + 1) - (q.totient : ℂ)⁻¹) / (z + 1)

theorem aux_differentiableAt (b : ZMod q) {s : ℂ} (h1 : LFunctionTrivChar₁ q s ≠ 0)
    (h2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (LFunctionResidueClassAux b) s := by
  unfold LFunctionResidueClassAux
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · apply DifferentiableAt.div _ (differentiable_LFunctionTrivChar₁ q s) h1
    exact (((differentiable_LFunctionTrivChar₁ q).analyticAt s).deriv.differentiableAt).neg
  · apply DifferentiableAt.fun_sum
    intro χ hχ
    have hχ1 : χ ≠ 1 := by simpa using hχ
    apply DifferentiableAt.div _ (differentiable_LFunction hχ1 s) (h2 χ hχ1)
    exact (((differentiable_LFunction hχ1).analyticAt s).deriv.differentiableAt).const_mul _

theorem Gq_differentiableOn (b : ZMod q) : DifferentiableOn ℂ (Gq b) (Uq q) := by
  intro z hz
  obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
  simp only [mem_iInter₂, mem_ofPred_eq] at hz1 hz2 hz3
  apply DifferentiableAt.differentiableWithinAt
  unfold Gq
  have hD : DifferentiableAt ℂ
      (fun w => LFunctionResidueClassAux b (w + 1) - (q.totient : ℂ)⁻¹) z :=
    ((aux_differentiableAt b hz2 hz3).comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w + 1) z)).sub_const _
  exact hD.div (by fun_prop) hz1

theorem Gq_eq (b : ZMod q) (hb : IsUnit b) {z : ℂ} (hz : 0 < z.re) :
    Gq b z = Gint (fun x => psiAP b x / x - (q.totient : ℝ)⁻¹) z := by
  set s := z + 1 with hsdef
  have hs : 1 < s.re := by simp [hsdef]; linarith
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hre : (-z - 1).re < -1 := by simp; linarith
  have I1 : IntegrableOn (fun t : ℝ => ((psiAP b t / t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) (Ioi 1) :=
    integrableOn_integrand ((psiAP_measurable b).div measurable_id)
      (fun x hx => psiAP_div_bound b hx) hz le_rfl
  have I2 : IntegrableOn (fun t : ℝ => ((q.totient : ℝ)⁻¹ : ℂ) * (t : ℂ) ^ (-z - 1)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hre one_pos).const_mul _
  have h1 : Gint (fun x => psiAP b x / x - (q.totient : ℝ)⁻¹) z =
      (∫ t in Ioi (1 : ℝ), ((psiAP b t / t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) -
        ∫ t in Ioi (1 : ℝ), ((q.totient : ℝ)⁻¹ : ℂ) * (t : ℂ) ^ (-z - 1) := by
    unfold Gint
    rw [← integral_sub I1 I2]
    congr 1; ext t; push_cast; ring
  have h2 : ∫ t in Ioi (1 : ℝ), ((q.totient : ℝ)⁻¹ : ℂ) * (t : ℂ) ^ (-z - 1) =
      ((q.totient : ℝ)⁻¹ : ℂ) / z := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hre one_pos]
    simp only [ofReal_one, one_cpow, sub_add_cancel]
    field_simp
  have h3 : ∫ t in Ioi (1 : ℝ), ((psiAP b t / t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) =
      ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((residueClass b k : ℝ) : ℂ)) *
        (t : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by simp at ht; linarith)
    have e : -(s + 1) = (-z - 1) - 1 := by rw [hsdef]; ring
    simp only [e, cpow_sub _ _ ht0, cpow_one, psiAP]
    push_cast
    field_simp
  have hS : LSeriesSummable (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_residueClass_le_one b).trans_lt (by exact_mod_cast hs))
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    have e : (∑ k ∈ Finset.Icc 1 n, (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) k) = ((psiAP b n : ℝ) : ℂ) := by
      simp [psiAP, Nat.floor_natCast]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (psiAP_nonneg b _),
      Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact psiAP_le b (Nat.cast_nonneg _)
  have h4 := LSeries_eq_mul_integral (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) zero_le_one hs hS hO
  have h5 := eqOn_LFunctionResidueClassAux hb (show s ∈ {s : ℂ | 1 < s.re} from hs)
  simp only at h5
  have hsz : s - 1 = z := by rw [hsdef]; ring
  rw [hsz] at h5
  rw [h1, h2, h3]
  unfold Gq
  rw [← hsdef, h5, h4]
  push_cast
  field_simp
  ring

/-- **Prime number theorem in arithmetic progressions**: `ψ(x; q, b) / x → 1/φ(q)`. -/
theorem tendsto_psiAP (b : ZMod q) (hb : IsUnit b) :
    Tendsto (fun x => psiAP b x / x) atTop (𝓝 (q.totient : ℝ)⁻¹) := by
  have hc : 0 < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    positivity
  exact taub hc (psiAP_mono b)
    (newman_real (A_measurable b) (fun x hx => A_bound b hx) Uq_open (fun z hz => mem_Uq hz)
      (Gq_differentiableOn b) (fun z hz => Gq_eq b hb hz))

end application

/-! ## The Prime Number Theorem -/

section pnt

theorem psiAP_one (x : ℝ) : psiAP (1 : ZMod 1) x = Chebyshev.psi x := by
  rw [psiAP, Chebyshev.psi, Icc_one_eq_Ioc_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim _ _) _

/-- `ψ(x) / x → 1`. -/
theorem tendsto_psi_div : Tendsto (fun x => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have := tendsto_psiAP (q := 1) (1 : ZMod 1) isUnit_one
  simpa [psiAP_one] using this

/-- `θ(x) / x → 1`. -/
theorem tendsto_theta_div : Tendsto (fun x => Chebyshev.theta x / x) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have h0 : Tendsto (fun x => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => C / Real.sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) hx.le
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
      calc (Chebyshev.psi x - Chebyshev.theta x) / x ≤ C * Real.sqrt x / x :=
            div_le_div_of_nonneg_right (hC x) hx.le
        _ = C / Real.sqrt x := by
            rw [div_eq_div_iff hx.ne' hs.ne', mul_assoc, hsq]
  have := tendsto_psi_div.sub h0
  simp only [sub_zero] at this
  refine this.congr fun x => ?_
  ring

/-- **Prime Number Theorem**: `π(x) / (x / log x) → 1`. -/
theorem tendsto_primeCounting_div : Tendsto
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.bound
  have hE : Tendsto (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) *
      (Real.log x / x)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => |C| / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hC, eventually_gt_atTop 1] with x hx hx1
    have hl : 0 < Real.log x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Real.norm_eq_abs (Real.log x / x), abs_of_pos (by positivity)]
    rw [Real.norm_eq_abs (x / Real.log x ^ 2), abs_of_pos (by positivity)] at hx
    calc _ ≤ C * (x / Real.log x ^ 2) * (Real.log x / x) :=
          mul_le_mul_of_nonneg_right hx (by positivity)
      _ = C / Real.log x := by field_simp
      _ ≤ |C| / Real.log x := div_le_div_of_nonneg_right (le_abs_self C) hl.le
  have := tendsto_theta_div.add hE
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  field_simp
  ring

/-- **Prime Number Theorem**, asymptotic-equivalence form: `π(x) ~ x / log x`. -/
theorem primeCounting_isEquivalent : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
    (fun x : ℝ => x / Real.log x) :=
  isEquivalent_of_tendsto_one tendsto_primeCounting_div

/-- **Prime Number Theorem** for natural numbers: `π(n) / (n / log n) → 1`. -/
theorem tendsto_primeCounting_nat : Tendsto
    (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
  have := tendsto_primeCounting_div.comp tendsto_natCast_atTop_atTop
  refine this.congr fun n => ?_
  simp [Function.comp, Nat.floor_natCast]

end pnt

end OMAPNT

end kitPNT

theorem OMA.solution : OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2.H1 := by
  have h := OMAPNT.tendsto_psi_div.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr' ?_
  filter_upwards with N
  simp only [Function.comp_apply, Chebyshev.psi, Nat.floor_natCast]
