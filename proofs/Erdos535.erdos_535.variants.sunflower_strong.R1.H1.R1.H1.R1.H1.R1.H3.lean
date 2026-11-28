import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1

/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Copyright OpenAI. Apache-2.0. -/
-- OAI.Compat
section

/-! Compatibility shims for the Lean v4.33.1 / formal-conjectures Mathlib pin.
Each restates a lemma that exists under this name in the newer Mathlib used by openai/math. -/

theorem ite_eq_left {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort*} {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort*} {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

theorem Measurable.of_eval {α : Type*} {ι : Type*} {X : ι → Type*} [MeasurableSpace α]
    [∀ i, MeasurableSpace (X i)] {f : α → ∀ i, X i} (hf : ∀ i, Measurable fun a => f a i) :
    Measurable f := measurable_pi_lambda f hf

open MeasureTheory in
theorem charFun_map_eq_charFun_map_inner_one {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} {Y : Ω → E} (hY : AEMeasurable Y μ) (t : E) :
    charFun (μ.map Y) t = charFun (μ.map fun ω => inner ℝ (Y ω) t) 1 := by
  have hc : Continuous fun x : E => inner ℝ x t := continuous_id.inner continuous_const
  have hY' : AEMeasurable (fun ω => inner ℝ (Y ω) t) μ := hc.measurable.comp_aemeasurable hY
  rw [charFun_apply, charFun_apply, integral_map hY, integral_map hY']
  · simp
  · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (inner ℝ x (1:ℝ) * Complex.I)).aestronglyMeasurable
  · exact (by fun_prop : Continuous fun x : E => Complex.exp (inner ℝ x t * Complex.I)).aestronglyMeasurable
end
-- OAI.LinearAlgebra.SpectralBooks.AffinePatch
section

/-! # Centering a Euclidean patch in its affine span -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonempty convex patch admits affine Euclidean coordinates centered at a
relative interior point. This also applies to a singleton in its zero-dimensional span. -/
theorem exists_centered_affinePatch {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty) :
    ∃ i : (affineSpan ℝ C).direction →ᵃⁱ[ℝ] E,
      C ⊆ range i ∧ (0 : (affineSpan ℝ C).direction) ∈ interior (i ⁻¹' C) := by
  let A := affineSpan ℝ C
  obtain ⟨x, hx⟩ := hne
  let : Nonempty A := ⟨⟨x, subset_affineSpan ℝ C hx⟩⟩
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := Set.Nonempty.intrinsicInterior hC (show C.Nonempty from ⟨x, hx⟩)
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ z
  let i := A.subtypeₐᵢ.comp e.toAffineIsometry
  refine ⟨i, ?_, ?_⟩
  · intro y hy
    let y' : A := ⟨y, subset_affineSpan ℝ C hy⟩
    obtain ⟨v, hv⟩ := e.surjective y'
    exact ⟨v, congrArg Subtype.val hv⟩
  · let B : Set A := Subtype.val ⁻¹' C
    change 0 ∈ interior (e.toHomeomorph ⁻¹' B)
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior B
    simpa [e] using hz

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.Width
section

/-!
# Mean width of a finite Euclidean configuration

We use the Gaussian normalization of the manuscript. The first variation when a
site leaves the origin is an integral over the directions supported at the origin.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Support function of a finite nonempty set of sites. -/
def support (S : Finset E) (hS : S.Nonempty) (u : E) : ℝ :=
  S.sup' hS (fun x ↦ ⟪u, x⟫)

theorem support_insert (S : Finset E) (hS : S.Nonempty) (v u : E) :
    support (insert v S) (Finset.insert_nonempty v S) u =
      max ⟪u, v⟫ (support S hS u) :=
  Finset.sup'_insert hS _

theorem support_smul (S : Finset E) (hS : S.Nonempty) (u : E) {a : ℝ} (ha : 0 ≤ a) :
    support (S.image (a • ·)) (hS.image _) u = a * support S hS u := by
  unfold support
  rw [Finset.sup'_image]
  simpa only [Function.comp_apply, real_inner_smul_right] using
    (Finset.apply_sup'_eq_sup'_comp hS (a * ·)
      (fun b c ↦ mul_max_of_nonneg b c ha) (f := fun x ↦ ⟪u, x⟫)).symm

theorem support_nonneg_of_zero_mem {S : Finset E} (h0 : 0 ∈ S) (u : E) :
    0 ≤ support S ⟨0, h0⟩ u := by
  simpa only [support, inner_zero_right] using S.le_sup' (fun x ↦ ⟪u, x⟫) h0

/-- Directions at which the origin supports the given configuration. -/
def normalConeAtZero (S : Finset E) : Set E :=
  {u | ∀ x ∈ S, ⟪u, x⟫ ≤ 0}

theorem mem_normalConeAtZero_iff {S : Finset E} (h0 : 0 ∈ S) (u : E) :
    u ∈ normalConeAtZero S ↔ support S ⟨0, h0⟩ u = 0 := by
  change (∀ x ∈ S, ⟪u, x⟫ ≤ 0) ↔ _
  rw [← Finset.sup'_le_iff ⟨0, h0⟩ (fun x ↦ ⟪u, x⟫)]
  exact ⟨(le_antisymm · (support_nonneg_of_zero_mem h0 u)), Eq.le⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem measurableSet_normalConeAtZero (S : Finset E) : MeasurableSet (normalConeAtZero S) := by
  have heq : normalConeAtZero S = ⋂ x ∈ (S : Set E), {u : E | ⟪u, x⟫ ≤ 0} := by
    ext
    simp [normalConeAtZero]
  rw [heq]
  exact .biInter S.countable_toSet fun x _ ↦
    measurableSet_le (f := fun u : E ↦ ⟪u, x⟫) (by fun_prop) measurable_const

/-- Gaussian mean width, normalized to give a segment its Euclidean length. -/
def meanWidth (S : Finset E) (hS : S.Nonempty) : ℝ :=
  Real.sqrt (2 * Real.pi) * ∫ u, support S hS u ∂stdGaussian E

theorem integrable_support (S : Finset E) (hS : S.Nonempty) :
    Integrable (support S hS) (stdGaussian E) := by
  have heq : support S hS = S.sup' hS (fun x u ↦ ⟪u, x⟫) := by
    funext u
    exact (Finset.sup'_apply hS (fun (x u : E) ↦ ⟪u, x⟫) u).symm
  rw [heq]
  refine Finset.sup'_induction hS _ (p := fun f : E → ℝ ↦ Integrable f (stdGaussian E))
    (fun _ hf _ hg ↦ hf.sup hg) (fun x _ ↦ ?_)
  exact (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const x

omit [BorelSpace E] in
theorem meanWidth_smul (S : Finset E) (hS : S.Nonempty) {a : ℝ} (ha : 0 ≤ a) :
    meanWidth (S.image (a • ·)) (hS.image _) = a * meanWidth S hS := by
  simp only [meanWidth, support_smul S hS _ ha, integral_const_mul, ← mul_assoc]
  rw [mul_comm (Real.sqrt _)]

/-- The exact width increment upon adjoining a site to a dilation. -/
theorem meanWidth_insert_smul_sub (S : Finset E) (hS : S.Nonempty) (v : E)
    {a : ℝ} (ha : 0 ≤ a) :
    meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
      meanWidth (S.image (a • ·)) (hS.image _) =
    Real.sqrt (2 * Real.pi) *
      ∫ u, max (⟪u, v⟫ - a * support S hS u) 0 ∂stdGaussian E := by
  unfold meanWidth
  rw [← mul_sub, ← integral_sub (integrable_support _ _) (integrable_support _ _)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  simp only [support_insert _ (hS.image _), support_smul S hS u ha]
  rcases le_total ⟪u, v⟫ (a * support S hS u) with h | h
  · simp [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
  · simp [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]

private theorem tendsto_max_sub_mul (b : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun a : ℝ ↦ max (b - a * s) 0) atTop
      (𝓝 (if s = 0 then max b 0 else 0)) := by
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ite_false]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (b / s)] with a ha
    exact (max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (lt_of_le_of_ne hs (Ne.symm h))).mp ha))).symm

/-- The large-dilation limit in the width-marginal formula, using the equivalent
Gaussian integral of the support function. -/
theorem tendsto_meanWidth_insert_smul_sub {S : Finset E} (h0 : 0 ∈ S) (v : E) :
    Tendsto (fun a : ℝ ↦
      meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
        meanWidth (S.image (a • ·)) (Finset.Nonempty.image ⟨0, h0⟩ _)) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) *
        ∫ u in normalConeAtZero S, max ⟪u, v⟫ 0 ∂stdGaussian E)) := by
  have hS : S.Nonempty := ⟨0, h0⟩
  have hv : Integrable (fun u : E ↦ ⟪u, v⟫) (stdGaussian E) :=
    (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const v
  rw [← integral_indicator (measurableSet_normalConeAtZero S)]
  apply Filter.Tendsto.congr' _ (tendsto_const_nhds.mul
    (tendsto_integral_filter_of_dominated_convergence (fun u : E ↦ max ⟪u, v⟫ 0)
      (μ := stdGaussian E) (F := fun (a : ℝ) u ↦ max (⟪u, v⟫ - a * support S hS u) 0)
      ?_ ?_ (hv.sup (integrable_const 0)) ?_))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    exact (meanWidth_insert_smul_sub S hS v ha).symm
  · exact .of_forall fun a ↦
      ((hv.sub ((integrable_support S hS).const_mul a)).sup (integrable_const 0)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    refine ae_of_all _ fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (sub_le_self _ (mul_nonneg ha (support_nonneg_of_zero_mem h0 u))) le_rfl
  · refine ae_of_all _ fun u ↦ ?_
    simpa only [Set.indicator_apply, mem_normalConeAtZero_iff h0] using
      tendsto_max_sub_mul ⟪u, v⟫ (support_nonneg_of_zero_mem h0 u)

/-- Right derivative at the instant when the added site separates from the origin. -/
theorem hasDerivWithinAt_meanWidth_insert {S : Finset E} (h0 : 0 ∈ S) (v : E) :
    HasDerivWithinAt
      (fun h : ℝ ↦ meanWidth (insert (h • v) S) (Finset.insert_nonempty _ _))
      (Real.sqrt (2 * Real.pi) *
        ∫ u in normalConeAtZero S, max ⟪u, v⟫ 0 ∂stdGaussian E) (Set.Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi]
  apply ((tendsto_meanWidth_insert_smul_sub h0 v).comp tendsto_inv_nhdsGT_zero).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : (0 : ℝ) < h := hh
  have hS : S.Nonempty := ⟨0, h0⟩
  have hmove := meanWidth_smul (insert (h • v) S) (Finset.insert_nonempty _ _)
    (inv_nonneg.mpr hp.le)
  simp only [Finset.image_insert, inv_smul_smul₀ hp.ne'] at hmove
  simp only [Function.comp_apply, slope_def_field, zero_smul, Finset.insert_eq_of_mem h0,
    sub_zero, hmove, meanWidth_smul S hS (inv_nonneg.mpr hp.le)]
  ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.GaussianAbsolute
section

/-! # Absolute first moment of the standard Gaussian -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Real Set

section

/-- The Gaussian normalization used for the mean width gives a segment of length two
when its endpoints are the two unit vectors on the real line. -/
theorem normalized_integral_abs_gaussianReal :
    √(2 * π) * (∫ x : ℝ, |x| ∂(gaussianReal 0 1)) = 2 := by
  have hpos : (∫ x : ℝ in Ioi 0, x * exp (-(1 / 2) * x ^ 2)) = 1 := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.Gamma_one] at h
    simpa only [neg_mul] using h
  have hfull : (∫ x : ℝ, |x| * exp (-(1 / 2) * x ^ 2)) = 2 := by
    have h := integral_comp_abs (f := fun x : ℝ ↦ x * exp (-(1 / 2) * x ^ 2))
    change (∫ x : ℝ, |x| * exp (-(1 / 2) * |x| ^ 2)) =
      2 * ∫ x : ℝ in Ioi 0, x * exp (-(1 / 2) * x ^ 2) at h
    simpa only [sq_abs, hpos, mul_one] using h
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  convert hfull using 1
  congr 1
  ext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, mul_comm]
  congr 2
  ring

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TriangleWidth
section

/-! # Gaussian mean width of segments and triangles -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalized_integral_abs_inner (x : E) :
    Real.sqrt (2 * Real.pi) * ∫ u, |⟪u, x⟫| ∂(stdGaussian E) = 2 * ‖x‖ := by
  let L := innerSL ℝ x
  have hmap : (stdGaussian E).map L = (gaussianReal 0 1).map (‖x‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, gaussianReal_map_const_mul,
      integral_strongDual_stdGaussian, variance_dual_stdGaussian]
    simp [L, Real.toNNReal_of_nonneg (sq_nonneg ‖x‖)]
  have hi : (∫ u, |⟪u, x⟫| ∂(stdGaussian E)) =
      ‖x‖ * ∫ t : ℝ, |t| ∂(gaussianReal 0 1) := by
    calc
      _ = ∫ t : ℝ, |t| ∂((stdGaussian E).map L) := by
        rw [integral_map L.continuous.aemeasurable (by fun_prop)]
        simp only [L, innerSL_apply_apply, real_inner_comm x]
      _ = ∫ t : ℝ, |‖x‖ * t| ∂(gaussianReal 0 1) := by
        rw [hmap, integral_map (by fun_prop) (by fun_prop)]
      _ = _ := by simp [abs_mul, integral_const_mul]
  rw [hi, mul_left_comm, normalized_integral_abs_gaussianReal, mul_comm]

private theorem twice_range_of_three (a b c : ℝ) :
    2 * (max a (max b c) + max (-a) (max (-b) (-c))) =
      |a - b| + |b - c| + |c - a| := by
  grind [abs_eq_max_neg]

private theorem integral_precomp_neg (f : E → ℝ) (hf : AEStronglyMeasurable f (stdGaussian E)) :
    (∫ u, f (-u) ∂(stdGaussian E)) = ∫ u, f u ∂(stdGaussian E) := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have he := stdGaussian_map e
  calc
    _ = ∫ u, f u ∂((stdGaussian E).map e) :=
      (integral_map e.continuous.aemeasurable (by simpa only [he] using hf)).symm
    _ = _ := by rw [he]

/-- The Gaussian mean width of three vertices equals their half-perimeter, allowing
repeated or collinear vertices. -/
theorem meanWidth_triangle [DecidableEq E] (a b c : E) :
    meanWidth {a, b, c} (Finset.insert_nonempty _ _) =
      (dist a b + dist b c + dist c a) / 2 := by
  let f (u : E) := max ⟪u, a⟫ (max ⟪u, b⟫ ⟪u, c⟫)
  have hproj (v : E) : Integrable (fun u : E ↦ ⟪u, v⟫) (stdGaussian E) :=
    (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const v
  have hf : Integrable f (stdGaussian E) := (hproj a).sup ((hproj b).sup (hproj c))
  have hf' : Integrable (fun u ↦ f (-u)) (stdGaussian E) := by
    simp only [f, inner_neg_left]
    exact (hproj a).neg.sup ((hproj b).neg.sup (hproj c).neg)
  have hwidth (u : E) :
      2 * (f u + f (-u)) = |⟪u, a - b⟫| + |⟪u, b - c⟫| + |⟪u, c - a⟫| := by
    simpa only [f, inner_neg_left, inner_sub_right] using
      twice_range_of_three ⟪u, a⟫ ⟪u, b⟫ ⟪u, c⟫
  have heq := congrArg (fun g : E → ℝ ↦ ∫ u, g u ∂(stdGaussian E)) (funext hwidth)
  rw [integral_const_mul, integral_add hf hf', integral_precomp_neg f hf.aestronglyMeasurable,
    integral_add ((hproj (a - b)).abs.fun_add (hproj (b - c)).abs) (hproj (c - a)).abs,
    integral_add (hproj (a - b)).abs (hproj (b - c)).abs] at heq
  have hs : support {a, b, c} (Finset.insert_nonempty _ _) = f := by
    funext u
    simp only [support, Finset.sup'_insert (Finset.insert_nonempty _ _),
      Finset.sup'_insert (Finset.singleton_nonempty _), Finset.sup'_singleton, f]
  unfold meanWidth
  rw [hs]
  simp only [dist_eq_norm]
  linarith only [congrArg (Real.sqrt (2 * Real.pi) * ·) heq,
    normalized_integral_abs_inner (a - b), normalized_integral_abs_inner (b - c),
    normalized_integral_abs_inner (c - a)]

/-- A segment has normalized mean width equal to its length. -/
theorem meanWidth_pair [DecidableEq E] (a b : E) :
    meanWidth {a, b} (Finset.insert_nonempty _ _) = dist a b := by
  simpa [dist_comm b a] using meanWidth_triangle a b b

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- GaussianIsometry
section
/- Copyright OpenAI, Apache-2.0. Extracted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 AngularWidth.lean. No polar-coordinate dependency is needed for Gaussian isometry invariance. -/
namespace OAI.LinearAlgebra.SpectralBooks
noncomputable section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Translation adds a linear function to the support. Its Gaussian expectation vanishes. -/
theorem meanWidth_translate [DecidableEq E] (T : Finset E) (hT : T.Nonempty) (a : E) :
    meanWidth (T.image (· + a)) (hT.image _) = meanWidth T hT := by
  have heq (u : E) : support (T.image (· + a)) (hT.image _) u =
      support T hT u + ⟪u, a⟫ := by
    simp only [support, Finset.sup'_image, Function.comp_apply, inner_add_right,
      Finset.sup'_add]
  have hlin : (∫ u, ⟪u, a⟫ ∂stdGaussian E) = 0 := by
    simpa only [innerSL_apply_apply, real_inner_comm a] using
      integral_strongDual_stdGaussian (innerSL ℝ a)
  simp only [meanWidth, heq, integral_add (integrable_support T hT)
    ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const a), hlin, add_zero]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Embedding the sites linearly and isometrically preserves their mean width,
including when the ambient dimension increases. -/
theorem meanWidth_linearIsometry [DecidableEq F] (i : E →ₗᵢ[ℝ] F)
    (T : Finset E) (hT : T.Nonempty) :
    meanWidth (T.image i) (hT.image _) = meanWidth T hT := by
  let p := ContinuousLinearMap.adjoint i.toContinuousLinearMap
  have hmap : (stdGaussian F).map p = stdGaussian E := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, integral_map p.continuous.aemeasurable (by fun_prop)]
    simp only [p, ContinuousLinearMap.adjoint_inner_left]
    change charFun (stdGaussian F) (i t) = charFun (stdGaussian E) t
    simp [charFun_stdGaussian]
  have heq (u : F) : support (T.image i) (hT.image _) u = support T hT (p u) := by
    simp only [support, Finset.sup'_image, Function.comp_apply, p,
      ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap]
  have h := integral_map p.continuous.aemeasurable
    (f := support T hT) (μ := stdGaussian F) (by
      rw [hmap]
      exact (integrable_support T hT).aestronglyMeasurable)
  rw [hmap] at h
  simp only [meanWidth, heq, h]

/-- The support-integral mean width is invariant under affine isometric embeddings. -/
theorem meanWidth_affineIsometry [DecidableEq F] (i : E →ᵃⁱ[ℝ] F)
    (T : Finset E) (hT : T.Nonempty) :
    meanWidth (T.image i) (hT.image _) = meanWidth T hT := by
  have heq : T.image i = (T.image i.linearIsometry).image (· + i 0) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simpa using i.map_vadd (0 : E) x
  rw [show meanWidth (T.image i) (hT.image _) =
      meanWidth ((T.image i.linearIsometry).image (· + i 0)) ((hT.image _).image _) by simp only [← heq],
    meanWidth_translate _ (hT.image _) _, meanWidth_linearIsometry i.linearIsometry T hT]

end
end OAI.LinearAlgebra.SpectralBooks
end
-- OAI.LinearAlgebra.SpectralBooks.PlacementConvexity
section

/-! # Consequences of convexity of placed diagonal prices

A finite list of synchronized straight-line interpolations is recorded by its
finite set of endpoint pairs. Duplicates at an occupied site have no effect
on the diagonal price. In a homogeneous flat, the midpoint inequality for
all pairs of vertices implies subadditivity for Minkowski addition.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- Joint convexity of diagonal prices along synchronized straight lines. -/
def JointlyConvexPrice (δ : Finset E → ℝ) : Prop :=
  ∀ (P : Finset (E × E)), P.Nonempty → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    δ (P.image fun p ↦ a • p.1 + b • p.2) ≤
      a * δ (P.image Prod.fst) + b * δ (P.image Prod.snd)

/-- On a homogeneous flat, interpolating a list indexed by the full product of
two vertex sets gives the subadditive inequality for their Minkowski sum. -/
theorem price_add_le_of_jointConvex (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S) (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    δ (S + T) ≤ δ S + δ T := by
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have h := hjoint (S ×ˢ T) (hS.product hT) r r hr.le hr.le (by norm_num [r])
  have himage : (S ×ˢ T).image (fun p ↦ r • p.1 + r • p.2) = (S + T).image (r • ·) := by
    simp only [Finset.add_def, Finset.image_image, Function.comp_def, smul_add]
  rw [himage, hscale _ (hS.add hT) r hr, Finset.product_image_fst hT,
    Finset.product_image_snd hS] at h
  dsimp [r] at h
  linarith

omit [Module ℝ E] in
/-- Adding a singleton gives a translate, and adding its negative translates back. -/
theorem price_translate_of_add_le (δ : Finset E → ℝ)
    (hsubadd : ∀ (S T : Finset E), S.Nonempty → T.Nonempty → δ (S + T) ≤ δ S + δ T)
    (hsingle : ∀ x : E, δ {x} = 0) (S : Finset E) (hS : S.Nonempty) (v : E) :
    δ (S + {v}) = δ S := by
  apply le_antisymm
  · simpa [hsingle] using hsubadd S {v} hS (Finset.singleton_nonempty _)
  · have h := hsubadd (S + {v}) {-v} (hS.add (Finset.singleton_nonempty _))
        (Finset.singleton_nonempty _)
    simpa only [add_assoc, Finset.singleton_add_singleton, add_neg_cancel, hsingle, add_zero,
      show ({0} : Finset E) = 0 by rfl] using h

/-- Adjoining a point in the convex hull leaves a monotone, jointly convex
diagonal price unchanged. -/
theorem price_insert_of_mem_convexHull (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (S : Finset E) (hS : S.Nonempty) {z : E} (hz : z ∈ convexHull ℝ (S : Set E)) :
    δ (insert z S) = δ S := by
  refine le_antisymm (?_ : z ∈ {w : E | δ (insert w S) ≤ δ S})
    (hmono hS (Finset.subset_insert _ _))
  apply convexHull_min (t := {w : E | δ (insert w S) ≤ δ S}) _ _ hz
  · intro x hx
    simp [Finset.insert_eq_of_mem hx]
  · intro x hx y hy a b ha hb hab
    let P := S.image (fun s ↦ (s, s))
    have h := hjoint (insert (x, y) P) (Finset.insert_nonempty _ _) a b ha hb hab
    have hid (s : E) : a • s + b • s = s := by rw [← add_smul, hab, one_smul]
    simp [P, Finset.image_image, Function.comp_def, hid] at h
    change δ (insert (a • x + b • y) S) ≤ δ S
    change δ (insert x S) ≤ δ S at hx
    change δ (insert y S) ≤ δ S at hy
    calc
      _ ≤ a * δ (insert x S) + b * δ (insert y S) := h
      _ ≤ a * δ S + b * δ S := add_le_add
        (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- Adjoining a finite family of points in the convex hull preserves price. -/
theorem price_union_of_subset_convexHull (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (S T : Finset E) (hS : S.Nonempty) (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) :
    δ (S ∪ T) = δ S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert z T hz ih =>
    have hzS := hT (Finset.mem_insert_self z T)
    have hT' := fun y (hy : y ∈ T) ↦ hT (Finset.mem_insert_of_mem hy)
    have hsub : (S : Set E) ⊆ ↑(S ∪ T) := Finset.subset_union_left
    rw [Finset.union_insert, price_insert_of_mem_convexHull δ hjoint hmono _
      (hS.mono Finset.subset_union_left) (convexHull_mono hsub hzS), ih hT']

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TangentPrice
section

/-! # One-sided tangent prices of convex dilation profiles -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology

/-- At the center of a dilation the price vanishes. Nonnegativity then bounds
its increasing secant slopes from below, giving a finite tangent price. -/
theorem exists_tangentPrice {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hconv : ConvexOn ℝ (Icc 0 R) f) (hzero : f 0 = 0)
    (hnonneg : ∀ h ∈ Icc 0 R, 0 ≤ f h) :
    ∃ D : ℝ, 0 ≤ D ∧ Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 D) := by
  have hm : MonotoneOn (slope f 0) (Ioo 0 R) :=
    (hconv.monotoneOn_slope_gt ⟨le_rfl, hR.le⟩).mono
      (fun _ hh ↦ ⟨Ioo_subset_Icc_self hh, hh.1⟩)
  have hl : 0 ∈ lowerBounds (slope f 0 '' Ioo 0 R) := by
    rintro _ ⟨h, hh, rfl⟩
    simpa only [slope_def_field, hzero, sub_zero] using
      div_nonneg (hnonneg _ (Ioo_subset_Icc_self hh)) hh.1.le
  have hne : (Ioo 0 R).Nonempty := nonempty_Ioo.mpr hR
  refine ⟨_, le_csInf (hne.image _) hl, ?_⟩
  simpa only [slope_fun_def_field, hzero, sub_zero] using
    hm.tendsto_nhdsWithin_Ioo_right hne ⟨0, hl⟩

/-- Dilating the configuration by a positive factor multiplies its tangent
price by the same factor. -/
theorem tangentPrice_rescale {f : ℝ → ℝ} {D t : ℝ}
    (hf : Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 D)) (ht : 0 < t) :
    Tendsto (fun h ↦ f (t * h) / h) (𝓝[>] 0) (𝓝 (t * D)) := by
  have hscale : Tendsto (fun h ↦ t * h) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_iff_comap.mpr (comap_mulLeft_nhdsGT_zero ht).ge
  apply ((hf.comp hscale).const_mul t).congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  dsimp
  field_simp

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.PatchPrice
section

/-! # Prices on a Euclidean patch and their infinitesimal limits

The synchronized convexity inequality can be used within a bounded patch.
At an interior point every fixed finite configuration lies in the patch
after a sufficiently small dilation.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter Set
open scoped Classical Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint convexity of placed prices when all the endpoints belong to a patch. -/
def JointlyConvexPriceOn (C : Set E) (δ : Finset E → ℝ) : Prop :=
  ∀ (P : Finset (E × E)), P.Nonempty → (∀ p ∈ P, p.1 ∈ C ∧ p.2 ∈ C) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      δ (P.image fun p ↦ a • p.1 + b • p.2) ≤
        a * δ (P.image Prod.fst) + b * δ (P.image Prod.snd)

/-- All rescaled finite prices at the same point have the specified limits. -/
def IsTangentPriceAt (δ : Finset E → ℝ) (y : E) (D : Finset E → ℝ) : Prop :=
  ∀ S : Finset E, S.Nonempty → Tendsto (fun h : ℝ ↦ δ (S.image (fun w ↦ y + h • w)) / h)
    (𝓝[>] 0) (𝓝 (D S))

theorem eventually_patch_image_subset {C : Set E} {y : E} (hy : y ∈ interior C) (S : Finset E) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (S.image (fun w ↦ y + h • w) : Set E) ⊆ C := by
  have hx (x : E) : Tendsto (fun h : ℝ ↦ y + h • x) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have hc : Continuous (fun h : ℝ ↦ y + h • x) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  filter_upwards [(eventually_all_finset S).mpr fun x _ ↦ (hx x) (mem_interior_iff_mem_nhds.mp hy)]
    with h hh
  intro z hz
  obtain ⟨x, hx', rfl⟩ := Finset.mem_image.mp hz
  exact hh x hx'

/-- Synchronized interpolation specializes to convexity in the dilation parameter
on any interval for which the dilated sites stay in the patch. -/
theorem JointlyConvexPriceOn.convexOn_dilation {C : Set E} {δ : Finset E → ℝ}
    (hc : JointlyConvexPriceOn C δ) (S : Finset E) (hS : S.Nonempty) (y : E) {I : Set ℝ}
    (hI : Convex ℝ I) (hloc : ∀ t ∈ I, ∀ x ∈ S, y + t • x ∈ C) :
    ConvexOn ℝ I (fun t ↦ δ (S.image (fun x ↦ y + t • x))) := by
  refine ⟨hI, ?_⟩
  intro t ht s hs a b ha hb hab
  let P := S.image (fun x ↦ (y + t • x, y + s • x))
  have hP : ∀ p ∈ P, p.1 ∈ C ∧ p.2 ∈ C := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hloc t ht x hx, hloc s hs x hx⟩
  have h := hc P (hS.image _) hP a b ha hb hab
  have haff (x : E) : a • (y + t • x) + b • (y + s • x) = y + (a * t + b * s) • x := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul,
      hab, one_smul, add_smul]
  simpa only [P, Finset.image_image, Function.comp_def, haff, smul_eq_mul] using h

/-- The tangent price exists simultaneously on all finite configurations at an
interior point. Nonnegativity bounds the convex secant slopes from below. -/
theorem exists_tangentPriceAt {C : Set E} {δ : Finset E → ℝ} (hc : JointlyConvexPriceOn C δ)
    {y : E} (hy : y ∈ interior C) (hy0 : δ {y} = 0)
    (hnonneg : ∀ (S : Finset E), S.Nonempty → (S : Set E) ⊆ C → 0 ≤ δ S) :
    ∃ D : Finset E → ℝ, IsTangentPriceAt δ y D := by
  have hex (S : Finset E) (hS : S.Nonempty) :
      ∃ l : ℝ, 0 ≤ l ∧ Tendsto (fun h : ℝ ↦ δ (S.image (fun w ↦ y + h • w)) / h)
        (𝓝[>] 0) (𝓝 l) := by
    obtain ⟨R, hR, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (eventually_patch_image_subset hy S)
    have hI (t : ℝ) (ht : t ∈ Icc 0 R) : (S.image (fun x ↦ y + t • x) : Set E) ⊆ C := by
      rcases ht.1.eq_or_lt with h | h
      · subst t
        simpa [Finset.image_const hS] using interior_subset hy
      · exact hsub ⟨h, ht.2⟩
    apply exists_tangentPrice hR (hc.convexOn_dilation S hS y (convex_Icc _ _)
      (fun t ht x hx ↦ hI t ht (Finset.mem_image_of_mem _ hx)))
    · simpa [Finset.image_const hS] using hy0
    · exact fun t ht ↦ hnonneg _ (hS.image _) (hI t ht)
  refine ⟨fun S ↦ if hS : S.Nonempty then (hex S hS).choose else 0, ?_⟩
  intro S hS
  simpa [hS] using (hex S hS).choose_spec.2

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.Increment
section

/-!
# Intersecting submodularity of diagonal prices

The proof of Lemma `lem:submod` in the manuscript uses two integer weight
specializations to obtain a one-site inequality. We verify the weights on
their specified supports and the telescoping argument for finite sets.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset

section Increments

variable {α : Type*} [DecidableEq α] (δ : Finset α → ℝ)

/-- The one-site inequality (equation `eq:width-increment`). -/
def DiminishingIncrements : Prop :=
  ∀ ⦃I A : Finset α⦄ ⦃z : α⦄, I.Nonempty → I ⊆ A → z ∉ A →
    δ (insert z A) - δ A ≤ δ (insert z I) - δ I

/-- The price inequality for finite sets with nonempty intersection. -/
def IntersectingSubmodular : Prop :=
  ∀ ⦃A B : Finset α⦄, (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B

variable {δ}

/-- Adjoin a finite family of new sites successively to both sets. -/
theorem diminishingIncrements_union (h : DiminishingIncrements δ)
    {I A : Finset α} (hne : I.Nonempty) (hIA : I ⊆ A)
    (S : Finset α) (hdis : Disjoint S A) :
    δ (A ∪ S) - δ A ≤ δ (I ∪ S) - δ I := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert z S hz ih =>
    obtain ⟨hzA, hSA⟩ := Finset.disjoint_insert_left.mp hdis
    have step := h (I := I ∪ S) (A := A ∪ S) (z := z) (hne.mono (Finset.subset_union_left (s₂ := S)))
      (Finset.union_subset_union hIA (Finset.Subset.refl S))
      (by simpa only [Finset.mem_union, not_or] using And.intro hzA hz)
    rw [Finset.union_insert, Finset.union_insert]
    linarith [ih hSA]

/-- Intersecting submodularity is equivalent to the one-site increment inequality. -/
theorem intersectingSubmodular_iff_diminishingIncrements :
    IntersectingSubmodular δ ↔ DiminishingIncrements δ := by
  constructor
  · intro h I A z hI hIA hz
    have hinter : A ∩ insert z I = I := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      grind
    have hunion : A ∪ insert z I = insert z A := by
      rw [Finset.union_insert, Finset.union_eq_left.mpr hIA]
    have h' := h (A := A) (B := insert z I) (by simpa only [hinter] using hI)
    rw [hinter, hunion] at h'
    linarith
  · intro h A B hAB
    have h' := diminishingIncrements_union h hAB Finset.inter_subset_left
      (B \ A) Finset.sdiff_disjoint
    have heq : (A ∩ B) ∪ (B \ A) = B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      grind
    rw [heq, Finset.union_sdiff_self_eq_union] at h'
    linarith

end Increments

section IntegerWeights

variable {ι : Type*} [Fintype ι]

/-- On the support selected by coefficient extraction, the first local
weights sum to `(g - h)²`. Here `ι` indexes the sites other than site 1. -/
theorem firstWeight_eq_sq (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = (g - h) ^ 2 := by
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hs]
  ring

/-- The first specialization retains precisely `g = h`. -/
theorem firstWeight_eq_zero_iff (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = 0 ↔ g = h := by
  rw [firstWeight_eq_sq g h v₁ v hs]
  simp [sub_eq_zero]

/-- On the remaining support, the second local weights also sum to a
sum of squares in the integers. -/
theorem secondWeight_eq_sum_sq (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = ∑ j, (v j - v₁) ^ 2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_right_comm (2 : ℤ) _ v₁]
  rw [← Finset.mul_sum, hs]
  simp
  ring

/-- The second specialization retains precisely the common choices of all labels. -/
theorem secondWeight_eq_zero_iff (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = 0 ↔ ∀ j, v j = v₁ := by
  rw [secondWeight_eq_sum_sq v₁ v hs, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp [sub_eq_zero]

end IntegerWeights

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.EuclideanPrice
section

/-! # Diagonal price inequalities on an embedded Euclidean patch

These properties are the inputs to the geometric part of the flat
diagonal law. Joint convexity and the metric bounds are only needed within
the embedded patch. Monotonicity and intersecting submodularity are properties
of the price on finite collections of sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure DiagonalPriceLawsOn (C : Set E) (δ : Finset E → ℝ) : Prop where
  monotone : Monotone δ
  submodular : IntersectingSubmodular δ
  jointlyConvex : JointlyConvexPriceOn C δ
  wire : ∀ a ∈ C, ∀ b ∈ C, δ {a, b} = dist a b
  triangle_le : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, δ {a, b, c} ≤
    (dist a b + dist b c + dist c a) / 2

namespace DiagonalPriceLawsOn

variable {C : Set E} {δ : Finset E → ℝ} (H : DiagonalPriceLawsOn C δ)

include H

theorem mono_patch {C' : Set E} (h : C' ⊆ C) : DiagonalPriceLawsOn C' δ where
  monotone := H.monotone
  submodular := H.submodular
  jointlyConvex P hP hPC := H.jointlyConvex P hP fun p hp ↦ ⟨h (hPC p hp).1, h (hPC p hp).2⟩
  wire a ha b hb := H.wire a (h ha) b (h hb)
  triangle_le a ha b hb c hc := H.triangle_le a (h ha) b (h hb) c (h hc)

theorem singleton {a : E} (ha : a ∈ C) : δ {a} = 0 := by
  simpa using H.wire a ha a ha

theorem pair {a b : E} (ha : a ∈ C) (hb : b ∈ C) : δ {a,b} = dist a b := by
  exact H.wire a ha b hb

theorem nonneg (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C) : 0 ≤ δ S := by
  obtain ⟨x, hx⟩ := hS
  exact (H.singleton (hSC hx)).symm.le.trans (H.monotone (Finset.singleton_subset_iff.mpr hx))

end DiagonalPriceLawsOn

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.PatchPullback
section

/-! # Restricting finite prices to an affine subspace -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped Classical

/-- Intersecting submodularity pulls back along an injection of sites. -/
theorem IntersectingSubmodular.pullback {E F : Type*} [DecidableEq E] [DecidableEq F]
    {δ : Finset F → ℝ} (h : IntersectingSubmodular δ) (f : E → F) (hf : Function.Injective f) :
    IntersectingSubmodular (fun S ↦ δ (S.image f)) := by
  intro A B hI
  simpa only [Finset.image_union, Finset.image_inter A B hf] using
    h (A := A.image f) (B := B.image f) (Finset.image_inter A B hf ▸ hI.image f)

/-- Monotonicity of prices is preserved under a relabeling or an identification of sites. -/
theorem monotone_price_image {E F : Type*} [DecidableEq F] {δ : Finset F → ℝ}
    (h : Monotone δ) (f : E → F) : Monotone (fun S : Finset E ↦ δ (S.image f)) :=
  fun _ _ hST ↦ h (Finset.image_subset_image hST)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint convexity pulls back by any affine map carrying the source patch into
the target patch. In particular this applies to an affine isometry onto the
affine span of a finite configuration. -/
theorem JointlyConvexPriceOn.pullback {C : Set E} {C' : Set F} {δ : Finset F → ℝ}
    (hj : JointlyConvexPriceOn C' δ) (f : E →ᵃ[ℝ] F) (hf : Set.MapsTo f C C') :
    JointlyConvexPriceOn C (fun S ↦ δ (S.image f)) := by
  intro P hP hPC a b ha hb hab
  let pair := fun p : E × E ↦ (f p.1, f p.2)
  have hmap : ∀ p ∈ P.image pair, p.1 ∈ C' ∧ p.2 ∈ C' := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hf (hPC q hq).1, hf (hPC q hq).2⟩
  have h := hj (P.image pair) (hP.image _) hmap a b ha hb hab
  have hcomb (p : E × E) : f (a • p.1 + b • p.2) = a • f p.1 + b • f p.2 := by
    rw [show a = 1-b by linarith, ← AffineMap.lineMap_apply_module, ← AffineMap.lineMap_apply_module]
    exact f.apply_lineMap _ _ _
  simpa only [pair, Finset.image_image, Function.comp_def, hcomb] using h

/-- Restrict all the diagonal price laws along an affine isometric embedding. -/
theorem DiagonalPriceLawsOn.comp_affineIsometry {C : Set F} {δ : Finset F → ℝ}
    (H : DiagonalPriceLawsOn C δ) (f : E →ᵃⁱ[ℝ] F) :
    DiagonalPriceLawsOn (f ⁻¹' C) (fun S ↦ δ (S.image f)) where
  monotone := monotone_price_image H.monotone f
  submodular := H.submodular.pullback f f.injective
  jointlyConvex := H.jointlyConvex.pullback f.toAffineMap (fun _ hx ↦ hx)
  wire a ha b hb := by simpa using H.wire (f a) ha (f b) hb
  triangle_le := by
    intro a ha b hb c hc
    simpa using H.triangle_le (f a) ha (f b) hb (f c) hc

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.ConvexPatch
section

/-! # Recovering a convex dilation profile from its one-sided slopes -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set Filter
open scoped Topology

private theorem convexPatch_tendsto_increment {f : ℝ → ℝ} {t : ℝ}
    (hconv : ConvexOn ℝ (Icc 0 1) f) (ht : t ∈ Ioo 0 1) :
    Tendsto (fun h ↦ (f (t + h) - f t) / h) (𝓝[>] 0) (𝓝 (derivWithin f (Ioi t) t)) := by
  have hti : t ∈ interior (Icc (0 : ℝ) 1) := by simpa only [interior_Icc] using ht
  have hd := hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hti
  have hshift : Tendsto (fun h : ℝ ↦ t + h) (𝓝[>] 0) (𝓝[>] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := t)).add
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      exact lt_add_of_pos_right t hh
  simpa only [Function.comp_def, slope_def_field, add_sub_cancel_left] using
    ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hd).comp hshift

/-- The last real-variable step of the flat diagonal law. Here `f t` is the price
of the configuration dilated by `t` and `W` is its normalized mean width. -/
theorem convexPatch_price_eq_of_increment_limsup {f : ℝ → ℝ} {W : ℝ}
    (hconv : ConvexOn ℝ (Icc 0 1) f) (hcont : ContinuousOn f (Icc 0 1)) (hzero : f 0 = 0)
    (htangent : Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 W))
    (hinc : ∀ t ∈ Ioo 0 1,
      limsup (fun h ↦ (f (t + h) - f t) / h) (𝓝[>] 0) ≤ W) :
    f 1 = W := by
  have hderiv₀ : HasDerivWithinAt f W (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).2
    change Tendsto (fun h ↦ slope f 0 h) _ _
    simpa only [slope_def_field, hzero, sub_zero] using htangent
  have hline : EqOn f (fun t ↦ W * t) (Ioo 0 1) := by
    intro t ht
    have hti : t ∈ interior (Icc (0 : ℝ) 1) := by simpa only [interior_Icc] using ht
    have hlim := convexPatch_tendsto_increment hconv ht
    have hupper := hinc t ht
    rw [hlim.limsup_eq] at hupper
    have h₀ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have hlo := hconv.le_slope_of_hasDerivWithinAt_Ioi h₀ (interior_subset hti) ht.1 hderiv₀
    have hhi := (hconv.slope_le_leftDeriv_of_mem_interior h₀ hti ht.1).trans
      ((hconv.leftDeriv_le_rightDeriv_of_mem_interior hti).trans hupper)
    have heq := le_antisymm hhi hlo
    simp only [slope_def_field, hzero, sub_zero] at heq
    exact (div_eq_iff ht.1.ne').mp heq
  have hclosed := hline.of_subset_closure hcont (continuous_const.mul continuous_id).continuousOn
    Ioo_subset_Icc_self (by rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)])
  simpa using hclosed (right_mem_Icc.mpr zero_le_one)

/-- Version of the convex patch argument using an eventual epsilon bound for
each interior difference quotient. -/
theorem convexPatch_price_eq_of_eventually_increment_le {f : ℝ → ℝ} {W : ℝ}
    (hconv : ConvexOn ℝ (Icc 0 1) f) (hcont : ContinuousOn f (Icc 0 1)) (hzero : f 0 = 0)
    (htangent : Tendsto (fun h ↦ f h / h) (𝓝[>] 0) (𝓝 W))
    (hinc : ∀ t ∈ Ioo 0 1, ∀ ε > 0,
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (f (t + h) - f t) / h ≤ W + ε) :
    f 1 = W := by
  apply convexPatch_price_eq_of_increment_limsup hconv hcont hzero htangent
  intro t ht
  have hlim := convexPatch_tendsto_increment hconv ht
  rw [hlim.limsup_eq]
  exact le_of_forall_pos_le_add fun ε hε ↦ le_of_tendsto hlim (hinc t ht ε hε)

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.PatchIncrement
section

/-! # Bounding the price of an insertion by its price on an inner patch -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical

/-- Monotonicity extends the one-site inequality to insertions already present in the
larger configuration. -/
theorem price_increment_le_of_subset {α : Type*} (δ : Finset α → ℝ)
    (hmono : ∀ ⦃S T : Finset α⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ) {I A : Finset α}
    (hI : I.Nonempty) (hIA : I ⊆ A) (z : α) :
    δ (insert z A) - δ A ≤ δ (insert z I) - δ I := by
  by_cases hz : z ∈ A
  · rw [Finset.insert_eq_of_mem hz, sub_self, sub_nonneg]
    exact hmono hI (Finset.subset_insert z I)
  · exact intersectingSubmodular_iff_diminishingIncrements.mp hsub hI hIA hz

/-- If every point of the patch lies in the convex hull of the configuration,
its insertion cost bounds the insertion cost for the whole configuration. -/
theorem price_increment_le_of_hull_patch {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    {S P : Finset E}
    (hhull : ∀ T : Finset E, (T : Set E) ⊆ convexHull ℝ (S : Set E) → δ (S ∪ T) = δ S)
    (hP : P.Nonempty)
    (hPS : (P : Set E) ⊆ convexHull ℝ (S : Set E)) (z : E) :
    δ (insert z S) - δ S ≤ δ (insert z P) - δ P := by
  have h := price_increment_le_of_subset δ hmono hsub hP (Finset.subset_union_right (s₁ := S)) z
  rw [hhull P hPS] at h
  exact (sub_le_sub_right (hmono (Finset.insert_nonempty z S)
    (Finset.insert_subset_insert z Finset.subset_union_left)) _).trans h

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.GaussianTies
section

/-! # Uniqueness of projections of a finite set in a Gaussian direction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A tie between two distinct points has Gaussian measure zero, since their
difference gives a one-dimensional projection of positive variance. -/
theorem measure_projection_tie_eq_zero {x y : E} (hxy : x ≠ y) :
    stdGaussian E {u : E | ⟪u, x⟫ = ⟪u, y⟫} = 0 := by
  let L : StrongDual ℝ E := innerSL ℝ (x - y)
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have : NullSingletonClass ((stdGaussian E).map L) := by
    rw [IsGaussian.map_eq_gaussianReal]
    apply nullSingletonClass_gaussianReal
    rw [variance_dual_stdGaussian, ne_eq, Real.toNNReal_eq_zero, not_le]
    simpa only [L, innerSL_apply_norm] using sq_pos_of_pos hnorm
  have hzero := measure_singleton (μ := (stdGaussian E).map L) (0 : ℝ)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton _)] at hzero
  convert hzero using 2
  ext u
  change ⟪u, x⟫ = ⟪u, y⟫ ↔ ⟪x - y, u⟫ = 0
  rw [real_inner_comm u (x - y), inner_sub_right, sub_eq_zero]

/-- Almost every Gaussian direction separates every pair in a finite point set. -/
theorem ae_no_ties (S : Finset E) :
    ∀ᵐ u ∂stdGaussian E, ∀ x ∈ S, ∀ y ∈ S, ⟪u, x⟫ = ⟪u, y⟫ → x = y := by
  apply (ae_ball_iff S.countable_toSet).2
  intro x _
  apply (ae_ball_iff S.countable_toSet).2
  intro y _
  by_cases hxy : x = y
  · exact Filter.Eventually.of_forall fun _ _ ↦ hxy
  have h : ∀ᵐ u ∂stdGaussian E, ⟪u, x⟫ ≠ ⟪u, y⟫ := by
    simpa only [ae_iff, not_not] using measure_projection_tie_eq_zero hxy
  filter_upwards [h] with u hu heq using False.elim (hu heq)

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.WidthPartition
section

/-! # Splitting mean width over the maximizing sites

The normal cones cover all directions and have Gaussian-null pairwise overlaps.
This yields the sum of the marginal integrals at the end of the flat diagonal law.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translate the sites so that the specified vertex is the origin. -/
def centeredSites (S : Finset E) (v : E) : Finset E := S.image (· - v)

theorem mem_normalConeAtZero_centeredSites (S : Finset E) (v u : E) :
    u ∈ normalConeAtZero (centeredSites S v) ↔ ∀ w ∈ S, ⟪u, w⟫ ≤ ⟪u, v⟫ := by
  simp [normalConeAtZero, centeredSites, inner_sub_right]

theorem sum_normalCone_indicators {S : Finset E} (h0 : 0 ∈ S) (u : E)
    (htie : ∀ x ∈ S, ∀ y ∈ S, ⟪u, x⟫ = ⟪u, y⟫ → x = y) :
    ∑ v ∈ S, (normalConeAtZero (centeredSites S v)).indicator (fun g ↦ max ⟪g, v⟫ 0) u =
      support S ⟨0, h0⟩ u := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup' (s := S) ⟨0, h0⟩ (fun x ↦ ⟪u, x⟫)
  change support S ⟨0, h0⟩ u = ⟪u, v⟫ at hmax
  have hu : ∀ w ∈ S, ⟪u, w⟫ ≤ ⟪u, v⟫ := fun w hw ↦
    (S.le_sup' (fun x ↦ ⟪u, x⟫) hw).trans_eq hmax
  rw [Finset.sum_eq_single_of_mem v hv]
  · rw [Set.indicator_of_mem ((mem_normalConeAtZero_centeredSites S v u).mpr hu)]
    exact (max_eq_left ((support_nonneg_of_zero_mem h0 u).trans_eq hmax)).trans hmax.symm
  · intro w hw hne
    apply Set.indicator_of_notMem
    intro h
    have hle := (mem_normalConeAtZero_centeredSites S w u).mp h v hv
    exact hne (htie w hw v hv (le_antisymm (hu w hw) hle))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Summing over all original sites gives the width exactly when the origin is
among the sites. The Gaussian hyperplanes on which the maximizer ties are null. -/
theorem sum_normalCone_marginals {S : Finset E} (h0 : 0 ∈ S) :
    ∑ v ∈ S, Real.sqrt (2 * Real.pi) *
      ∫ u in normalConeAtZero (centeredSites S v), max ⟪u, v⟫ 0 ∂stdGaussian E =
      meanWidth S ⟨0, h0⟩ := by
  rw [← Finset.mul_sum]
  unfold meanWidth
  congr 1
  simp_rw [← integral_indicator (measurableSet_normalConeAtZero _)]
  rw [← integral_finsetSum]
  · exact integral_congr_ae ((ae_no_ties S).mono fun u hu ↦ sum_normalCone_indicators h0 u hu)
  · intro v _
    exact ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const (𝕜 := ℝ) v |>.sup
      (integrable_const 0)).indicator (measurableSet_normalConeAtZero _)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.LocalPatch
section

/-!
# Local comparison at a site of a convex Euclidean patch

To estimate the increment when a new site separates from an old one, shrink
the configuration about the old site. The contracted points lie in its convex
hull. On dividing by the step size, the prices of the contracted configurations
converge to the tangent mean widths. Taking the dilation to infinity isolates
the directions that support the original site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Normalized prices of translated and contracted finite configurations have
the specified Gaussian mean width as their tangent price at `y`. -/
def HasTangentMeanWidth (δ : Finset E → ℝ) (y : E) : Prop :=
  ∀ (U : Finset E) (hU : U.Nonempty),
    Tendsto (fun h : ℝ ↦ δ (U.image (fun w ↦ y + h • w)) / h)
      (𝓝[>] 0) (𝓝 (meanWidth U hU))

variable (δ : Finset E → ℝ)
  (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
  (hsub : IntersectingSubmodular δ)
  {S : Finset E}
  (hhull : ∀ T : Finset E, (T : Set E) ⊆ convexHull ℝ (S : Set E) →
    δ (S ∪ T) = δ S)

include hmono hsub hhull

omit [BorelSpace E] in
/-- At a fixed dilation `M`, the price increment at a site is bounded to
first order by the width increment of the centered dilate. -/
theorem eventually_price_increment_div_le_dilated {y : E} (hy : y ∈ S) (v : E)
    (htangent : HasTangentMeanWidth δ y) {M : ℝ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    let U := (centeredSites S y).image (M • ·)
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (δ (insert (y + h • v) S) - δ S) / h ≤
      meanWidth (insert v U) (Finset.insert_nonempty _ _) -
      meanWidth U ((Finset.Nonempty.image (⟨y, hy⟩ : S.Nonempty) _).image _) + ε := by
  let U := (centeredSites S y).image (M • ·)
  have hU : U.Nonempty := (Finset.Nonempty.image (⟨y, hy⟩ : S.Nonempty) _).image _
  have hlim := (htangent (insert v U) (Finset.insert_nonempty _ _)).sub (htangent U hU)
  have happ := hlim.eventually_lt_const (lt_add_of_pos_right _ hε)
  filter_upwards [Ioo_mem_nhdsGT (one_div_pos.mpr hM), happ] with h hh hbound
  let P := U.image (fun w ↦ y + h • w)
  have hPS : (P : Set E) ⊆ convexHull ℝ (S : Set E) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    rw [smul_smul]
    apply segment_subset_convexHull (s := (S : Set E)) hy ha
    rw [segment_eq_image']
    exact Set.mem_image_of_mem _ ⟨mul_nonneg hh.1.le hM.le, ((lt_div_iff₀ hM).mp hh.2).le⟩
  have hinc := price_increment_le_of_hull_patch δ hmono hsub hhull (hU.image _) hPS
    (y + h • v)
  simp only [Finset.image_insert, ← sub_div] at hbound
  exact (div_le_div_of_nonneg_right hinc hh.1.le).trans hbound.le

/-- Upper right marginal price at a site in terms of the positive part of the
motion projected onto directions supporting that site. -/
theorem eventually_price_increment_div_le_normalCone {y : E} (hy : y ∈ S)
    (v : E) (htangent : HasTangentMeanWidth δ y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), (δ (insert (y + h • v) S) - δ S) / h ≤
      Real.sqrt (2 * Real.pi) *
        (∫ u in normalConeAtZero (centeredSites S y), max ⟪u, v⟫ 0 ∂stdGaussian E) + ε := by
  have h0 : 0 ∈ centeredSites S y := Finset.mem_image.mpr ⟨y, hy, sub_self y⟩
  have hlim := tendsto_meanWidth_insert_smul_sub h0 v
  have happ := hlim.eventually_lt_const (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨M, hM, hnear⟩ := ((eventually_gt_atTop (0 : ℝ)).and happ).exists
  filter_upwards [eventually_price_increment_div_le_dilated δ hmono hsub hhull hy v htangent
    hM (half_pos hε)] with h hbound
  linarith

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.SpineConditioning
section

/-!
# Conditioning a finite family of tips on a spine

These are the finite, deterministic inequalities used before taking
expectations in the proof of Theorem `thm:student`. Tips may coincide with each other or
with points of the spine.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {α ι : Type*} [DecidableEq α] {δ : Finset α → ℝ}

/-- The price of adding all the tips to the spine is bounded by the
sum of their individual increments at the spine. -/
theorem conditioning_union_image_le_of_nonempty
    (hmono : ∀ ⦃S T : Finset α⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (B ∪ s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.image_insert, Finset.union_insert, Finset.sum_insert hi]
    by_cases hx : tip i ∈ B ∪ s.image tip
    · rw [Finset.insert_eq_of_mem hx]
      have hinc : δ B ≤ δ (insert (tip i) B) := hmono hB (Finset.subset_insert _ _)
      linarith
    · have hinc := intersectingSubmodular_iff_diminishingIncrements.mp hsub
          (I := B) (A := B ∪ s.image tip) hB Finset.subset_union_left hx
      linarith

/-- Conditioning with monotonicity on all finite sets. -/
theorem conditioning_union_image_le (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (B ∪ s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) :=
  conditioning_union_image_le_of_nonempty (fun _ _ _ h => hmono h) hsub hB s tip

/-- The conditioning bound for the tips alone, including repeated tips. -/
theorem conditioning_image_le (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) :=
  (hmono Finset.subset_union_right).trans (conditioning_union_image_le hmono hsub hB s tip)

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.FlatPatch
section

/-! # Passing from interior tangent prices to the price of a Euclidean patch

At a positive dilation, the marginal bound at each occupied site involves its
normal cone. These cones partition the Gaussian directions up to null sets.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Dilation about the origin preserves the normal cone at the corresponding site. -/
theorem normalConeAtZero_centeredSites_smul (S : Finset E) (v : E) {t : ℝ} (ht : 0 < t) :
    normalConeAtZero (centeredSites (S.image (t • ·)) (t • v)) =
      normalConeAtZero (centeredSites S v) := by
  ext u
  simp [mem_normalConeAtZero_centeredSites, real_inner_smul_right, ht]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def marginal (S : Finset E) (v : E) : ℝ :=
  Real.sqrt (2 * Real.pi) * ∫ u in normalConeAtZero (centeredSites S v),
    max ⟪u, v⟫ 0 ∂stdGaussian E

/-- The collective dilation increment is at most the sum of the individual
normal-cone marginals, even when several of the new sites coincide. -/
private theorem eventually_dilation_increment_div_le
    (δ : Finset E → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    {S : Finset E} (h0 : 0 ∈ S) (t : ℝ)
    (hlocal : ∀ v ∈ S, ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (δ (insert (t • v + h • v) (S.image (t • ·))) - δ (S.image (t • ·))) / h ≤
        marginal S v + ε) :
    ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (δ (S.image ((t + h) • ·)) - δ (S.image (t • ·))) / h ≤ meanWidth S ⟨0, h0⟩ + ε := by
  intro ε hε
  have hS : S.Nonempty := ⟨0, h0⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  filter_upwards [self_mem_nhdsWithin, (eventually_all_finset S).mpr
    (fun v hv ↦ hlocal v hv (ε / S.card) (div_pos hε hcard))]
    with h (hh : 0 < h) hbound
  have hc := conditioning_image_le hmono hsub (hS.image (t • ·)) S ((t + h) • ·)
  calc
    _ ≤ (∑ v ∈ S, (δ (insert ((t + h) • v) (S.image (t • ·))) - δ (S.image (t • ·)))) / h :=
      div_le_div_of_nonneg_right (by linarith only [hc]) hh.le
    _ = ∑ v ∈ S, (δ (insert (t • v + h • v) (S.image (t • ·))) -
        δ (S.image (t • ·))) / h := by rw [Finset.sum_div]; simp_rw [add_smul]
    _ ≤ ∑ v ∈ S, (marginal S v + ε / S.card) := Finset.sum_le_sum hbound
    _ = meanWidth S ⟨0, h0⟩ + ε := by
      rw [Finset.sum_add_distrib, show ∑ v ∈ S, marginal S v = meanWidth S ⟨0, h0⟩ from
        sum_normalCone_marginals h0, Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- The patch reduction of the flat diagonal law. Translate a relative interior
site to the origin and include it in `S`. The tangent hypothesis is used only at
strictly interior dilations of its vertices. The hull condition concerns the
dilated configurations inside the given patch. -/
theorem flatDiagonalLaw_of_tangentMeanWidth
    (δ : Finset E → ℝ) (hmono : Monotone δ) (hsub : IntersectingSubmodular δ)
    {S : Finset E} (h0 : 0 ∈ S) (hzero : δ {0} = 0)
    (hhull : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ T : Finset E,
      (T : Set E) ⊆ convexHull ℝ (S.image (t • ·) : Set E) →
      δ (S.image (t • ·) ∪ T) = δ (S.image (t • ·)))
    (hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t ↦ δ (S.image (t • ·))))
    (hcont : ContinuousOn (fun t : ℝ ↦ δ (S.image (t • ·))) (Icc 0 1))
    (htan : ∀ t ∈ Ico (0 : ℝ) 1, ∀ v ∈ S, HasTangentMeanWidth δ (t • v)) :
    δ S = meanWidth S ⟨0, h0⟩ := by
  have hS : S.Nonempty := ⟨0, h0⟩
  have htan₀ : HasTangentMeanWidth δ 0 := by simpa using htan 0 ⟨le_rfl, zero_lt_one⟩ 0 h0
  have h := convexPatch_price_eq_of_eventually_increment_le hconv hcont
    (by simpa [Finset.image_const hS] using hzero) (by simpa using htan₀ S hS) ?_
  · simpa using h
  · intro t ht
    apply eventually_dilation_increment_div_le δ hmono hsub h0 t
    intro v hv ε hε
    have hy := Finset.mem_image_of_mem (t • ·) hv
    have hlocal := eventually_price_increment_div_le_normalCone δ
      (fun _ _ _ h ↦ hmono h) hsub (hhull t ht) hy v
      (htan t ⟨ht.1.le, ht.2⟩ v hv) hε
    simpa only [marginal, normalConeAtZero_centeredSites_smul S v ht.1] using hlocal

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.MinkowskiSupport
section

/-! # Support functions of Minkowski sums and continuity of Gaussian mean width -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Metric Filter
open scoped RealInnerProductSpace Pointwise Classical

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Support functions add under Minkowski addition of finite configurations. -/
theorem support_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) (u : E) :
    support (S + T) (hS.add hT) u = support S hS u + support T hT u := by
  unfold support
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    rw [inner_add_right]
    exact add_le_add (S.le_sup' (fun v ↦ ⟪u, v⟫) hx) (T.le_sup' (fun v ↦ ⟪u, v⟫) hy)
  · obtain ⟨x, hx, ex⟩ := Finset.exists_mem_eq_sup' hS (fun v ↦ ⟪u, v⟫)
    obtain ⟨y, hy, ey⟩ := Finset.exists_mem_eq_sup' hT (fun v ↦ ⟪u, v⟫)
    rw [ex, ey, ← inner_add_right]
    exact (S + T).le_sup' (fun v ↦ ⟪u, v⟫) (Finset.add_mem_add hx hy)

/-- Support function restricted to the unit sphere, with its uniform topology. -/
def sphereSupport (S : Finset E) (hS : S.Nonempty) : C(sphere (0 : E) 1, ℝ) where
  toFun u := support S hS u
  continuous_toFun := Continuous.finset_sup'_apply hS (fun _ _ ↦
    continuous_subtype_val.inner continuous_const)

/-- The continuous functions generating the triangle approximation space. -/
def triangleSupports (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set C(sphere (0 : E) 1, ℝ) :=
  {f | ∃ a b c : E, f = sphereSupport {a, b, c} (Finset.insert_nonempty _ _)}

theorem sphereSupport_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    sphereSupport (S + T) (hS.add hT) = sphereSupport S hS + sphereSupport T hT := by
  ext u
  exact support_add S T hS hT u

theorem sphereSupport_zero : sphereSupport ({0} : Finset E) (Finset.singleton_nonempty _) = 0 := by
  ext u
  simp [sphereSupport, support]

theorem support_smul_direction (S : Finset E) (hS : S.Nonempty) (u : E) {a : ℝ} (ha : 0 ≤ a) :
    support S hS (a • u) = a * support S hS u := by
  unfold support
  simpa only [real_inner_smul_left, Function.comp_def] using
    (Finset.apply_sup'_eq_sup'_comp hS (a * ·)
      (fun b c ↦ mul_max_of_nonneg b c ha) (f := fun x ↦ ⟪u, x⟫)).symm

/-- Adjoining sites in the convex hull preserves the support function. -/
theorem support_union_of_subset_convexHull {S T : Finset E} (hS : S.Nonempty)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) (u : E) :
    support (S ∪ T) (hS.mono Finset.subset_union_left) u = support S hS u := by
  have hc : Convex ℝ {v : E | ⟪u, v⟫ ≤ support S hS u} :=
    convex_halfSpace_le (innerSL ℝ u).toLinearMap.isLinear _
  have hbound : (S : Set E) ⊆ {v : E | ⟪u, v⟫ ≤ support S hS u} :=
    fun _ hx ↦ Finset.le_sup' (fun w : E ↦ ⟪u, w⟫) hx
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hbound h
    · exact convexHull_min hbound hc (hT h)
  · apply Finset.sup'_le
    intro x hx
    exact Finset.le_sup' _ (Finset.mem_union_left T hx)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Adjoining finitely many points in the convex hull preserves mean width. -/
theorem meanWidth_union_of_subset_convexHull {S T : Finset E} (hS : S.Nonempty)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) :
    meanWidth (S ∪ T) (hS.mono Finset.subset_union_left) = meanWidth S hS := by
  simp only [meanWidth, funext (support_union_of_subset_convexHull hS hT)]

theorem meanWidth_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    meanWidth (S + T) (hS.add hT) = meanWidth S hS + meanWidth T hT := by
  simp only [meanWidth, support_add S T hS hT, integral_add (integrable_support S hS) (integrable_support T hT),
    mul_add]

/-- Uniform error on unit directions bounds the error in Gaussian mean width. -/
theorem abs_meanWidth_sub_le (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) {ε : ℝ}
    (hclose : ∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) :
    |meanWidth S hS - meanWidth T hT| ≤
      (Real.sqrt (2 * Real.pi) * ∫ u : E, ‖u‖ ∂stdGaussian E) * ε := by
  have pointwise (u : E) : |support S hS u - support T hT u| ≤ ε * ‖u‖ := by
    by_cases hu : u = 0
    · simp [hu, support]
    let w := NormedSpace.normalize u
    have hw : w ∈ sphere (0 : E) 1 := by simp [w, NormedSpace.norm_normalize hu]
    have heq : ‖u‖ • w = u := NormedSpace.norm_smul_normalize u
    calc
      _ = ‖u‖ * |support S hS w - support T hT w| := by
        conv_lhs => rw [← heq]
        rw [support_smul_direction _ _ _ (norm_nonneg u), support_smul_direction _ _ _ (norm_nonneg u),
          ← mul_sub, abs_mul, abs_norm]
      _ ≤ ε * ‖u‖ := (mul_le_mul_of_nonneg_left (hclose w hw) (norm_nonneg u)).trans_eq (mul_comm _ _)
  have integralBound := norm_integral_le_of_norm_le
    (f := fun u ↦ support S hS u - support T hT u)
    ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).norm.const_mul ε)
    (Eventually.of_forall pointwise)
  simp only [Real.norm_eq_abs, integral_const_mul] at integralBound
  rw [meanWidth, meanWidth, ← mul_sub, ← integral_sub (integrable_support S hS) (integrable_support T hT),
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left integralBound (Real.sqrt_nonneg _)).trans_eq (by ring)

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TriangleDensity
section

/-! # Gaussian smoothing of the absolute projections in the triangle-density argument -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ContDiff

section

/-- The one-variable profile used to recover the even moments of a hemisphere restriction. -/
noncomputable def gaussianAbsProfile (a : ℝ) : ℝ :=
  ∫ x, |x + a| ∂gaussianReal 0 1

private theorem gaussianAbsProfile_hasDerivAt (a : ℝ) :
    HasDerivAt gaussianAbsProfile (1 - 2 * (gaussianReal 0 1).real (Iic (-a))) a := by
  let μ := gaussianReal 0 1
  let s := Iic (-a)
  let q := s.indicator (fun _ => (2 : ℝ))
  have hms : MeasurableSet s := measurableSet_Iic
  have hq : Integrable q μ := (integrable_const (2 : ℝ)).indicator hms
  have hqint : ∫ x, (1 - q x) ∂μ = 1 - 2 * μ.real s := by
    rw [integral_sub (integrable_const _) hq, integral_indicator hms]
    simp [mul_comm]
  rw [← hqint]
  apply (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (F := fun t x : ℝ => |x + t|)
    (F' := fun x => 1 - q x) (bound := fun _ => (1 : ℝ)) (s := univ)
    univ_mem ?_ ?_ ?_ ?_ (integrable_const 1) ?_).2
  · exact Eventually.of_forall fun t => by fun_prop
  · exact (IsGaussian.integrable_id.add (integrable_const a)).abs
  · exact (integrable_const (1 : ℝ) |>.sub hq).aestronglyMeasurable
  · refine ae_of_all _ fun x => LipschitzOnWith.of_dist_le_mul ?_
    intro t ht u hu
    simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub (x + t) (x + u)
  · let : NullSingletonClass μ := nullSingletonClass_gaussianReal one_ne_zero
    filter_upwards [μ.ae_ne (-a)] with x hx
    have H := (hasDerivAt_id a).const_add x
    rcases lt_or_gt_of_ne hx with hl | hl
    · have hmem : x ∈ s := hl.le
      norm_num [q, hmem]
      simpa [Function.comp_def] using
        (hasDerivAt_abs_neg (show x + a < 0 by linarith)).comp a H
    · have hmem : x ∉ s := not_le_of_gt hl
      norm_num [q, hmem]
      simpa [Function.comp_def] using
        (hasDerivAt_abs_pos (show 0 < x + a by linarith)).comp a H

private theorem stdGaussian_cdf_hasDerivAt (a : ℝ) :
    HasDerivAt (fun t => (gaussianReal 0 1).real (Iic t)) (gaussianPDFReal 0 1 a) a := by
  let p := gaussianPDFReal 0 1
  have hp : Continuous p := by unfold p gaussianPDFReal; fun_prop
  have hpint : Integrable p := integrable_gaussianPDFReal 0 1
  have heq : (fun t => (gaussianReal 0 1).real (Iic t)) =
      fun t => (∫ x in Iic 0, p x) + ∫ x in (0 : ℝ)..t, p x := by
    funext t
    rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ x),
      ← intervalIntegral.integral_Iic_sub_Iic hpint.integrableOn hpint.integrableOn]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable _ _)
    hp.aestronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt).const_add _

/-- Differentiating the smoothed absolute value twice gives twice the standard Gaussian density. -/
theorem gaussianAbsProfile_hasDerivAt_deriv (a : ℝ) :
    HasDerivAt (deriv gaussianAbsProfile) (2 * gaussianPDFReal 0 1 a) a := by
  have hdf := funext fun t => (gaussianAbsProfile_hasDerivAt t).deriv
  rw [hdf]
  have h := (hasDerivAt_const a (1 : ℝ)).sub
    (((stdGaussian_cdf_hasDerivAt (-a)).comp a (hasDerivAt_id a).neg).const_mul 2)
  simpa [Function.comp_def, gaussianPDFReal] using! h

theorem gaussianAbsProfile_smooth : ContDiff ℝ ∞ gaussianAbsProfile := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun a => (gaussianAbsProfile_hasDerivAt a).differentiableAt, ?_⟩
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun a => (gaussianAbsProfile_hasDerivAt_deriv a).differentiableAt, ?_⟩
  rw [funext fun a => (gaussianAbsProfile_hasDerivAt_deriv a).deriv]
  unfold gaussianPDFReal
  fun_prop

/-- All even derivatives at the origin detect a moment, including the constant moment. -/
theorem gaussianAbsProfile_even_deriv_ne_zero (j : ℕ) :
    iteratedDeriv (2 * j) gaussianAbsProfile 0 ≠ 0 := by
  cases j with
  | zero =>
    simp only [Nat.mul_zero, iteratedDeriv_zero, gaussianAbsProfile, add_zero]
    let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    apply ne_of_gt
    rw [integral_pos_iff_support_of_nonneg (fun x => abs_nonneg x) IsGaussian.integrable_id.abs]
    have hs : Function.support (fun x : ℝ => |x|) = ({0} : Set ℝ)ᶜ := by ext x; simp
    simp [hs, measure_compl]
  | succ k =>
    rw [show 2 * (k+1) = 2 * k + 1 + 1 by omega,
      iteratedDeriv_succ', iteratedDeriv_succ',
      funext fun a => (gaussianAbsProfile_hasDerivAt_deriv a).deriv]
    have hp : (fun a => 2 * gaussianPDFReal 0 1 a) =
        fun a : ℝ => (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(a^2 / 2)) := by
      funext a
      simp [gaussianPDFReal, div_eq_mul_inv, mul_assoc]
    rw [hp, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
      Polynomial.deriv_gaussian_eq_hermite_mul_gaussian,
      ← Polynomial.coeff_zero_eq_aeval_zero']
    have hc := Polynomial.coeff_hermite_explicit k 0
    simp at hc
    rw [hc]
    simp [Nat.doubleFactorial_pos _ |>.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']

/-- Differentiation on compact parameter sets with an integrable signed weight.
The bound on the derivative comes from the continuous kernel on a compact rectangle. -/
private theorem integral_weightedKernel_hasDerivAt {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} (hw : Integrable w μ) (K K' : ℝ × X → ℝ)
    (hK : Continuous K) (hK' : Continuous K')
    (hd : ∀ t x, HasDerivAt (fun s => K (s,x)) (K' (t,x)) t) (a : ℝ) :
    HasDerivAt (fun t => ∫ x, w x * K (t,x) ∂μ) (∫ x, w x * K' (a,x) ∂μ) a := by
  let s := Icc (a - 1) (a + 1)
  have hs : s ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := a - 1) (b := a + 1)).prod (isCompact_univ (X := X))).bddAbove_image
    (f := fun p : ℝ × X => |K' p|) hK'.abs.continuousOn
  obtain ⟨N, hN⟩ := (isCompact_univ (X := X)).bddAbove_image
    (f := fun x : X => |K (a,x)|) (hK.comp (continuous_const.prodMk continuous_id)).abs.continuousOn
  have hm (t : ℝ) : AEStronglyMeasurable (fun x => w x * K (t,x)) μ :=
    hw.aestronglyMeasurable.mul (hK.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t x => w x * K (t,x)) (F' := fun t x => w x * K' (t,x))
    (bound := fun x => |w x| * M) hs (.of_forall hm) ?_ ?_ ?_ (hw.abs.mul_const M) ?_).2
  · apply (hw.abs.mul_const N).mono' (hm a)
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hN ⟨x, mem_univ _, rfl⟩) (abs_nonneg _)
  · exact hw.aestronglyMeasurable.mul
      (hK'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · refine ae_of_all _ fun x t ht => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM ⟨(t,x), ⟨ht, mem_univ _⟩, rfl⟩) (abs_nonneg _)
  · exact ae_of_all _ fun x t _ => (hd t x).const_mul (w x)

/-- The Gaussian averages used in the proof of triangle density determine every even
moment of a bounded continuous projection. An integrable real weight allows signed measures. -/
theorem even_moments_zero_of_gaussianAbsProfile {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} (hw : Integrable w μ) {u : X → ℝ} (hu : Continuous u)
    (hann : ∀ t : ℝ, ∫ x, w x * gaussianAbsProfile (t * u x) ∂μ = 0) (j : ℕ) :
    ∫ x, w x * u x ^ (2 * j) ∂μ = 0 := by
  let K (n : ℕ) (p : ℝ × X) :=
    u p.2 ^ n * iteratedDeriv n gaussianAbsProfile (p.1 * u p.2)
  have hc (n : ℕ) : Continuous (K n) :=
    ((hu.comp continuous_snd).pow n).mul
      ((gaussianAbsProfile_smooth.continuous_iteratedDeriv n (by exact_mod_cast le_top)).comp
        (continuous_fst.mul (hu.comp continuous_snd)))
  have hz (n : ℕ) : ∀ t : ℝ, ∫ x, w x * K n (t,x) ∂μ = 0 := by
    induction n with
    | zero => simpa [K] using hann
    | succ n ih =>
      intro t
      have hd (a : ℝ) (x : X) : HasDerivAt (fun s => K n (s,x)) (K (n+1) (a,x)) a := by
        have hl := (gaussianAbsProfile_smooth.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n)
          (a * u x)).hasDerivAt
        convert! ((hl.comp a ((hasDerivAt_id a).mul_const (u x))).const_mul (u x ^ n)) using 1
        simp [K, iteratedDeriv_succ, pow_succ]
        ring
      have H := integral_weightedKernel_hasDerivAt hw (K n) (K (n+1)) (hc n) (hc (n+1)) hd t
      rw [funext ih] at H
      simpa using H.deriv.symm
  have H := hz (2 * j) 0
  simp only [K, zero_mul, ← mul_assoc, integral_mul_const, mul_eq_zero] at H
  exact H.resolve_right (gaussianAbsProfile_even_deriv_ne_zero j)

open scoped RealInnerProductSpace

/-- A finite signed weight on unit vectors annihilating all absolute projections
also annihilates every even power of every linear projection. -/
theorem even_moments_zero_of_abs_projections {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {w : X → ℝ} (hw : Integrable w μ) {u : X → E} (hu : Continuous u)
    (hunit : ∀ x, ‖u x‖ = 1) (hann : ∀ g : E, ∫ x, w x * |⟪u x, g⟫| ∂μ = 0)
    (z : E) (j : ℕ) : ∫ x, w x * ⟪u x, z⟫ ^ (2 * j) ∂μ = 0 := by
  apply even_moments_zero_of_gaussianAbsProfile hw (hu.inner continuous_const) _ j
  intro t
  let γ := stdGaussian E
  let F (x : X) (g : E) := w x * |⟪u x, g + t • z⟫|
  have hdist (x : X) : γ.map (innerSL ℝ (u x)) = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal]
    simp only [γ, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
      innerSL_apply_norm, hunit, one_pow, Real.toNNReal_one]
  have hinner (x : X) : w x * gaussianAbsProfile (t * ⟪u x, z⟫) = ∫ g, F x g ∂γ := by
    unfold F gaussianAbsProfile
    rw [← hdist x, integral_map (by fun_prop) (by fun_prop), integral_const_mul]
    simp [inner_add_right, real_inner_smul_right, innerSL_apply_apply ℝ]
  simp_rw [hinner]
  have hFi : Integrable (Function.uncurry F) (μ.prod γ) := by
    refine (hw.abs.mul_prod ((IsGaussian.integrable_id (μ := γ)).norm.add
      (integrable_const ‖t • z‖))).mono' ?_ ?_
    · apply hw.aestronglyMeasurable.comp_fst.mul
      exact ((hu.comp continuous_fst).inner
        (continuous_snd.add continuous_const) (𝕜 := ℝ)).abs.aestronglyMeasurable
    · refine ae_of_all _ fun p => ?_
      change ‖w p.1 * |⟪u p.1, p.2 + t • z⟫|‖ ≤ |w p.1| * (‖p.2‖ + ‖t • z‖)
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ‖u p.1‖ * ‖p.2 + t • z‖ := abs_real_inner_le_norm _ _
        _ = ‖p.2 + t • z‖ := by rw [hunit, one_mul]
        _ ≤ _ := norm_add_le _ _
  rw [integral_integral_swap hFi]
  simp only [F, hann, integral_zero]

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.IntervalMoments
section

/-! # Moment determinacy for measures concentrated on a bounded interval -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Two finite measures concentrated on a bounded interval and having equal moments
in every natural degree are equal. -/
theorem measure_eq_of_moments_of_mem_Icc {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (hm : ∀ n : ℕ, (∫ x, x ^ n ∂μ) = ∫ x, x ^ n ∂ν) : μ = ν := by
  have hdom (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) :
      integrableExpSet id ξ = univ :=
    eq_univ_of_forall fun _ ↦ integrable_exp_mul_of_mem_Icc aemeasurable_id hξ
  have hhol (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) :
      AnalyticOnNhd ℂ (complexMGF id ξ) univ := by
    simpa [hdom ξ hξ] using (analyticOnNhd_complexMGF (X := id) (μ := ξ))
  have hder (ξ : Measure ℝ) [IsFiniteMeasure ξ] (hξ : ∀ᵐ x ∂ξ, x ∈ Icc a b) (n : ℕ) :
      iteratedDeriv n (complexMGF id ξ) 0 = ((∫ x, x ^ n ∂ξ : ℝ) : ℂ) := by
    rw [iteratedDeriv_complexMGF (by simp [hdom ξ hξ])]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow,
      integral_complex_ofReal]
  apply Measure.ext_of_complexMGF_id_eq
  apply (hhol μ hμ).eq_of_eventuallyEq (hhol ν hν) (z₀ := 0)
  have hμseries := ((hhol μ hμ) 0 (mem_univ _)).hasFPowerSeriesAt
  have hνseries := ((hhol ν hν) 0 (mem_univ _)).hasFPowerSeriesAt
  simp_rw [hder μ hμ, hm] at hμseries
  simp_rw [hder ν hν] at hνseries
  filter_upwards [hμseries.eventually_hasSum_sub, hνseries.eventually_hasSum_sub] with z hz hz'
  exact hz.unique hz'

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.SphereProjections
section

/-! # Determining a sphere measure from half-line projections -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Metric Set
open scoped InnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- The projected laws on closed negative hemispheres determine a finite sphere measure.
The opposite direction recovers the positive hemisphere. -/
theorem sphereMeasure_eq_of_negative_projection (ξ η : Measure (sphere (0 : E) 1))
    [IsFiniteMeasure ξ] [IsFiniteMeasure η]
    (h : ∀ z : E, (ξ.restrict {x : (sphere (0 : E) 1) | ⟪(x : E), z⟫_ℝ ≤ 0}).map (fun x : (sphere (0 : E) 1) ↦ ⟪(x : E), z⟫_ℝ)
      = (η.restrict {x : (sphere (0 : E) 1) | ⟪(x : E), z⟫_ℝ ≤ 0}).map (fun x : (sphere (0 : E) 1) ↦ ⟪(x : E), z⟫_ℝ)) :
    ξ = η := by
  let p (z : E) (x : (sphere (0 : E) 1)) := ⟪(x : E), z⟫_ℝ
  have hp (z : E) : Measurable (p z) := (continuous_subtype_val.inner continuous_const).measurable
  have hneg (z : E) : (ξ.map (p z)).restrict (Iic 0) = (η.map (p z)).restrict (Iic 0) := by
    rw [Measure.restrict_map (hp z) measurableSet_Iic, Measure.restrict_map (hp z) measurableSet_Iic]
    simpa [p, preimage, Iic] using h z
  have hpos (z : E) : (ξ.map (p z)).restrict (Ici 0) = (η.map (p z)).restrict (Ici 0) := by
    have H := congrArg (Measure.map (fun t : ℝ ↦ -t)) (h (-z))
    rw [Measure.map_map measurable_neg (hp (-z)), Measure.map_map measurable_neg (hp (-z))] at H
    rw [Measure.restrict_map (hp z) measurableSet_Ici, Measure.restrict_map (hp z) measurableSet_Ici]
    simpa [p, Function.comp_def, preimage, Ici] using H
  have hproj (z : E) : ξ.map (p z) = η.map (p z) := by
    have H := Measure.restrict_union_congr.mpr ⟨hneg z, hpos z⟩
    simpa using H
  apply (MeasurableEmbedding.subtype_coe (isClosed_sphere (x := (0 : E)) (ε := 1)).measurableSet).map_injective
  apply Measure.ext_of_charFun
  funext z
  rw [charFun_map_eq_charFun_map_inner_one measurable_subtype_coe.aemeasurable,
    charFun_map_eq_charFun_map_inner_one (μ := η) measurable_subtype_coe.aemeasurable]
  exact congrArg (fun μ : Measure ℝ ↦ charFun μ 1) (hproj z)

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.HemisphereMoments
section

/-! # Recovery of a sphere measure from even moments on hemispheres

On the negative hemisphere for a given projection, the squared projection determines
the projection by the negative square root. Its law is compactly supported, so
its moments determine its law. The scalar projections then determine the measure.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Set
open scoped RealInnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem negativeProjection_eq_of_even_moments
    (ξ η : Measure (Metric.sphere (0 : E) 1)) [IsFiniteMeasure ξ] [IsFiniteMeasure η] (z : E)
    (hmom : ∀ j : ℕ,
      (∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂ξ) =
      ∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂η) :
    (ξ.restrict {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}).map (fun x : Metric.sphere (0 : E) 1 ↦ ⟪(x : E), z⟫) =
    (η.restrict {x : Metric.sphere (0 : E) 1 | ⟪(x : E), z⟫ ≤ 0}).map (fun x : Metric.sphere (0 : E) 1 ↦ ⟪(x : E), z⟫) := by
  let p (x : Metric.sphere (0 : E) 1) := ⟪(x : E), z⟫
  let H := {x | p x ≤ 0}
  let q := fun x ↦ p x ^ 2
  have hp : Measurable p := by dsimp [p]; fun_prop
  have hH : MeasurableSet H := measurableSet_le hp measurable_const
  have hq : Measurable q := hp.pow_const 2
  have hbound (μ : Measure (Metric.sphere (0 : E) 1)) :
      ∀ᵐ s ∂μ.map q, s ∈ Icc 0 (‖z‖ ^ 2) := by
    apply (ae_map_iff hq.aemeasurable measurableSet_Icc).2
    refine ae_of_all _ fun x ↦ ⟨sq_nonneg _, ?_⟩
    have hpx : |p x| ≤ ‖z‖ := by simpa [p] using abs_real_inner_le_norm (x : E) z
    simpa only [q, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hpx 2
  have heq : (ξ.restrict H).map q = (η.restrict H).map q := by
    apply measure_eq_of_moments_of_mem_Icc (hbound _) (hbound _)
    intro j
    rw [integral_map hq.aemeasurable (by fun_prop), integral_map hq.aemeasurable (by fun_prop)]
    simpa only [q, p, H, ← pow_mul] using hmom j
  have hrecover (μ : Measure (Metric.sphere (0 : E) 1)) :
      ((μ.restrict H).map q).map (fun t : ℝ ↦ - Real.sqrt t) = (μ.restrict H).map p := by
    rw [Measure.map_map (by fun_prop) hq]
    refine Measure.map_congr ((ae_restrict_mem hH).mono fun x hx ↦ ?_)
    change -Real.sqrt (p x ^ 2) = p x
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hx, neg_neg]
  exact (hrecover ξ).symm.trans ((congrArg (Measure.map (fun t : ℝ ↦ -Real.sqrt t)) heq).trans
    (hrecover η))

/-- Even projection moments on all closed hemispheres determine a finite measure
on the sphere. -/
theorem sphereMeasure_eq_of_hemisphere_even_moments [FiniteDimensional ℝ E]
    (ξ η : Measure (Metric.sphere (0 : E) 1)) [IsFiniteMeasure ξ] [IsFiniteMeasure η]
    (hmom : ∀ (z v : E) (j : ℕ),
      (∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), v⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂ξ) =
      ∫ x in {x : Metric.sphere (0 : E) 1 | ⟪(x : E), v⟫ ≤ 0}, ⟪(x : E), z⟫ ^ (2 * j) ∂η) :
    ξ = η := by
  apply sphereMeasure_eq_of_negative_projection
  intro z
  exact negativeProjection_eq_of_even_moments ξ η z (hmom z z)

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TriangleMeasure
section

/-! # Hemisphere projections determined by triangle supports -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem integrable_sphere {ρ : Measure (Metric.sphere (0 : E) 1)} [IsFiniteMeasure ρ]
    {f : (Metric.sphere (0 : E) 1) → ℝ} (hf : Continuous f) : Integrable f ρ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem hemisphere_hinge_limit (ρ : Measure (Metric.sphere (0 : E) 1)) [IsFiniteMeasure ρ] (v w : E) :
    Tendsto (fun a : ℝ => ∫ x : (Metric.sphere (0 : E) 1), max (max 0 (a * ⟪(x:E), v⟫)) ⟪(x:E), w⟫ -
      max 0 (a * ⟪(x:E), v⟫) ∂ρ) atTop
      (𝓝 (∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, max 0 ⟪(x:E), w⟫ ∂ρ)) := by
  let H := {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}
  have hH : MeasurableSet H := measurableSet_le (by fun_prop) measurable_const
  rw [← integral_indicator hH]
  apply tendsto_integral_filter_of_dominated_convergence (fun x : (Metric.sphere (0 : E) 1) => |⟪(x:E), w⟫|)
  · exact .of_forall fun a => by fun_prop
  · refine .of_forall fun a => ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
    calc
      _ ≤ max 0 ⟪(x:E), w⟫ := by grind
      _ ≤ _ := max_le (abs_nonneg _) (le_abs_self _)
  · exact integrable_sphere (by fun_prop)
  · refine ae_of_all _ fun x => ?_
    by_cases hx : ⟪(x:E), v⟫ ≤ 0
    · rw [indicator_of_mem (show x ∈ H from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
      simp [max_eq_left (mul_nonpos_of_nonneg_of_nonpos ha hx)]
    · rw [indicator_of_notMem (show x ∉ H from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⟪(x:E), w⟫ / ⟪(x:E), v⟫)] with a ha
      have hle := (div_le_iff₀ (lt_of_not_ge hx)).mp ha
      simp [max_eq_left (hle.trans (le_max_right 0 _))]

private theorem abs_projection_hemisphere_eq {μ ν : Measure (Metric.sphere (0 : E) 1)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v w : E, (∫ x : (Metric.sphere (0 : E) 1), max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂μ) =
      ∫ x : (Metric.sphere (0 : E) 1), max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂ν)
    (v w : E) : (∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, |⟪(x:E), w⟫| ∂μ) =
      ∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, |⟪(x:E), w⟫| ∂ν := by
  have hinge (b : E) : (∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, max 0 ⟪(x:E), b⟫ ∂μ) =
      ∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, max 0 ⟪(x:E), b⟫ ∂ν := by
    refine tendsto_nhds_unique (hemisphere_hinge_limit μ v b)
      ((hemisphere_hinge_limit ν v b).congr fun a => ?_)
    rw [integral_sub (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop)),
      integral_sub (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop))]
    have h0 := h (a • v) 0
    simp only [inner_zero_right, max_eq_left (le_max_left _ _), real_inner_smul_right] at h0
    simpa only [real_inner_smul_right, h0] using congrArg
      (· - ∫ x : (Metric.sphere (0 : E) 1), max 0 (a * ⟪(x:E), v⟫) ∂ν) (h (a • v) b).symm
  have ha (x : (Metric.sphere (0 : E) 1)) : |⟪(x:E), w⟫| = max 0 ⟪(x:E), w⟫ + max 0 ⟪(x:E), -w⟫ := by
    rw [inner_neg_right]
    rcases le_total 0 ⟪(x:E), w⟫ with h | h <;> simp [h, neg_nonpos.mpr, neg_nonneg.mpr, abs_of_nonpos, abs_of_nonneg]
  simp_rw [ha]
  rw [integral_add (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop)),
      integral_add (integrable_sphere (by fun_prop)) (integrable_sphere (by fun_prop)), hinge, hinge]

/-- Finite triangle integrals determine every even moment of the projections of
each closed hemisphere restriction. -/
theorem hemisphere_moments_eq_of_triangle_integrals {μ ν : Measure (Metric.sphere (0 : E) 1)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v w : E, (∫ x : (Metric.sphere (0 : E) 1), max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂μ) =
      ∫ x : (Metric.sphere (0 : E) 1), max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂ν)
    (z v : E) (j : ℕ) :
    (∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, ⟪(x:E), z⟫ ^ (2*j) ∂μ) =
    ∫ x in {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}, ⟪(x:E), z⟫ ^ (2*j) ∂ν := by
  let H := {x : (Metric.sphere (0 : E) 1) | ⟪(x:E), v⟫ ≤ 0}
  let α := μ.restrict H
  let β := ν.restrict H
  let ρ := α + β
  let : IsFiniteMeasure α := inferInstanceAs (IsFiniteMeasure (μ.restrict H))
  let : IsFiniteMeasure β := inferInstanceAs (IsFiniteMeasure (ν.restrict H))
  let : IsFiniteMeasure ρ := inferInstanceAs (IsFiniteMeasure (α + β))
  let : α.HaveLebesgueDecomposition ρ := Measure.haveLebesgueDecomposition_of_sigmaFinite α ρ
  let : β.HaveLebesgueDecomposition ρ := Measure.haveLebesgueDecomposition_of_sigmaFinite β ρ
  let w (x : (Metric.sphere (0 : E) 1)) := (α.rnDeriv ρ x).toReal - (β.rnDeriv ρ x).toReal
  have hα : α ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hβ : β ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hw : Integrable w ρ := by
    have ha := (integrable_toReal_rnDeriv_mul_iff hα).mpr (integrable_const (1:ℝ))
    have hb := (integrable_toReal_rnDeriv_mul_iff hβ).mpr (integrable_const (1:ℝ))
    simpa [w, Pi.sub_def] using ha.sub hb
  have hd {f : (Metric.sphere (0 : E) 1) → ℝ} (hf : Continuous f) :
      (∫ x, w x * f x ∂ρ) = (∫ x, f x ∂α) - ∫ x, f x ∂β := by
    simp only [w, sub_mul]
    rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hα).mpr (integrable_sphere hf))
      ((integrable_toReal_rnDeriv_mul_iff hβ).mpr (integrable_sphere hf)),
      integral_toReal_rnDeriv_mul hα, integral_toReal_rnDeriv_mul hβ]
  have he := even_moments_zero_of_abs_projections (u := fun x : (Metric.sphere (0 : E) 1) => (x:E)) hw
    continuous_subtype_val (fun x => by simp) (fun g => ?_) z j
  · rw [hd (by fun_prop)] at he
    exact sub_eq_zero.mp he
  · rw [hd (by fun_prop)]
    exact sub_eq_zero.mpr (abs_projection_hemisphere_eq h v g)

theorem eq_of_triangle_integrals (μ ν : Measure (Metric.sphere (0 : E) 1))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v w : E, (∫ x : (Metric.sphere (0 : E) 1), max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂μ) =
      ∫ x : (Metric.sphere (0 : E) 1), max (max 0 ⟪(x:E), v⟫) ⟪(x:E), w⟫ ∂ν) : μ = ν :=
  sphereMeasure_eq_of_hemisphere_even_moments μ ν (hemisphere_moments_eq_of_triangle_integrals h)

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.RieszSplit
section

/-! # Decomposition of a real continuous functional into positive functionals -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

private theorem norm_sup_zero_add_le (f g : C(X, ℝ)) :
    ‖(f + g) ⊔ 0‖ ≤ ‖f ⊔ 0‖ + ‖g ⊔ 0‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  change |max (f x + g x) 0| ≤ _
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · have hf := (f ⊔ 0).apply_le_norm x
    have hg := (g ⊔ 0).apply_le_norm x
    change max (f x) 0 ≤ _ at hf
    change max (g x) 0 ≤ _ at hg
    exact add_le_add ((le_max_left _ _).trans hf) ((le_max_left _ _).trans hg)
  · positivity

private theorem norm_sup_zero_smul (c : ℝ) (hc : 0 ≤ c) (f : C(X, ℝ)) :
    ‖(c • f) ⊔ 0‖ = c * ‖f ⊔ 0‖ := by
  have h : (c • f) ⊔ 0 = c • (f ⊔ 0) := by
    ext x
    change max (c * f x) 0 = c * max (f x) 0
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

private theorem norm_le_parts (f : C(X, ℝ)) : ‖f‖ ≤ ‖f ⊔ 0‖ + ‖(-f) ⊔ 0‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  have hf := (f ⊔ 0).apply_le_norm x
  have hn := ((-f) ⊔ 0).apply_le_norm x
  change max (f x) 0 ≤ _ at hf
  change max (-f x) 0 ≤ _ at hn
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [le_max_left (-f x) 0, norm_nonneg (f ⊔ 0)]
  · linarith [le_max_left (f x) 0, norm_nonneg ((-f) ⊔ 0)]

/-- Every real continuous functional on continuous functions on a compact space
is the difference of two positive linear maps. -/
theorem exists_positiveLinearMap_sub (L : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ P N : C(X, ℝ) →ₚ[ℝ] ℝ, ∀ f, L f = P f - N f := by
  let D : Submodule ℝ (C(X, ℝ) × C(X, ℝ)) :=
    { carrier := {p | p.1 = p.2}
      zero_mem' := rfl
      add_mem' := fun {a b} ha hb ↦ congrArg₂ (· + ·) ha hb
      smul_mem' := fun c _ ha ↦ congrArg (c • ·) ha }
  let F : (C(X, ℝ) × C(X, ℝ)) →ₗ.[ℝ] ℝ :=
    ⟨D, L.toLinearMap.comp ((LinearMap.fst ℝ _ _).comp D.subtype)⟩
  let B (p : C(X, ℝ) × C(X, ℝ)) := ‖L‖ * (‖p.1 ⊔ 0‖ + ‖(-p.2) ⊔ 0‖)
  obtain ⟨G, hdiag, hG⟩ := exists_extension_of_le_sublinear F B
    (by
      intro c hc p
      change ‖L‖ * (‖(c • p.1) ⊔ 0‖ + ‖(-(c • p.2)) ⊔ 0‖) = c * B p
      rw [← smul_neg, norm_sup_zero_smul c hc.le, norm_sup_zero_smul c hc.le]
      dsimp [B]
      ring)
    (by
      intro p q
      change ‖L‖ * (‖(p.1 + q.1) ⊔ 0‖ + ‖(-(p.2 + q.2)) ⊔ 0‖) ≤ B p + B q
      rw [neg_add]
      dsimp [B]
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ L.opNorm_nonneg
      linarith [norm_sup_zero_add_le p.1 q.1, norm_sup_zero_add_le (-p.2) (-q.2)])
    (by
      intro p
      have hp : p.val.1 = p.val.2 := p.property
      change L p.val.1 ≤ ‖L‖ * (‖p.val.1 ⊔ 0‖ + ‖(-p.val.2) ⊔ 0‖)
      rw [← hp]
      exact (le_abs_self _).trans <| (L.le_opNorm _).trans <|
        mul_le_mul_of_nonneg_left (norm_le_parts _) L.opNorm_nonneg)
  let P := G.comp (LinearMap.inl ℝ C(X, ℝ) C(X, ℝ))
  let N := -G.comp (LinearMap.inr ℝ C(X, ℝ) C(X, ℝ))
  have hP (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ P f := by
    have h := hG (-f, 0)
    have hf' : -f ≤ 0 := fun x ↦ neg_nonpos.mpr (hf x)
    have hneg : (-f, (0 : C(X, ℝ))) = -(f, 0) := by simp
    have hbound : B (-f, 0) = 0 := by simp [B, sup_eq_right.mpr hf']
    rw [hbound, hneg, map_neg, neg_nonpos] at h
    exact h
  have hN (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ N f := by
    have h := hG (0, f)
    have hf' : -f ≤ 0 := fun x ↦ neg_nonpos.mpr (hf x)
    simpa [B, sup_eq_right.mpr hf', N] using h
  refine ⟨{ P with monotone' := fun a b h ↦ ?_ }, { N with monotone' := fun a b h ↦ ?_ }, ?_⟩
  · simpa using hP (b - a) (fun x ↦ sub_nonneg.mpr (h x))
  · simpa using hN (b - a) (fun x ↦ sub_nonneg.mpr (h x))
  · intro f
    have h := (hdiag ⟨(f, f), rfl⟩).symm
    change L f = G (f, 0) - -G (0, f)
    change L f = G (f, f) at h
    rw [h, sub_neg_eq_add, ← map_add]
    simp

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TriangleSpan
section

/-! # Uniform density from separation of finite Borel measures -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set MeasureTheory
open scoped CompactlySupported

section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

private theorem exists_measure_of_positiveLinearMap (P : C(X, ℝ) →ₚ[ℝ] ℝ) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂μ = P f := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ P f.toContinuousMap
      map_add' := fun f g ↦ P.map_add _ _
      map_smul' := fun c f ↦ P.map_smul _ _
      monotone' := fun _ _ h ↦ P.monotone h }
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, fun f ↦ ?_⟩
  let fc : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace _⟩
  exact RealRMK.integral_rieszMeasure Λ fc

/-- A family which determines finite Borel measures on a compact Hausdorff
space spans a uniformly dense subspace of the real continuous functions. -/
theorem dense_span_of_separates_measures (S : Set C(X, ℝ))
    (hsep : ∀ (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ f ∈ S, ∫ x, f x ∂μ = ∫ x, f x ∂ν) → μ = ν) :
    Dense (Submodule.span ℝ S : Set C(X, ℝ)) := by
  intro f
  by_contra hf
  let M := (Submodule.span ℝ S).topologicalClosure
  have hf' : f ∉ M := hf
  obtain ⟨L, c, hM, hfc⟩ := geometric_hahn_banach_closed_point M.convex
    (Submodule.isClosed_topologicalClosure _) hf'
  have hzero (g : C(X, ℝ)) (hg : g ∈ M) : L g = 0 := by
    by_contra h
    have hc := hM ((c / L g) • g) (M.smul_mem _ hg)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h] at hc
    exact hc.false
  obtain ⟨P, N, hL⟩ := exists_positiveLinearMap_sub L
  obtain ⟨μ, hμ, hP⟩ := exists_measure_of_positiveLinearMap P
  obtain ⟨ν, hν, hN⟩ := exists_measure_of_positiveLinearMap N
  have heq := hsep μ ν fun g hg ↦ by
    rw [hP, hN]
    exact sub_eq_zero.mp ((hL g).symm.trans
      (hzero g ((Submodule.span ℝ S).le_topologicalClosure (Submodule.subset_span hg))))
  have hLf : L f = 0 := by rw [hL, ← hP, ← hN, heq, sub_self]
  have h0 := hM 0 M.zero_mem
  simp only [map_zero] at h0
  exact (h0.trans hfc).ne' hLf

section

open scoped RealInnerProductSpace Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Triangle support functions, including degenerate triangles, span a uniformly
dense subspace of the continuous functions on the unit sphere. -/
theorem dense_span_triangleSupports :
    Dense (Submodule.span ℝ (triangleSupports E) : Set C(Metric.sphere (0 : E) 1, ℝ)) := by
  apply dense_span_of_separates_measures
  intro μ ν _ _ h
  apply eq_of_triangle_integrals μ ν
  intro v w
  have htri := h _ ⟨0, v, w, rfl⟩
  simpa only [sphereSupport, ContinuousMap.coe_mk, support,
    Finset.sup'_insert (Finset.insert_nonempty _ _), Finset.sup'_insert (Finset.singleton_nonempty _),
    Finset.sup'_singleton, inner_zero_right, max_assoc] using htri

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.PriceContinuity
section

/-! # Uniform support bounds control polytope prices

A fixed polytope containing the unit ball absorbs errors in support values.
Separation of a point from a finite convex hull detects inclusion by testing
against unit vectors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped RealInnerProductSpace Classical Pointwise
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem mem_hull_of_forall_unit (T : Finset E) (hT : T.Nonempty) (x : E)
    (h : ∀ u : E, ‖u‖ = 1 → ∃ y ∈ convexHull ℝ (T : Set E), ⟪u, x⟫ ≤ ⟪u, y⟫) :
    x ∈ convexHull ℝ (T : Set E) := by
  by_contra hx
  obtain ⟨f, c, hf, hfx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (T.finite_toSet.isClosed_convexHull ℝ) hx
  let w := (InnerProductSpace.toDual ℝ E).symm f
  have hw (y : E) : ⟪w, y⟫ = f y := InnerProductSpace.toDual_symm_apply
  have hpos : 0 < ‖w‖ := by
    by_contra! hn
    have hw0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    have hz (y : E) : f y = 0 := by simpa [hw0] using (hw y).symm
    obtain ⟨t, ht⟩ := hT
    exact (lt_irrefl (0 : ℝ)) (by simpa [hz] using (hf t (subset_convexHull ℝ _ ht)).trans hfx)
  obtain ⟨y, hy, hxy⟩ := h (‖w‖⁻¹ • w) (by simp [norm_smul, hpos.ne'])
  simp only [real_inner_smul_left, hw] at hxy
  exact (not_le.mpr ((hf y hy).trans hfx)) (le_of_mul_le_mul_left hxy (inv_pos.mpr hpos))

private theorem subset_hull_add_of_support_le (S T Q : Finset E) (hS : S.Nonempty)
    (hT : T.Nonempty) (hQ : Q.Nonempty)
    (hball : closedBall (0 : E) 1 ⊆ convexHull ℝ (Q : Set E))
    (ε : ℝ)
    (h : ∀ u ∈ sphere (0 : E) 1, support S hS u ≤ support T hT u + ε) :
    (S : Set E) ⊆ convexHull ℝ ((T + Q.image (ε • ·) : Finset E) : Set E) := by
  intro x hx
  apply mem_hull_of_forall_unit _ (hT.add (hQ.image _))
  intro u hu
  have hus : u ∈ sphere (0 : E) 1 := by simpa using hu
  obtain ⟨y, hy, hsup⟩ := T.exists_mem_eq_sup' hT (fun y ↦ ⟪u, y⟫)
  refine ⟨y + ε • u, ?_, ?_⟩
  · rw [Finset.coe_add, Finset.coe_image, convexHull_add]
    have hscale : ε • u ∈ convexHull ℝ ((fun y : E ↦ ε • y) '' (Q : Set E)) := by
      change ε • u ∈ convexHull ℝ (ε • (Q : Set E))
      rw [convexHull_smul]
      exact Set.smul_mem_smul_set (hball (sphere_subset_closedBall hus))
    exact Set.add_mem_add (subset_convexHull ℝ (T : Set E) hy) hscale
  · have hl : ⟪u, x⟫ ≤ support S hS u := S.le_sup' _ hx
    have hr : support T hT u = ⟪u, y⟫ := hsup
    simpa only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu,
      one_pow, mul_one, hr] using hl.trans (h u hus)

/-- Uniform support approximation on the unit sphere bounds the price error by
the same error times the price of a fixed polytope containing the unit ball. -/
theorem exists_price_lipschitz_of_jointConvex (δ : Finset E → ℝ)
    (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S) :
    ∃ C : ℝ, ∀ ε > 0, ∀ S T : Finset E, ∀ hS : S.Nonempty, ∀ hT : T.Nonempty,
      (∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) →
          |δ S - δ T| ≤ C * ε := by
  obtain ⟨Q, hQball, _⟩ := (convex_closedBall (0 : E) 1).exists_subset_interior_convexHull_finset_of_isCompact
    (isCompact_closedBall _ _) (t := Set.univ) Filter.univ_mem
  have hball := hQball.trans interior_subset
  have hQ : Q.Nonempty := by
    by_contra! h
    subst Q
    simpa using hball (show (0 : E) ∈ closedBall 0 1 by simp)
  refine ⟨δ Q, ?_⟩
  intro ε he S T hS hT h
  have hdir (A B : Finset E) (hA : A.Nonempty) (hB : B.Nonempty)
      (hAB : ∀ u ∈ sphere (0 : E) 1, support A hA u ≤ support B hB u + ε) :
      δ A ≤ δ B + ε * δ Q := by
    let P := B + Q.image (ε • ·)
    have hP : P.Nonempty := hB.add (hQ.image _)
    have hsub := subset_hull_add_of_support_le A B Q hA hB hQ hball ε hAB
    calc
      δ A ≤ δ (P ∪ A) := hmono hA Finset.subset_union_right
      _ = δ P := price_union_of_subset_convexHull δ hjoint hmono P A hP hsub
      _ ≤ δ B + δ (Q.image (ε • ·)) := price_add_le_of_jointConvex δ hjoint hscale
        B _ hB (hQ.image _)
      _ = _ := by rw [hscale Q hQ ε he]
  have hST := hdir S T hS hT (fun u hu ↦ by linarith [(abs_le.mp (h u hu)).2])
  have hTS := hdir T S hT hS (fun u hu ↦ by linarith [(abs_le.mp (h u hu)).1])
  rw [mul_comm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.SegmentAdditivity
section

/-! # Adding a segment to a polytope

The homogeneous-flat part of the flat diagonal law glues together translated
vertex lists along the direction of a segment. Intersecting submodularity
controls the price of every successive translate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [DecidableEq E]

private def translates (S : Finset E) (v : E) : ℕ → Finset E
  | 0 => S
  | n + 1 => S ∪ (translates S v n + {v})

private theorem subset_translates (S : Finset E) (v : E) (n : ℕ) :
    S ⊆ translates S v n := by
  cases n with
  | zero => rfl
  | succ n => exact Finset.subset_union_left

private theorem mem_lastTranslate {S : Finset E} {x : E} (hx : x ∈ S) (v : E) (n : ℕ) :
    x + n • v ∈ translates S v n := by
  induction n with
  | zero => simpa [translates] using hx
  | succ n ih =>
    apply Finset.mem_union_right
    rw [succ_nsmul, ← add_assoc]
    exact Finset.add_mem_add ih (Finset.mem_singleton_self _)

private theorem price_translates_le (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (htrans : ∀ (S : Finset E), S.Nonempty → ∀ v : E, δ (S + {v}) = δ S)
    (hsubmod : IntersectingSubmodular δ) (S : Finset E) (hS : S.Nonempty) (v : E) (n : ℕ) :
    δ (translates S v n) ≤ δ S + n * (δ (S ∪ (S + {v})) - δ S) := by
  induction n with
  | zero => simp [translates]
  | succ n ih =>
    let P := translates S v n
    have hSP : S ⊆ P := subset_translates S v n
    have hP := hS.mono hSP
    let X := P + {v}
    let B := S ∪ (S + {v})
    have hSX : S + {v} ⊆ X := Finset.add_subset_add_right hSP
    have hSB : S + {v} ⊆ B := Finset.subset_union_right
    have hSI : S + {v} ⊆ X ∩ B := Finset.subset_inter hSX hSB
    have hS' : (S + {v}).Nonempty := hS.add (Finset.singleton_nonempty _)
    have hU : X ∪ B = translates S v (n+1) := by
      change X ∪ (S ∪ (S + {v})) = S ∪ X
      ext x
      simp only [Finset.mem_union]
      grind
    have hstep := hsubmod (A := X) (B := B) (hS'.mono hSI)
    have hinter := hmono hS' hSI
    have hX : δ X = δ P := htrans P hP v
    rw [hU, hX] at hstep
    rw [htrans S hS v] at hinter
    dsimp [B, P] at hstep
    push_cast
    linarith

variable [NormedSpace ℝ E]

/-- For a translation-invariant, monotone, intersecting-submodular price which is
subadditive for Minkowski addition and agrees with distance on pairs, adding
a segment of displacement `v` increases the price by exactly `‖v‖`. -/
theorem price_add_segment (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (htrans : ∀ (S : Finset E), S.Nonempty → ∀ v : E, δ (S + {v}) = δ S)
    (hsubmod : IntersectingSubmodular δ)
    (hsubadd : ∀ (S T : Finset E), S.Nonempty → T.Nonempty → δ (S + T) ≤ δ S + δ T)
    (hpair : ∀ x y : E, δ {x, y} = dist x y)
    (S : Finset E) (hS : S.Nonempty) (v : E) :
    δ (S + {0, v}) = δ S + ‖v‖ := by
  have hseg : S + {0, v} = S ∪ (S + {v}) := by
    rw [show ({0, v} : Finset E) = {0} ∪ {v} by simp, Finset.add_union]
    change S + 0 ∪ (S + {v}) = _
    rw [add_zero]
  apply le_antisymm
  · simpa [hpair] using hsubadd S {0, v} hS (Finset.insert_nonempty _ _)
  rw [hseg]
  obtain ⟨x, hx⟩ := hS
  by_contra! hlt
  have hgap : 0 < ‖v‖ - (δ (S ∪ (S + {v})) - δ S) := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (δ S / (‖v‖ - (δ (S ∪ (S + {v})) - δ S)))
  have hlarge := (div_lt_iff₀ hgap).mp hn
  have hupper := price_translates_le δ hmono htrans hsubmod S ⟨x, hx⟩ v n
  have hmem : ({x, x + n • v} : Finset E) ⊆ translates S v n := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨subset_translates S v n hx, mem_lastTranslate hx v n⟩
  have hlower := hmono (Finset.insert_nonempty _ _) hmem
  rw [hpair, dist_eq_norm', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
    Real.norm_natCast] at hlower
  linarith

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TriangleAdditivity
section

/-! # Adding a triangle to a polytope

Adding a triangle and then its negative has the same effect as adding the
segments along its three oriented edges. Segment additivity and the planar
triangle law therefore force additivity upon just the first addition.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [DecidableEq E]

/-- Differences of triangle vertices are precisely the subset sums of the three
oriented edge vectors. The identity also holds for degenerate triangles. -/
theorem triangle_add_neg_eq_segments (x y z : E) :
    ({x, y, z} : Finset E) + {-x, -y, -z} =
      ({0, y - x} : Finset E) + {0, z - y} + {0, x - z} := by
  ext t
  simp only [Finset.mem_add, Finset.mem_insert, Finset.mem_singleton,
    exists_eq_or_imp, exists_eq_left, zero_add, add_zero]
  simp only [or_and_right, exists_or, exists_eq_left']
  abel_nf
  tauto

/-- For a subadditive price with exact segment additivity and the planar triangle
law, Minkowski addition of a triangle is exactly additive. -/
theorem price_add_triangle (δ : Finset E → ℝ)
    (hsubadd : ∀ (S T : Finset E), S.Nonempty → T.Nonempty → δ (S + T) ≤ δ S + δ T)
    (hsegment : ∀ (S : Finset E), S.Nonempty → ∀ v : E, δ (S + {0, v}) = δ S + ‖v‖)
    (htriangle : ∀ x y z : E, δ {x, y, z} = (dist x y + dist y z + dist z x) / 2)
    (S : Finset E) (hS : S.Nonempty) (x y z : E) :
    δ (S + {x, y, z}) = δ S + δ {x, y, z} := by
  let T : Finset E := {x, y, z}
  let U : Finset E := {-x, -y, -z}
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hU : U.Nonempty := Finset.insert_nonempty _ _
  have hsum : δ ((S + T) + U) = δ S + (dist x y + dist y z + dist z x) := by
    rw [add_assoc, triangle_add_neg_eq_segments, ← add_assoc, ← add_assoc]
    repeat rw [hsegment _ _ _]
    · simp only [dist_eq_norm']
      ring
    all_goals repeat first | apply Finset.Nonempty.add | exact Finset.insert_nonempty _ _ | exact hS
  have h₂ := hsubadd (S + T) U (hS.add hT) hU
  rw [hsum] at h₂
  have hpriceT := htriangle x y z
  have hpriceU := htriangle (-x) (-y) (-z)
  simp only [dist_neg_neg] at hpriceU
  change δ (S + T) = δ S + δ T
  change δ T = _ at hpriceT
  change δ U = _ at hpriceU
  exact le_antisymm (hsubadd S T hS hT) (by linarith)

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.MinkowskiDensity
section

/-! # From triangle support density to the homogeneous flat diagonal law

Subtracting Gaussian mean width from the price leaves a function unchanged by
addition of triangles. Every linear combination of triangle support functions is
the difference of support functions of two finite Minkowski sums of triangles.
The Lipschitz bound in the support norm then determines the price on every
polytope.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Metric MeasureTheory ProbabilityTheory Filter
open scoped Pointwise Classical Topology

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def InvariantUnder (D : (S : Finset E) → S.Nonempty → ℝ)
    (P : Finset E) (hP : P.Nonempty) : Prop :=
  ∀ (S : Finset E) (hS : S.Nonempty), D (S + P) (hS.add hP) = D S hS

omit [InnerProductSpace ℝ E] in
private theorem invariantUnder_zero (D : (S : Finset E) → S.Nonempty → ℝ) :
    InvariantUnder D {0} (Finset.singleton_nonempty _) := by
  intro S hS
  simp [show ({0} : Finset E) = 0 from rfl]

omit [InnerProductSpace ℝ E] in
private theorem invariantUnder_add {D : (S : Finset E) → S.Nonempty → ℝ}
    {P Q : Finset E} {hP : P.Nonempty} {hQ : Q.Nonempty}
    (hp : InvariantUnder D P hP) (hq : InvariantUnder D Q hQ) :
    InvariantUnder D (P + Q) (hP.add hQ) := by
  intro S hS
  simpa only [add_assoc] using (hq (S + P) (hS.add hP)).trans (hp S hS)

private theorem span_difference_of_triangles (D : (S : Finset E) → S.Nonempty → ℝ)
    (htri : ∀ a b c : E, InvariantUnder D {a, b, c} (Finset.insert_nonempty _ _))
    {f : C(sphere (0 : E) 1, ℝ)} (hf : f ∈ Submodule.span ℝ (triangleSupports E)) :
    ∃ (P M : Finset E) (hP : P.Nonempty) (hM : M.Nonempty),
      InvariantUnder D P hP ∧ InvariantUnder D M hM ∧
        f = sphereSupport P hP - sphereSupport M hM := by
  induction hf using Submodule.closure_induction with
  | zero =>
    refine ⟨{0}, {0}, _, _, invariantUnder_zero D, invariantUnder_zero D, ?_⟩
    simp
  | add x y _ _ hx hy =>
    obtain ⟨P, M, hP, hM, p, m, rfl⟩ := hx
    obtain ⟨Q, N, hQ, hN, q, n, rfl⟩ := hy
    refine ⟨P + Q, M + N, hP.add hQ, hM.add hN, invariantUnder_add p q, invariantUnder_add m n, ?_⟩
    rw [sphereSupport_add P Q hP hQ, sphereSupport_add M N hM hN]
    abel
  | smul_mem r g hg =>
    obtain ⟨a, b, c, rfl⟩ := hg
    let T : Finset E := {a, b, c}
    have hT : T.Nonempty := Finset.insert_nonempty _ _
    have scaled (s : ℝ) (hs : 0 ≤ s) :
        s • sphereSupport T hT =
          sphereSupport {s • a, s • b, s • c} (Finset.insert_nonempty _ _) := by
      ext u
      have h := support_smul T hT (u : E) hs
      change s * support T hT (u : E) = support {s • a, s • b, s • c} (Finset.insert_nonempty _ _) (u : E)
      simpa [T, Finset.image_insert] using h.symm
    by_cases hr : 0 ≤ r
    · refine ⟨{r • a, r • b, r • c}, {0}, _, _, htri _ _ _, invariantUnder_zero D, ?_⟩
      rw [sphereSupport_zero, sub_zero]
      exact scaled r hr
    · refine ⟨{0}, {-r • a, -r • b, -r • c}, _, _, invariantUnder_zero D, htri _ _ _, ?_⟩
      rw [sphereSupport_zero, zero_sub, ← scaled (-r) (by linarith)]
      simp [T]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Triangle additivity identifies a support-Lipschitz price on the homogeneous
flat once the continuous triangle supports have dense linear span. -/
theorem price_eq_meanWidth_of_dense_triangleSupports
    (hdense : Dense (Submodule.span ℝ (triangleSupports E) : Set C(sphere (0 : E) 1, ℝ)))
    (δ : Finset E → ℝ)
    (htriangle : ∀ a b c : E, δ {a, b, c} = (dist a b + dist b c + dist c a) / 2)
    (hadd : ∀ (S : Finset E), S.Nonempty → ∀ a b c : E,
      δ (S + {a, b, c}) = δ S + δ {a, b, c})
    (hL : ∃ C : ℝ, ∀ ε > 0, ∀ S T : Finset E, ∀ hS : S.Nonempty, ∀ hT : T.Nonempty,
      (∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) →
        |δ S - δ T| ≤ C * ε)
    (S : Finset E) (hS : S.Nonempty) :
    δ S = meanWidth S hS := by
  let D (P : Finset E) (hP : P.Nonempty) := δ P - meanWidth P hP
  have tri (a b c : E) : InvariantUnder D {a, b, c} (Finset.insert_nonempty _ _) := by
    intro Q hQ
    simp only [D, hadd Q hQ, htriangle, meanWidth_add Q _ hQ (Finset.insert_nonempty _ _),
      meanWidth_triangle]
    ring
  have h0 : D {0} (Finset.singleton_nonempty _) = 0 := by
    have hp := htriangle (0 : E) 0 0
    have hw := meanWidth_triangle (0 : E) 0 0
    simp at hp hw
    simp [D, hp, hw]
  obtain ⟨C, hC⟩ := hL
  let A := Real.sqrt (2 * Real.pi) * ∫ u : E, ‖u‖ ∂stdGaussian E
  have hbound (ε : ℝ) (hε : 0 < ε) : |D S hS| ≤ (C + A) * ε := by
    obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp (hdense (sphereSupport S hS)) ε hε
    obtain ⟨P, M, hP, hM, p, m, rfl⟩ := span_difference_of_triangles D tri hg
    have hclose (u : E) (hu : u ∈ sphere (0 : E) 1) :
        |support (S + M) (hS.add hM) u - support P hP u| ≤ ε := by
      let v : sphere (0 : E) 1 := ⟨u, hu⟩
      rw [dist_eq_norm] at hd
      have h := ((sphereSupport S hS - (sphereSupport P hP - sphereSupport M hM)).norm_coe_le_norm v).trans hd.le
      change |support S hS u - (support P hP u - support M hM u)| ≤ ε at h
      rw [support_add S M hS hM]
      convert h using 2
      ring
    have hp : D P hP = 0 := by
      have h := (p {0} (Finset.singleton_nonempty _)).trans h0
      simpa only [show ({0} : Finset E) = 0 from rfl, zero_add] using h
    have hm := m S hS
    have hpclose := hC ε hε (S + M) P (hS.add hM) hP hclose
    have hwclose := abs_meanWidth_sub_le (S + M) P (hS.add hM) hP hclose
    calc
      |D S hS| = |(δ (S + M) - δ P) -
          (meanWidth (S + M) (hS.add hM) - meanWidth P hP)| := by
        rw [← hm]
        unfold D at hp ⊢
        congr 1
        linarith
      _ ≤ _ := by
        rw [add_mul]
        exact (abs_sub _ _).trans (add_le_add hpclose hwclose)
  have hz : |D S hS| ≤ 0 := by
    apply ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) (f := fun ε ↦ (C + A) * ε)
    · simpa using (tendsto_const_nhds (x := C + A)).mul
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun ε hε ↦ hbound ε hε
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

/-- For a homogeneous price, wire normalization and the half-perimeter upper
bound suffice for the flat diagonal law. The three edge segments of a triangle
sum to its difference body, forcing the upper bound to be attained. -/
theorem homogeneousFlatLaw_of_triangle_le
    (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsubmod : IntersectingSubmodular δ)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S)
    (hpair : ∀ a b : E, δ {a, b} = dist a b)
    (hupper : ∀ a b c : E, δ {a, b, c} ≤ (dist a b + dist b c + dist c a) / 2)
    (S : Finset E) (hS : S.Nonempty) :
    δ S = meanWidth S hS := by
  have hsingle (x : E) : δ {x} = 0 := by simpa using hpair x x
  have hsum := price_add_le_of_jointConvex δ hjoint hscale
  have htrans := price_translate_of_add_le δ hsum hsingle
  have hseg := price_add_segment δ hmono htrans hsubmod hsum hpair
  have htriangle (a b c : E) : δ {a, b, c} = (dist a b + dist b c + dist c a) / 2 := by
    apply le_antisymm (hupper a b c)
    have hab : ({0, b - a} : Finset E).Nonempty := Finset.insert_nonempty _ _
    have hbc : ({0, c - b} : Finset E).Nonempty := Finset.insert_nonempty _ _
    have hbody : δ (({a, b, c} : Finset E) + {-a, -b, -c}) =
        dist a b + dist b c + dist c a := by
      rw [triangle_add_neg_eq_segments, hseg _ (hab.add hbc), hseg _ hab, hpair]
      simp [dist_eq_norm']
    have hbound := hsum {a, b, c} {-a, -b, -c} (Finset.insert_nonempty _ _) (Finset.insert_nonempty _ _)
    rw [hbody] at hbound
    have hneg := hupper (-a) (-b) (-c)
    simp only [dist_neg_neg] at hneg
    linarith
  exact price_eq_meanWidth_of_dense_triangleSupports dense_span_triangleSupports δ htriangle
    (price_add_triangle δ hsum hseg htriangle)
    (exists_price_lipschitz_of_jointConvex δ hjoint hmono hscale) S hS

/-- The homogeneous case of the flat diagonal law follows from triangle density,
joint convexity, monotonicity, intersecting submodularity and the planar law. -/
theorem homogeneousFlatLaw
    (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsubmod : IntersectingSubmodular δ)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S)
    (htriangle : ∀ a b c : E, δ {a, b, c} = (dist a b + dist b c + dist c a) / 2)
    (S : Finset E) (hS : S.Nonempty) :
    δ S = meanWidth S hS := by
  apply homogeneousFlatLaw_of_triangle_le δ hjoint hmono hsubmod hscale _ _ S hS
  · intro a b
    simpa [dist_comm b a] using htriangle a b b
  · exact fun a b c ↦ (htriangle a b c).le

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.PatchContinuity
section

/-! # Continuity of the price of moving sites

An extra site can inherit a binary common label from any occupied site for the
cost of a single wire. Summing these relocation costs gives continuity even
when sites collide or approach the boundary of a convex patch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Classical Topology
section

variable {E ι : Type*} [PseudoMetricSpace E] {C : Set E}

private theorem patchPrice_sub_le (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, δ {x, y} = dist x y)
    (S : Finset ι) (hS : S.Nonempty) (x y : ι → E)
    (hx : ∀ i ∈ S, x i ∈ C) (hy : ∀ i ∈ S, y i ∈ C) :
    δ (S.image y) - δ (S.image x) ≤ ∑ i ∈ S, dist (x i) (y i) := by
  let B := S.image x
  have he : S.image y ⊆ B ∪ S.image y := Finset.subset_union_right
  have hupper := (hmono (hS.image _) he).trans
    (conditioning_union_image_le_of_nonempty hmono hsub (hS.image x) S y)
  refine (sub_le_iff_le_add'.mpr hupper).trans (Finset.sum_le_sum fun i hi => ?_)
  have hxi : {x i} ⊆ B := Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ hi)
  have hsingle : δ {x i} = 0 := by simpa using hpair _ (hx i hi) _ (hx i hi)
  have h := price_increment_le_of_subset δ hmono hsub (Finset.singleton_nonempty _) hxi (y i)
  simpa only [hpair _ (hy i hi) _ (hx i hi), hsingle, sub_zero, dist_comm (y i)] using h

/-- Transport bound for a list of sites moving within the patch, with repetitions allowed. -/
theorem patchPrice_dist_le (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, δ {x, y} = dist x y)
    (S : Finset ι) (hS : S.Nonempty) (x y : ι → E)
    (hx : ∀ i ∈ S, x i ∈ C) (hy : ∀ i ∈ S, y i ∈ C) :
    dist (δ (S.image x)) (δ (S.image y)) ≤ ∑ i ∈ S, dist (x i) (y i) := by
  rw [Real.dist_eq, abs_le]
  constructor
  · linarith [patchPrice_sub_le δ hmono hsub hpair S hS x y hx hy]
  · simpa only [dist_comm] using patchPrice_sub_le δ hmono hsub hpair S hS y x hy hx

/-- A finite configuration moving continuously in a patch has a continuous diagonal price. -/
theorem continuousOn_price_image {A : Type*} [TopologicalSpace A] {I : Set A}
    (δ : Finset E → ℝ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, δ {x, y} = dist x y)
    (S : Finset ι) (hS : S.Nonempty) (f : ι → A → E)
    (hC : ∀ i ∈ S, ∀ t ∈ I, f i t ∈ C) (hf : ∀ i ∈ S, ContinuousOn (f i) I) :
    ContinuousOn (fun t => δ (S.image fun i => f i t)) I := by
  intro t ht
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (g := fun s => ∑ i ∈ S, dist (f i s) (f i t))
    (.of_forall fun _ => dist_nonneg)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact patchPrice_dist_le δ hmono hsub hpair S hS (fun i => f i s) (fun i => f i t)
      (fun i hi => hC i hi s hs) (fun i hi => hC i hi t ht)
  · simpa using tendsto_finsetSum S (fun i hi => tendsto_iff_dist_tendsto_zero.mp (hf i hi t ht))

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.PatchHull
section

/-! # Finite convex hulls inside a patch

Keeping all occupied sites fixed and moving one extra index along a straight
segment yields the convexity of its price sublevel within the patch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    {δ : Finset E → ℝ}

theorem JointlyConvexPriceOn.price_insert_of_mem_convexHull (hj : JointlyConvexPriceOn C δ)
    (hc : Convex ℝ C)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → (T : Set E) ⊆ C → δ S ≤ δ T)
    (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C)
    {z : E} (hz : z ∈ convexHull ℝ (S : Set E)) : δ (insert z S) = δ S := by
  have hzC := convexHull_min hSC hc hz
  have hsub : (↑(insert z S) : Set E) ⊆ C := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hzC hSC
  refine le_antisymm ?_ (hmono hS (Finset.subset_insert _ _) hsub)
  let L := {w : E | δ (insert w S) ≤ δ S}
  have hSL : (S : Set E) ⊆ C ∩ L := fun x hx ↦ ⟨hSC hx, by simp [L, Finset.insert_eq_of_mem hx]⟩
  suffices hCL : Convex ℝ (C ∩ L) from (convexHull_min hSL hCL hz).2
  intro x hx y hy a b ha hb hab
  refine ⟨hc hx.1 hy.1 ha hb hab, ?_⟩
  let P := S.image (fun s ↦ (s, s))
  have hin : ∀ p ∈ insert (x,y) P, p.1 ∈ C ∧ p.2 ∈ C := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hx.1, hy.1⟩
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hSC hs, hSC hs⟩
  have h := hj (insert (x,y) P) (Finset.insert_nonempty _ _) hin a b ha hb hab
  have hid (s : E) : a • s + b • s = s := by rw [← add_smul, hab, one_smul]
  simp [P, Finset.image_image, Function.comp_def, hid] at h
  change δ (insert (a • x + b • y) S) ≤ δ S
  calc
    _ ≤ a * δ (insert x S) + b * δ (insert y S) := h
    _ ≤ a * δ S + b * δ S := add_le_add
      (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

theorem JointlyConvexPriceOn.price_union_of_subset_convexHull (hj : JointlyConvexPriceOn C δ)
    (hc : Convex ℝ C)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → (T : Set E) ⊆ C → δ S ≤ δ T)
    (S T : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) : δ (S ∪ T) = δ S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert z T hz ih =>
    have hT' : (T : Set E) ⊆ convexHull ℝ (S : Set E) :=
      fun _ hy ↦ hT (Finset.mem_insert_of_mem hy)
    have hsub : (S : Set E) ⊆ ↑(S ∪ T) := Finset.subset_union_left
    have hUC : (↑(S ∪ T) : Set E) ⊆ C := by
      simpa only [Finset.coe_union] using Set.union_subset hSC (hT'.trans (convexHull_min hSC hc))
    rw [Finset.union_insert, hj.price_insert_of_mem_convexHull hc hmono _
      (hS.mono Finset.subset_union_left) hUC (convexHull_mono hsub (hT (Finset.mem_insert_self z T))),
      ih hT']

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.TangentProperties
section

/-! # Structural properties of tangent diagonal prices

Blowing up a patch at an interior point preserves its finite price
inequalities and makes the limiting price homogeneous.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open Filter
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    {δ D : Finset E → ℝ} {y : E}

theorem IsTangentPriceAt.monotone (ht : IsTangentPriceAt δ y D) (hy : y ∈ interior C)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → (T : Set E) ⊆ C → δ S ≤ δ T)
    ⦃S T : Finset E⦄ (hS : S.Nonempty) (hST : S ⊆ T) : D S ≤ D T := by
  apply le_of_tendsto_of_tendsto (ht S hS) (ht T (hS.mono hST))
  filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy T] with h (hh : 0 < h) hTC
  apply div_le_div_of_nonneg_right _ hh.le
  exact hmono (hS.image _) (Finset.image_subset_image hST) hTC

theorem IsTangentPriceAt.intersectingSubmodular (ht : IsTangentPriceAt δ y D)
    (hy : y ∈ interior C)
    (hsubmod : ∀ ⦃A B : Finset E⦄, (A : Set E) ⊆ C → (B : Set E) ⊆ C → (A ∩ B).Nonempty →
      δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B) :
    IntersectingSubmodular D := by
  intro A B hI
  have hA := hI.mono Finset.inter_subset_left
  have hB := hI.mono Finset.inter_subset_right
  have hU := hA.mono (Finset.subset_union_left (s₂ := B))
  apply le_of_tendsto_of_tendsto ((ht _ hU).add (ht _ hI)) ((ht _ hA).add (ht _ hB))
  filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy A,
    eventually_patch_image_subset hy B] with h (hh : 0 < h) hAC hBC
  let g := fun x : E ↦ y + h • x
  have hinj : Function.Injective g := (add_right_injective y).comp (smul_right_injective E hh.ne')
  have heq := Finset.image_inter A B hinj
  have hsub := hsubmod hAC hBC (heq ▸ hI.image g)
  simp only [← add_div]
  apply div_le_div_of_nonneg_right _ hh.le
  change δ ((A ∪ B).image g) + δ ((A ∩ B).image g) ≤ _
  rw [Finset.image_union, heq]
  exact hsub

theorem IsTangentPriceAt.jointlyConvex (ht : IsTangentPriceAt δ y D)
    (hy : y ∈ interior C) (hj : JointlyConvexPriceOn C δ) : JointlyConvexPrice D := by
  intro P hP a b ha hb hab
  let M (p : E × E) := a • p.1 + b • p.2
  apply le_of_tendsto_of_tendsto (ht (P.image M) (hP.image _))
    (((ht (P.image Prod.fst) (hP.image _)).const_mul a).add
      ((ht (P.image Prod.snd) (hP.image _)).const_mul b))
  filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy (P.image Prod.fst),
    eventually_patch_image_subset hy (P.image Prod.snd)] with h (hh : 0 < h) h₁ h₂
  let g := fun x : E ↦ y + h • x
  let mapPair := fun p : E × E ↦ (g p.1, g p.2)
  have hin : ∀ p ∈ P.image mapPair, p.1 ∈ C ∧ p.2 ∈ C := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨h₁ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq)),
      h₂ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq))⟩
  have hineq := hj (P.image mapPair) (hP.image _) hin a b ha hb hab
  have hmap (p : E × E) : a • (g p.1) + b • (g p.2) = g (M p) := by
    dsimp [g, M]
    rw [smul_add, smul_add, smul_add, smul_comm a h, smul_comm b h]
    calc
      _ = (a • y + b • y) + (h • a • p.1 + h • b • p.2) := by abel
      _ = _ := by rw [← add_smul, hab, one_smul]
  simp only [Finset.image_image, Function.comp_def, mapPair, hmap] at hineq
  change δ ((P.image M).image g) / _ ≤ a * (δ ((P.image Prod.fst).image g) / _) +
    b * (δ ((P.image Prod.snd).image g) / _)
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ hh.le
  simpa only [Finset.image_image, Function.comp_def] using hineq

theorem IsTangentPriceAt.homogeneous (ht : IsTangentPriceAt δ y D)
    (S : Finset E) (hS : S.Nonempty) (t : ℝ) (htpos : 0 < t) :
    D (S.image (t • ·)) = t * D S := by
  have hlim := tangentPrice_rescale (f := fun h : ℝ ↦ δ (S.image fun x ↦ y + h • x))
    (ht S hS) htpos
  apply tendsto_nhds_unique (ht _ (hS.image _))
  simpa only [Finset.image_image, Function.comp_def, smul_smul, mul_comm t] using hlim

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- OAI.LinearAlgebra.SpectralBooks.CenteredFlatLaw
section

/-! # Diagonal prices in a convex Euclidean patch

Rescale the finite price inequalities directly at an interior point. Their
limits have the homogeneous flat law, and the normal-cone estimates integrate
these local price identities along dilations of the configuration.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter Set
open scoped Topology Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {C : Set E} {δ : Finset E → ℝ}

/-- At every interior point the tangent price exists and is normalized mean width. -/
theorem DiagonalPriceLawsOn.hasTangentMeanWidth (H : DiagonalPriceLawsOn C δ) {y : E}
    (hy : y ∈ interior C) : HasTangentMeanWidth δ y := by
  obtain ⟨D, hD⟩ := exists_tangentPriceAt H.jointlyConvex hy (H.singleton (interior_subset hy))
    H.nonneg
  have hpair (a b : E) : D {a,b} = dist a b := by
    have hAB : ({a,b} : Finset E).Nonempty := Finset.insert_nonempty _ _
    apply tendsto_nhds_unique (hD _ hAB)
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy {a,b}]
      with h (hh : 0 < h) hsub
    have hmem (x : E) (hx : x ∈ ({a,b} : Finset E)) := hsub (Finset.mem_image_of_mem _ hx)
    simp only [Finset.image_insert, Finset.image_singleton, H.wire _ (hmem a (by simp)) _ (hmem b (by simp)),
      dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hh]
    field_simp
  have htriangle (a b c : E) : D {a,b,c} ≤ (dist a b + dist b c + dist c a) / 2 := by
    have hABC : ({a,b,c} : Finset E).Nonempty := Finset.insert_nonempty _ _
    apply le_of_tendsto (hD _ hABC)
    filter_upwards [self_mem_nhdsWithin, eventually_patch_image_subset hy {a,b,c}]
      with h (hh : 0 < h) hsub
    have hmem (x : E) (hx : x ∈ ({a,b,c} : Finset E)) := hsub (Finset.mem_image_of_mem _ hx)
    have htri := H.triangle_le _ (hmem a (by simp)) _ (hmem b (by simp)) _ (hmem c (by simp))
    simp only [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hh] at htri
    simp only [Finset.image_insert, Finset.image_singleton, div_le_iff₀ hh]
    linarith only [htri]
  intro S hS
  have hflat := homogeneousFlatLaw_of_triangle_le D (hD.jointlyConvex hy H.jointlyConvex)
    (fun _ _ hne hst ↦ hD.monotone hy (fun _ _ _ h _ ↦ H.monotone h) hne hst)
    (hD.intersectingSubmodular hy (fun _ _ _ _ hab ↦ H.submodular hab)) hD.homogeneous hpair htriangle S hS
  rw [← hflat]
  exact hD S hS

/-- The flat diagonal law with the origin chosen in the relative interior and
adjoined to the finite set of sites. -/
theorem centeredFlatDiagonalLaw (H : DiagonalPriceLawsOn C δ) (hC : Convex ℝ C)
    (h0int : (0 : E) ∈ interior C) (S : Finset E) (hS0 : 0 ∈ S) (hSC : (S : Set E) ⊆ C) :
    δ S = meanWidth S ⟨0,hS0⟩ := by
  have hS : S.Nonempty := ⟨0, hS0⟩
  have hl (t : ℝ) (ht : t ∈ Icc 0 1) (x : E) (hx : x ∈ S) : t • x ∈ C := by
    simpa using hC (interior_subset h0int) (hSC hx)
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  apply flatDiagonalLaw_of_tangentMeanWidth δ H.monotone H.submodular hS0
    (H.singleton (interior_subset h0int))
  · intro t ht T hT
    refine H.jointlyConvex.price_union_of_subset_convexHull hC (fun _ _ _ h _ ↦ H.monotone h)
      _ T (hS.image _) ?_ hT
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact hl t (Ioo_subset_Icc_self ht) x hx
  · simpa using H.jointlyConvex.convexOn_dilation S hS 0 (convex_Icc (0 : ℝ) 1)
      (fun t ht x hx ↦ by simpa using hl t ht x hx)
  · exact continuousOn_price_image δ (fun _ _ _ h ↦ H.monotone h) H.submodular
      (fun _ hx _ hy ↦ H.pair hx hy) S hS (fun x t ↦ t • x)
      (fun x hx t ht ↦ hl t ht x hx) (by fun_prop)
  · intro t ht v hv
    apply H.hasTangentMeanWidth
    simpa using hC.combo_interior_self_mem_interior h0int (hSC hv)
      (sub_pos.mpr ht.2) ht.1 (sub_add_cancel 1 t)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end
-- FlatLaw
section

/-! # The flat diagonal law on an arbitrary convex Euclidean patch -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set
open scoped Classical RealInnerProductSpace
noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- On every convex Euclidean patch satisfying the diagonal price laws, the
price of a nonempty finite configuration equals its normalized Gaussian mean width. -/
theorem flatDiagonalLaw {C : Set E} {δ : Finset E → ℝ} (H : DiagonalPriceLawsOn C δ)
    (hC : Convex ℝ C) (S : Finset E) (hS : S.Nonempty) (hSC : (S : Set E) ⊆ C) :
    δ S = meanWidth S hS := by
  let K := convexHull ℝ (S : Set E)
  have hSK : (S : Set E) ⊆ K := subset_convexHull ℝ (S : Set E)
  have hKC : K ⊆ C := convexHull_min hSC hC
  obtain ⟨i, hrange, hint⟩ := exists_centered_affinePatch (convex_convexHull ℝ (S : Set E))
    (hS.to_set.mono hSK)
  let P := S.preimage i i.injective.injOn
  have himage : P.image i = S := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.mpr fun _ hx ↦ hrange (hSK hx)
  have h0K : (0 : (affineSpan ℝ K).direction) ∈ i ⁻¹' K := interior_subset hint
  have hup : (↑(insert 0 P) : Set (affineSpan ℝ K).direction) ⊆ i ⁻¹' C := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hKC h0K
    · exact hSC (Finset.mem_preimage.mp hx)
  have hh := centeredFlatDiagonalLaw (H.comp_affineIsometry i) (hC.affine_preimage i.toAffineMap)
    (interior_mono (Set.preimage_mono hKC) hint) (insert 0 P) (Finset.mem_insert_self _ _) hup
  have hi : (insert 0 P).image i = insert (i 0) S := by rw [Finset.image_insert, himage]
  have hprice := H.jointlyConvex.price_insert_of_mem_convexHull hC
    (fun _ _ _ h _ ↦ H.monotone h) S hS hSC h0K
  calc
    δ S = δ ((insert 0 P).image i) := by rw [hi, hprice]
    _ = meanWidth (insert 0 P) (Finset.insert_nonempty _ _) := hh
    _ = meanWidth ((insert 0 P).image i) ((Finset.insert_nonempty _ _).image _) :=
      (meanWidth_affineIsometry i _ (Finset.insert_nonempty _ _)).symm
    _ = meanWidth S hS := by
      have hmem : (({i 0} : Finset E) : Set E) ⊆ K := by
        simp only [Finset.coe_singleton, Set.singleton_subset_iff]
        exact h0K
      simpa only [hi, Finset.union_singleton] using meanWidth_union_of_subset_convexHull hS hmem

end

end SpectralBooks
end LinearAlgebra
end OAI

end
-- H3Adapter
section

open OAI.LinearAlgebra.SpectralBooks

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1.H3 := by
  intro δ hmono hsub hconv hwire htri S hS
  have H : DiagonalPriceLawsOn (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) δ :=
    { monotone := hmono
      submodular := fun A B h => by
        convert hsub A B (by convert h using 1 <;> congr!) using 0 <;> congr!
      jointlyConvex := fun P _ _ a b ha hb hab => by convert hconv P a b ha hb hab using 0 <;> congr!
      wire := fun a _ b _ => by convert hwire a b using 0 <;> congr!
      triangle_le := fun a _ b _ c _ => by convert htri a b c using 0 <;> congr! }
  exact flatDiagonalLaw H convex_univ S hS (Set.subset_univ _)

end
