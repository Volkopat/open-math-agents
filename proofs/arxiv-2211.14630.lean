import OMAStatements.S_arxiv_2211_14630
/- Embedding adapted from https://github.com/openai/math (OpenAI); modified for Lean 4.33.1 and combined with a volume argument, Apache-2.0, revision 3344da59991ed94f9ba711217b29c1d760badfa6. -/

section
-- OAI.Geometry.PolarProducts.Model


namespace OAI

section
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar

abbrev Position (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Phase (n : ℕ) := Position n × Position n

def IsSymmetricConvexBody {n : ℕ} (K : Set (Position n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty ∧
    ∀ x, x ∈ K ↔ -x ∈ K

def polar {n : ℕ} (K : Set (Position n)) : Set (Position n) :=
  {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}

def polarProduct {n : ℕ} (K : Set (Position n)) : Set (Phase n) :=
  interior K ×ˢ interior (polar K)

def capacityBall (n : ℕ) (c : ℝ) : Set (Phase n) :=
  {z | Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) < c}

noncomputable def omega0 {n : ℕ} (v w : Phase n) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2 - inner (𝕜 := ℝ) w.1 v.2

def HasSymplecticEmbedding {n : ℕ} (U V : Set (Phase n)) : Prop :=
  ∃ e : Phase n → Phase n,
    ContDiffOn ℝ ∞ e U ∧
    Topology.IsEmbedding (fun z : U => e z) ∧
    MapsTo e U V ∧
    ∀ z ∈ U, ∀ v w : Phase n,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w

noncomputable def gromovWidth {n : ℕ} (U : Set (Phase n)) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {c : ℝ | 0 < c ∧ HasSymplecticEmbedding (capacityBall n c) U})

end SymmetricPolar
end

end OAI

end

section
-- OAI.Geometry.PolarProducts.Contraction


namespace OAI

universe u1 u2

section LowerBoundInline

open Set Filter Function
open scoped Topology ContDiff NNReal

namespace SmoothContraction

variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable section

def fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) : F :=
  ContractingWith.fixedPoint (fun y => f (x, y)) ⟨hL, hLip x⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ F] in
theorem fixedPoint_eq {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) :
    f (x, fixedPoint hL hLip x) = fixedPoint hL hLip x :=
  (show ContractingWith L (fun y => f (x, y)) from ⟨hL, hLip x⟩).fixedPoint_isFixedPt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedSpace ℝ F] in
theorem eq_fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hL : L < 1) (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (x : E) {y : F}
    (hy : f (x, y) = y) : y = fixedPoint hL hLip x :=
  (show ContractingWith L (fun y => f (x, y)) from ⟨hL, hLip x⟩).fixedPoint_unique hy

omit [CompleteSpace E] in

theorem partial_isInvertible {f : E × F → F} {L : ℝ≥0}
    (hf : Differentiable ℝ f) (hL : L < 1)
    (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) (u : E × F) :
    ((fderiv ℝ (fun p : E × F => p.2 - f p) u).comp
      (ContinuousLinearMap.inr ℝ E F)).IsInvertible := by
  let A := (fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ E F)
  have hA : HasFDerivAt (fun y => f (u.1, y)) A u.2 :=
    (hf u).hasFDerivAt.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
  have hnorm : ‖A‖ < 1 := by
    rw [← hA.fderiv]
    exact (norm_fderiv_le_of_lipschitz ℝ (hLip u.1)).trans_lt (by exact_mod_cast hL)
  have heq : (fderiv ℝ (fun p : E × F => p.2 - f p) u).comp
      (ContinuousLinearMap.inr ℝ E F) = 1 - A := by
    change (fderiv ℝ (Prod.snd - f) u).comp _ = _
    rw [(hasFDerivAt_snd.sub (hf u).hasFDerivAt).fderiv]
    ext y
    simp [A]
  rw [heq]
  obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩

theorem contDiff_fixedPoint {f : E × F → F} {L : ℝ≥0}
    (hf : ContDiff ℝ ∞ f) (hL : L < 1)
    (hLip : ∀ x, LipschitzWith L (fun y => f (x, y))) :
    ContDiff ℝ ∞ (fixedPoint hL hLip) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let y := fixedPoint hL hLip x
  let g : E × F → F := fun p => p.2 - f p
  have hg : ContDiffAt ℝ ∞ g (x, y) := (contDiff_snd.sub hf).contDiffAt
  have hi := partial_isInvertible (hf.differentiable (by simp)) hL hLip (x, y)
  let ψ := hg.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ x := hg.contDiffAt_implicitFunction (by simp) hi
  have hzero : g (x, y) = 0 := sub_eq_zero.mpr (fixedPoint_eq hL hLip x).symm
  have hnear : ψ =ᶠ[𝓝 x] fixedPoint hL hLip := by
    filter_upwards [hg.eventually_apply_implicitFunction (by simp) hi] with x' hx'
    apply eq_fixedPoint hL hLip x'
    have : g (x', ψ x') = 0 := hx'.trans hzero
    exact (sub_eq_zero.mp this).symm
  exact hψ.congr_of_eventuallyEq hnear.symm

end
end SmoothContraction

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.SmoothPaths


namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal

open Set Filter Metric
open scoped Topology ContDiff

namespace SmoothPaths

universe u v

variable {X : Type v} {E F : Type u} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

def applyField (A : C(X, E →L[ℝ] F)) : C(X, E) →L[ℝ] C(X, F) := by
  let L : C(X, E) →ₗ[ℝ] C(X, F) :=
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply L.mkContinuous ‖A‖
  intro u
  apply (ContinuousMap.norm_le (L u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

@[simp] theorem applyField_apply (A : C(X, E →L[ℝ] F)) (u : C(X, E)) (t : X) :
    applyField A u t = A t (u t) := rfl

def applyFieldCLM : C(X, E →L[ℝ] F) →L[ℝ] C(X, E) →L[ℝ] C(X, F) := by
  let L : C(X, E →L[ℝ] F) →ₗ[ℝ] (C(X, E) →L[ℝ] C(X, F)) :=
    { toFun := fun A => applyField A
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hL : ∀ A : C(X, E →L[ℝ] F), ‖L A‖ ≤ 1 * ‖A‖ := by
    intro A
    rw [one_mul]
    apply (applyField A).opNorm_le_bound (norm_nonneg A)
    intro u
    apply (ContinuousMap.norm_le (applyField A u)
      (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
    intro t
    exact ((A t).le_opNorm (u t)).trans
      (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))
  exact LinearMap.mkContinuous (σ := RingHom.id ℝ)
    (E := C(X, E →L[ℝ] F)) (F := C(X, E) →L[ℝ] C(X, F)) L 1 hL

@[simp] theorem applyFieldCLM_apply (A : C(X, E →L[ℝ] F)) :
    applyFieldCLM A = applyField A := rfl

def superpose {f : E → F} (hf : Continuous f) (u : C(X, E)) : C(X, F) :=
  ⟨fun t => f (u t), hf.comp u.continuous⟩

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem superpose_apply {f : E → F} (hf : Continuous f)
    (u : C(X, E)) (t : X) : superpose hf u t = f (u t) := rfl

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_superpose {f : E → F} (hf : Continuous f) :
    Continuous (superpose (X := X) hf) :=
  ContinuousMap.continuous_postcomp ⟨f, hf⟩

theorem hasFDerivAt_superpose [ProperSpace E] {f : E → F}
    (hf : Differentiable ℝ f) (hf' : Continuous (fderiv ℝ f)) (u : C(X, E)) :
    HasFDerivAt (superpose hf.continuous)
      (applyField (superpose hf' u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc : UniformContinuousOn (fderiv ℝ f) (closedBall (0 : E) (‖u‖ + 2)) :=
    (isCompact_closedBall (0 : E) (‖u‖ + 2)).uniformContinuousOn_of_continuous hf'.continuousOn
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(X, E)) (lt_min hδ zero_lt_one)] with h hh
  have hhδ : ‖h‖ < δ := (mem_ball_zero_iff.mp hh).trans_le (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := (mem_ball_zero_iff.mp hh).trans_le (min_le_right _ _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have hu : ‖u t‖ ≤ ‖u‖ := u.norm_coe_le_norm t
  have hsmall : ‖h t‖ < δ := (h.norm_coe_le_norm t).trans_lt hhδ
  have hsmall1 : ‖h t‖ < 1 := (h.norm_coe_le_norm t).trans_lt hh1
  have hut : u t ∈ closedBall (0 : E) (‖u‖ + 2) := by
    rw [mem_closedBall_zero_iff]; linarith
  have hall : ∀ y ∈ ball (u t) (min δ 1),
      ‖fderiv ℝ f y - fderiv ℝ f (u t)‖ ≤ ε := by
    intro y hy
    have hdist : dist y (u t) < δ := hy.trans_le (min_le_left _ _)
    have hdist1 : dist y (u t) < 1 := hy.trans_le (min_le_right _ _)
    have hyball : y ∈ closedBall (0 : E) (‖u‖ + 2) := by
      rw [mem_closedBall_zero_iff]
      have hn := norm_le_norm_sub_add y (u t)
      rw [← dist_eq_norm] at hn
      linarith
    exact le_of_lt (by simpa only [dist_eq_norm] using hbound y hyball (u t) hut hdist)
  have hu0 : u t ∈ ball (u t) (min δ 1) := mem_ball_self (lt_min hδ zero_lt_one)
  have huh : u t + h t ∈ ball (u t) (min δ 1) := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_min hsmall hsmall1
  have he := (convex_ball (u t) (min δ 1)).norm_image_sub_le_of_norm_fderiv_le'
    (fun _ _ => hf _) hall hu0 huh
  simp only [add_sub_cancel_left] at he
  exact he.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hε.le)

theorem contDiff_superpose_nat [ProperSpace E] (n : ℕ) {f : E → F}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (superpose (X := X) hf.continuous) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (continuous_superpose hf.continuous)
  | succ n ih =>
    have hn : (↑(n + 1) : WithTop ℕ∞) ≠ 0 := by simp
    have hd : Differentiable ℝ f := hf.differentiable hn
    have hcd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hc : ContDiff ℝ n (fun u : C(X, E) => applyField (superpose hcd.continuous u)) :=
      by simpa only [Function.comp_def, applyFieldCLM_apply] using
        (applyFieldCLM (X := X) (E := E) (F := F)).contDiff.comp (ih hcd)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨_, hc, hasFDerivAt_superpose hd hcd.continuous⟩

theorem contDiff_superpose [ProperSpace E] {f : E → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (superpose (X := X) hf.continuous) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_superpose_nat n (contDiff_infty.mp hf n)

end
end SmoothPaths

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.LocalODE


namespace OAI

universe u3 u4 u5 u6

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

abbrev Time := Icc (0 : ℝ) 1

variable {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

def extend (u : C(Time, E)) : ℝ → E := fun t => u (projIcc 0 1 zero_le_one t)

omit [NormedSpace ℝ E] in
theorem continuous_extend (u : C(Time, E)) : Continuous (extend u) :=
  u.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] in
@[simp] theorem extend_coe (u : C(Time, E)) (t : Time) : extend u t = u t := by
  simp [extend]

def primitive (u : C(Time, E)) : C(Time, E) :=
  ⟨fun t => ∫ s in 0..(t : ℝ), extend u s,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_extend u).intervalIntegrable a b) 0).comp continuous_subtype_val⟩

@[simp] theorem primitive_apply (u : C(Time, E)) (t : Time) :
    primitive u t = ∫ s in 0..(t : ℝ), extend u s := rfl

theorem norm_primitive_le (u : C(Time, E)) : ‖primitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := ‖u‖)
    (fun s _ => u.norm_coe_le_norm (projIcc 0 1 zero_le_one s))
  change ‖∫ s in 0..(t : ℝ), extend u s‖ ≤ ‖u‖
  refine h.trans ?_
  rw [sub_zero, abs_of_nonneg t.2.1]
  exact mul_le_of_le_one_right (norm_nonneg _) t.2.2

def primitiveCLM : C(Time, E) →L[ℝ] C(Time, E) := by
  let L : C(Time, E) →ₗ[ℝ] C(Time, E) :=
    { toFun := primitive
      map_add' := by
        intro u v
        ext t
        change (∫ s in 0..(t : ℝ), extend u s + extend v s) = _
        exact intervalIntegral.integral_add
          ((continuous_extend u).intervalIntegrable _ _)
          ((continuous_extend v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        exact intervalIntegral.integral_smul c (extend u) }
  exact L.mkContinuous 1 (by
    intro u
    change ‖primitive u‖ ≤ 1 * ‖u‖
    simpa using norm_primitive_le u)

@[simp] theorem primitiveCLM_apply (u : C(Time, E)) : primitiveCLM u = primitive u := rfl

theorem primitiveCLM_norm_le : ‖primitiveCLM (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_primitive_le u

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u4} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

def picard {V : E → E} (hV : Continuous V) (h : ℝ) (x : E)
    (u : C(Time, E)) : C(Time, E) :=
  ContinuousMap.const Time x + h • primitive (SmoothPaths.superpose hV u)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem lipschitz_superpose {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) :
    LipschitzWith K (SmoothPaths.superpose (X := Time) hV.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  apply (ContinuousMap.dist_le (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro t
  exact (hV.dist_le_mul (u t) (v t)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist (f := u) (g := v) t) K.coe_nonneg)

omit [CompleteSpace E] in
theorem lipschitz_picard {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (x : E) : LipschitzWith (‖h‖₊ * K) (picard hV.continuous h x) := by
  have hp : LipschitzWith 1 (primitive (E := E)) := by
    change LipschitzWith 1 (primitiveCLM (E := E))
    exact ContinuousLinearMap.opNorm_le_iff_lipschitz.mp primitiveCLM_norm_le
  have hi := (lipschitzWith_smul h).comp (hp.comp (lipschitz_superpose hV))
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa [picard] using hi.dist_le_mul u v

omit [CompleteSpace E] in

theorem contDiff_picard [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V) (h : ℝ) :
    ContDiff ℝ ∞ (fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : E × C(Time, E) => ContinuousMap.const Time p.1) :=
    (ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)).contDiff.comp contDiff_fst
  have hp : ContDiff ℝ ∞ (fun p : E × C(Time, E) =>
      primitive (SmoothPaths.superpose hV.continuous p.2)) :=
    primitiveCLM.contDiff.comp ((SmoothPaths.contDiff_superpose hV).comp contDiff_snd)
  exact hc.add (hp.const_smul h)

def trajectory {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : C(Time, E) :=
  SmoothContraction.fixedPoint (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) hh (lipschitz_picard hV h) x

theorem trajectory_eq {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    picard hV.continuous h x (trajectory hV h hh x) = trajectory hV h hh x :=
  SmoothContraction.fixedPoint_eq (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) hh (lipschitz_picard hV h) x

theorem contDiff_trajectory [ProperSpace E] {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) :
    ContDiff ℝ ∞ (trajectory hV h hh) :=
  SmoothContraction.contDiff_fixedPoint (f := fun p : E × C(Time, E) => picard hV.continuous h p.1 p.2) (contDiff_picard hVs h) hh (lipschitz_picard hV h)

def curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : ℝ) : E :=
  x + h • ∫ s in 0..t, V (extend (trajectory hV h hh x) s)

@[simp] theorem curve_coe {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : Time) :
    curve hV h hh x t = trajectory hV h hh x t :=
  congrArg (fun u : C(Time, E) => u t) (trajectory_eq hV h hh x)

@[simp] theorem curve_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : curve hV h hh x 0 = x := by
  simp [curve]

theorem continuous_curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : Continuous (curve hV h hh x) := by
  have hc := hV.continuous.comp (continuous_extend (trajectory hV h hh x))
  exact continuous_const.add
    ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).const_smul h)

theorem hasDerivAt_curve {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (t : Time) :
    HasDerivAt (curve hV h hh x) (h • V (curve hV h hh x t)) (t : ℝ) := by
  have hc := hV.continuous.comp (continuous_extend (trajectory hV h hh x))
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 (t : ℝ)))
      hc.continuousAt
  rw [curve_coe]
  change HasDerivAt (fun s : ℝ =>
    x + h • ∫ r in 0..s, V (extend (trajectory hV h hh x) r)) _ (t : ℝ)
  simpa only [Pi.smul_apply, Function.comp_apply, extend_coe] using
    (hd.const_smul h).const_add x

def step {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : E :=
  trajectory hV h hh x ⟨1, by constructor <;> norm_num⟩

theorem contDiff_step [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) : ContDiff ℝ ∞ (step hV h hh) :=
  (ContinuousMap.evalCLM ℝ (M := E) (⟨1, by constructor <;> norm_num⟩ : Time)).contDiff.comp
    (contDiff_trajectory hV hVs h hh)

@[simp] theorem curve_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) : curve hV h hh x 1 = step hV h hh x :=
  curve_coe hV h hh x ⟨1, by constructor <;> norm_num⟩

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

theorem curve_unique {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 1))
    (hf' : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f (h • V (f t)) (Ici t) t)
    (h0 : f 0 = x) : EqOn f (curve hV h hh x) (Icc 0 1) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ y => h • V y) (s := fun _ => univ)
    (K := ‖h‖₊ * K)
  · intro _ _
    exact ((lipschitzWith_smul h).comp hV).lipschitzOnWith
  · exact hf
  · exact hf'
  · intro _ _; trivial
  · exact (continuous_curve hV h hh x).continuousOn
  · intro t ht
    exact (hasDerivAt_curve hV h hh x ⟨t, ht.1, ht.2.le⟩).hasDerivWithinAt
  · intro _ _; trivial
  · simpa using h0

theorem curve_reverse {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    EqOn (fun t => curve hV h hh x (1 - t))
      (curve hV (-h) (by simpa using hh) (step hV h hh x)) (Icc 0 1) := by
  apply curve_unique hV (-h) (by simpa using hh) (step hV h hh x)
  · exact ((continuous_curve hV h hh x).comp (continuous_const.sub continuous_id)).continuousOn
  · intro t ht
    have hr : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hd := (hasDerivAt_curve hV h hh x ⟨1 - t, hr⟩).scomp t
      ((hasDerivAt_id t).const_sub 1)
    have he : HasDerivAt (fun t => curve hV h hh x (1 - t))
        ((-h) • V (curve hV h hh x (1 - t))) t := by
      simpa only [Function.comp_def, id_eq, neg_smul, one_smul] using hd
    exact he.hasDerivWithinAt
  · simp

theorem step_neg_step {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    step hV (-h) (by simpa using hh) (step hV h hh x) = x := by
  have he := curve_reverse hV h hh x (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he.symm

def stepHomeomorph [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) : E ≃ₜ E where
  toFun := step hV h hh
  invFun := step hV (-h) (by simpa using hh)
  left_inv := step_neg_step hV h hh
  right_inv x := by
    simpa only [neg_neg] using step_neg_step hV (-h) (by simpa using hh) x
  continuous_toFun := (contDiff_step hV hVs h hh).continuous
  continuous_invFun := (contDiff_step hV hVs (-h) (by simpa using hh)).continuous

@[simp] theorem stepHomeomorph_apply [ProperSpace E] {V : E → E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) :
    stepHomeomorph hV hVs h hh x = step hV h hh x := rfl

theorem curve_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    EqOn (curve hV h hh x) (fun _ => x) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x continuousOn_const
  · intro t _
    simpa only [hx, smul_zero] using (hasDerivWithinAt_const t (Ici t) x)
  · rfl

@[simp] theorem step_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    step hV h hh x = x := by
  have he := curve_of_eq_zero hV h hh x hx (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u6} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

def tangentPath {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) : C(Time, E) :=
  fderiv ℝ (trajectory hV h hh) x v

theorem tangentPath_eq {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    tangentPath hV h hh x v =
      ContinuousMap.const Time v + h • primitive
        (SmoothPaths.applyField
          (SmoothPaths.superpose (hVs.continuous_fderiv (by simp)) (trajectory hV h hh x))
          (tangentPath hV h hh x v)) := by
  let Q := trajectory hV h hh
  let DQ := fderiv ℝ Q x
  let A := SmoothPaths.applyField
    (SmoothPaths.superpose (hVs.continuous_fderiv (by simp)) (Q x))
  have hQ : HasFDerivAt Q DQ x :=
    (contDiff_trajectory hV hVs h hh).differentiable (by simp) x |>.hasFDerivAt
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hVs.differentiable (by simp)) (hVs.continuous_fderiv (by simp)) (Q x)).comp x hQ
  have hP := (primitiveCLM (E := E)).hasFDerivAt.comp x hS
  have hC := (ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)).hasFDerivAt (x := x)
  have hD := hC.add (hP.const_smul h)
  have hD' : HasFDerivAt Q
      ((ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)) +
        h • primitiveCLM.comp (A.comp DQ)) x := by
    apply hD.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun y => (trajectory_eq hV h hh y).symm)
  exact congrArg (fun L : E →L[ℝ] C(Time, E) => L v) (hQ.unique hD')

end
end SmoothODE

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.CompleteFlow


namespace OAI

universe u7 u8 u9 u10 u11 u12 u13

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u7} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

def variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : ℝ) : E :=
  v + h • ∫ s in 0..t,
    fderiv ℝ V (extend (trajectory hV h hh x) s) (extend (tangentPath hV h hh x v) s)

theorem variation_coe {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : Time) :
    variation hV h hh x v t = tangentPath hV h hh x v t :=
  (congrArg (fun u : C(Time, E) => u t) (tangentPath_eq hV hVs h hh x v)).symm

omit [ProperSpace E] in
@[simp] theorem variation_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) : variation hV h hh x v 0 = v := by
  simp [variation]

omit [ProperSpace E] in
theorem continuous_variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    Continuous (variation hV h hh x v) := by
  have hc := ((hVs.continuous_fderiv (by simp)).comp
    (continuous_extend (trajectory hV h hh x))).clm_apply
      (continuous_extend (tangentPath hV h hh x v))
  exact continuous_const.add
    ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).const_smul h)

theorem hasDerivAt_variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : Time) :
    HasDerivAt (variation hV h hh x v)
      (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x v t)) (t : ℝ) := by
  have hc := ((hVs.continuous_fderiv (by simp)).comp
    (continuous_extend (trajectory hV h hh x))).clm_apply
      (continuous_extend (tangentPath hV h hh x v))
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 (t : ℝ)))
      hc.continuousAt
  rw [curve_coe, variation_coe hV hVs]
  change HasDerivAt (fun s : ℝ => v + h • ∫ r in 0..s,
    fderiv ℝ V (extend (trajectory hV h hh x) r) (extend (tangentPath hV h hh x v) r))
    _ (t : ℝ)
  simpa only [Pi.smul_apply, Function.comp_apply, extend_coe] using (hd.const_smul h).const_add v

theorem tangentPath_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    tangentPath hV h hh x v ⟨1, by constructor <;> norm_num⟩ = fderiv ℝ (step hV h hh) x v := by
  let t : Time := ⟨1, by constructor <;> norm_num⟩
  have hd := (ContinuousMap.evalCLM ℝ (M := E) t).hasFDerivAt.comp x
    ((contDiff_trajectory hV hVs h hh).differentiable (by simp) x).hasFDerivAt
  exact (congrArg (fun L : E →L[ℝ] E => L v) hd.fderiv).symm

theorem variation_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    variation hV h hh x v 1 = fderiv ℝ (step hV h hh) x v :=
  (variation_coe hV hVs h hh x v ⟨1, by constructor <;> norm_num⟩).trans
    (tangentPath_one hV hVs h hh x v)

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u8} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem step_preserves_tensor {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : Differentiable ℝ B)
    (hInv : ∀ z a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (x a b : E) :
    B (step hV h hh x) (fderiv ℝ (step hV h hh) x a)
      (fderiv ℝ (step hV h hh) x b) = B x a b := by
  let F : ℝ → ℝ := fun t => B (curve hV h hh x t)
    (variation hV h hh x a t) (variation hV h hh x b t)
  have hc : Continuous F :=
    ((hB.continuous.comp (continuous_curve hV h hh x)).clm_apply
      (continuous_variation hV hVs h hh x a)).clm_apply
      (continuous_variation hV hVs h hh x b)
  have hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    let T : Time := ⟨t, ht.1, ht.2.le⟩
    have hv := hasDerivAt_curve hV h hh x T
    have ha := hasDerivAt_variation hV hVs h hh x a T
    have hb := hasDerivAt_variation hV hVs h hh x b T
    have hdb : HasDerivAt (fun s : ℝ => B (curve hV h hh x s))
        (fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t))) t :=
      (hB (curve hV h hh x t)).hasFDerivAt.comp_hasDerivAt (l := B)
        (l' := fderiv ℝ B (curve hV h hh x t)) t hv
    have hdf := (hdb.clm_apply ha).clm_apply hb
    have hz :
        ((fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t)))
          (variation hV h hh x a t) +
          B (curve hV h hh x t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t)))
          (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t)) = 0 := by
      simp only [map_smul, smul_apply,
        add_apply, smul_eq_mul]
      calc
        _ = h * (fderiv ℝ B (curve hV h hh x t) (V (curve hV h hh x t))
            (variation hV h hh x a t) (variation hV h hh x b t) +
          B (curve hV h hh x t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t))
            (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t))) := by ring
        _ = 0 := by rw [hInv, mul_zero]
    exact (hdf.congr_deriv hz).hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc.continuousOn hd 1
    (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [F, curve_one, variation_one hV hVs, curve_zero, variation_zero] using he

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u9} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem contDiff_homeomorph_pow (f : E ≃ₜ E) (hf : ContDiff ℝ ∞ (f : E → E))
    (n : ℕ) : ContDiff ℝ ∞ ((f ^ n : E ≃ₜ E) : E → E) := by
  induction n with
  | zero =>
    rw [pow_zero]
    change ContDiff ℝ ∞ (id : E → E)
    exact contDiff_id
  | succ n ih =>
    rw [pow_succ']
    change ContDiff ℝ ∞ ((f : E → E) ∘ (f ^ n : E ≃ₜ E))
    exact hf.comp ih

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_preserves_tensor (f : E ≃ₜ E)
    (hf : ContDiff ℝ ∞ (f : E → E))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x a b, B (f x) (fderiv ℝ (f : E → E) x a)
      (fderiv ℝ (f : E → E) x b) = B x a b) (n : ℕ) (x a b : E) :
    B ((f ^ n) x) (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x a)
      (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x b) = B x a b := by
  induction n with
  | zero =>
    rw [pow_zero]
    change B x (fderiv ℝ (id : E → E) x a) (fderiv ℝ (id : E → E) x b) = _
    simp
  | succ n ih =>
    rw [pow_succ']
    change B (f ((f ^ n) x)) (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x a)
      (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x b) = _
    rw [fderiv_comp x (hf.differentiable (by simp) _)
      ((contDiff_homeomorph_pow f hf n).differentiable (by simp) _)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hB]
    exact ih

omit [ProperSpace E] in

theorem curve_linear_component {F : Type u10} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (L : E →L[ℝ] F) (v : F)
    (hL : ∀ z, L (V z) = v) (x : E) (t : Time) :
    L (curve hV h hh x t) = L x + (t : ℝ) • h • v := by
  let G : ℝ → F := fun s => L (curve hV h hh x s) - s • h • v
  have hc : Continuous G :=
    (L.continuous.comp (continuous_curve hV h hh x)).sub (continuous_id.smul continuous_const)
  have hd : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt G 0 (Ici s) s := by
    intro s hs
    have hd := L.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_curve hV h hh x ⟨s, hs.1, hs.2.le⟩)
    have hlin := (hasDerivAt_id s).smul_const (h • v)
    have hh' : HasDerivAt G 0 s := by
      change HasDerivAt ((L ∘ curve hV h hh x) - fun s : ℝ => s • h • v) 0 s
      simpa only [id_eq, map_smul, hL, one_smul, sub_self] using hd.sub hlin
    exact hh'.hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc.continuousOn hd (t : ℝ) t.property
  simpa only [G, curve_zero, zero_smul, sub_zero, sub_eq_iff_eq_add] using he

omit [ProperSpace E] in
@[simp] theorem step_linear_component {F : Type u11} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (L : E →L[ℝ] F) (v : F)
    (hL : ∀ z, L (V z) = v) (x : E) :
    L (step hV h hh x) = L x + h • v := by
  simpa only [curve_one, one_smul] using
    curve_linear_component hV h hh L v hL x (⟨1, by constructor <;> norm_num⟩ : Time)

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_linear_component {F : Type u12} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₜ E) (L : E →L[ℝ] F) (v : F) (hL : ∀ x, L (f x) = L x + v)
    (n : ℕ) (x : E) : L ((f ^ n) x) = L x + n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Homeomorph.mul_apply, hL, ih, succ_nsmul]
    abel

theorem exists_transport {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : Differentiable ℝ B)
    (hInv : ∀ z a b, fderiv ℝ B z (V z) a b + B z (fderiv ℝ V z a) b +
      B z a (fderiv ℝ V z b) = 0)
    {F : Type u13} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (v : F) (hL : ∀ x, L (V x) = v) (T : ℝ) :
    ∃ f : E ≃ₜ E, ContDiff ℝ ∞ (f : E → E) ∧ ContDiff ℝ ∞ (f.symm : E → E) ∧
      (∀ x a b, B (f x) (fderiv ℝ (f : E → E) x a) (fderiv ℝ (f : E → E) x b) = B x a b) ∧
      (∀ x, L (f x) = L x + T • v) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (‖T‖ * (K : ℝ)) 0)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  let h : ℝ := T / N
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖ * (K : ℝ) < (1 : ℝ)
    dsimp [h]
    rw [abs_div, abs_of_pos hN0, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  let f := stepHomeomorph hV hVs h hh
  have hf : ContDiff ℝ ∞ (f : E → E) := contDiff_step hV hVs h hh
  have hfi : ContDiff ℝ ∞ (f.symm : E → E) := contDiff_step hV hVs (-h) (by simpa using hh)
  refine ⟨f ^ N, contDiff_homeomorph_pow f hf N, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ ((f ^ N)⁻¹ : E ≃ₜ E)
    rw [← inv_pow]
    exact contDiff_homeomorph_pow f⁻¹ hfi N
  · exact homeomorph_pow_preserves_tensor f hf (step_preserves_tensor hV hVs h hh hB hInv) N
  · intro x
    have he := homeomorph_pow_linear_component f L (h • v)
      (step_linear_component hV h hh L v hL) N x
    have hs : (N : ℝ) * h = T := by dsimp [h]; field_simp
    simpa only [nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hs] using he

end
end SmoothODE

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.SmoothFlow


namespace OAI

universe u14 u15 u16

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u14} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

theorem curve_injective {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (t : Time) :
    Function.Injective (fun x => curve hV h hh x t) := by
  intro x y he
  have heq : EqOn (curve hV h hh x) (curve hV h hh y) (Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ y => h • V y) (s := fun _ => univ) (K := ‖h‖₊ * K)
    · intro _ _
      exact ((lipschitzWith_smul h).comp hV).lipschitzOnWith
    · exact (continuous_curve hV h hh x).continuousOn
    · intro s hs
      exact (hasDerivAt_curve hV h hh x ⟨s, hs.1.le, hs.2.trans t.property.2⟩).hasDerivWithinAt
    · intro _ _; trivial
    · exact (continuous_curve hV h hh y).continuousOn
    · intro s hs
      exact (hasDerivAt_curve hV h hh y ⟨s, hs.1.le, hs.2.trans t.property.2⟩).hasDerivWithinAt
    · intro _ _; trivial
    · exact he
  simpa only [curve_zero] using heq (show 0 ∈ Icc (0 : ℝ) t from ⟨le_rfl, t.property.1⟩)

theorem curve_of_const_along {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E)
    (hc : ∀ t : Time, V (x + (t : ℝ) • h • v) = v) :
    EqOn (curve hV h hh x) (fun t => x + t • h • v) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x
  · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  · intro t ht
    have he := hc ⟨t, ht.1, ht.2.le⟩
    have hd := ((hasDerivAt_id t).smul_const (h • v)).const_add x
    simpa only [he, one_smul, id_eq] using hd.hasDerivWithinAt (s := Ici t)
  · simp

theorem curve_spaceTime_outside {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {U : Set E} (hTime : ∀ z, (V z).1 = 1)
    (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0) (x : ℝ × E) (hx : x.2 ∉ U) (t : Time) :
    curve hV h hh x t = (x.1 + (t : ℝ) * h, x.2) := by
  have hc : ∀ s : Time, V (x + (s : ℝ) • h • (1, (0 : E))) = (1, 0) := by
    intro s
    apply Prod.ext
    · exact hTime _
    · exact hOut _ (by simpa using hx)
  have he := curve_of_const_along hV h hh x (1, (0 : E)) hc t.property
  calc
    curve hV h hh x t = x + (t : ℝ) • h • (1, (0 : E)) := he
    _ = (x.1 + (t : ℝ) * h, x.2) := by ext <;> simp [smul_eq_mul]

theorem curve_spaceTime_mapsTo {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {U : Set E} (hTime : ∀ z, (V z).1 = 1)
    (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0) (x : ℝ × E) (hx : x.2 ∈ U) (t : Time) :
    (curve hV h hh x t).2 ∈ U := by
  by_contra hout
  let y : ℝ × E := (x.1, (curve hV h hh x t).2)
  have he : curve hV h hh y t = curve hV h hh x t := by
    rw [curve_spaceTime_outside hV h hh hTime hOut y hout]
    apply Prod.ext
    · have he := curve_linear_component hV h hh (ContinuousLinearMap.fst ℝ ℝ E) 1 hTime x t
      simpa only [ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one, y] using he.symm
    · rfl
  have hy := curve_injective hV h hh t he
  have hxy := congrArg Prod.snd hy
  exact hout (hxy ▸ hx)

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u15} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem step_preserves_tensor_on {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E}
    (hB : ∀ z ∈ U, DifferentiableAt ℝ B z)
    (hInv : ∀ z ∈ U, ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (x : E) (hpath : ∀ t : Time, curve hV h hh x t ∈ U) (a b : E) :
    B (step hV h hh x) (fderiv ℝ (step hV h hh) x a)
      (fderiv ℝ (step hV h hh) x b) = B x a b := by
  let F : ℝ → ℝ := fun t => B (curve hV h hh x t)
    (variation hV h hh x a t) (variation hV h hh x b t)
  have hBc : ContinuousOn B U := fun z hz => (hB z hz).continuousAt.continuousWithinAt
  have hc : ContinuousOn F (Icc 0 1) :=
    ((hBc.comp (continuous_curve hV h hh x).continuousOn (fun t ht => hpath ⟨t, ht⟩)).clm_apply
      (continuous_variation hV hVs h hh x a).continuousOn).clm_apply
      (continuous_variation hV hVs h hh x b).continuousOn
  have hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    let T : Time := ⟨t, ht.1, ht.2.le⟩
    have hv := hasDerivAt_curve hV h hh x T
    have ha := hasDerivAt_variation hV hVs h hh x a T
    have hb := hasDerivAt_variation hV hVs h hh x b T
    have hdb : HasDerivAt (fun s : ℝ => B (curve hV h hh x s))
        (fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t))) t :=
      (hB (curve hV h hh x t) (hpath T)).hasFDerivAt.comp_hasDerivAt (l := B)
        (l' := fderiv ℝ B (curve hV h hh x t)) t hv
    have hdf := (hdb.clm_apply ha).clm_apply hb
    have hz :
        ((fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t)))
          (variation hV h hh x a t) +
          B (curve hV h hh x t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t)))
          (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t)) = 0 := by
      simp only [map_smul, smul_apply,
        add_apply, smul_eq_mul]
      calc
        _ = h * (fderiv ℝ B (curve hV h hh x t) (V (curve hV h hh x t))
            (variation hV h hh x a t) (variation hV h hh x b t) +
          B (curve hV h hh x t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t))
            (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t))) := by ring
        _ = 0 := by rw [hInv _ (hpath T), mul_zero]
    exact (hdf.congr_deriv hz).hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc hd 1
    (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [F, curve_one, variation_one hV hVs, curve_zero, variation_zero] using he

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u16} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_preserves_tensor_on (f : E ≃ₜ E)
    (hf : ContDiff ℝ ∞ (f : E → E)) {U : Set E} (hU : MapsTo f U U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x ∈ U, ∀ a b, B (f x) (fderiv ℝ (f : E → E) x a)
      (fderiv ℝ (f : E → E) x b) = B x a b) (n : ℕ) (x : E) (hx : x ∈ U) :
    (f ^ n) x ∈ U ∧ ∀ a b,
      B ((f ^ n) x) (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x a)
        (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x b) = B x a b := by
  induction n with
  | zero =>
    refine ⟨hx, ?_⟩
    intro a b
    change B x (fderiv ℝ (id : E → E) x a) (fderiv ℝ (id : E → E) x b) = _
    simp
  | succ n ih =>
    rw [pow_succ']
    refine ⟨hU ih.1, ?_⟩
    intro a b
    change B (f ((f ^ n) x)) (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x a)
      (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x b) = _
    rw [fderiv_comp x (hf.differentiable (by simp) _)
      ((contDiff_homeomorph_pow f hf n).differentiable (by simp) _)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hB _ ih.1]
    exact ih.2 a b

theorem exists_spaceTime_transport {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V) {U : Set E}
    (hTime : ∀ z, (V z).1 = 1) (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0)
    {B : (ℝ × E) → (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ}
    (hB : ∀ z, z.2 ∈ U → DifferentiableAt ℝ B z)
    (hInv : ∀ z, z.2 ∈ U → ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (T : ℝ) :
    ∃ f : (ℝ × E) ≃ₜ (ℝ × E),
      ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E)) ∧
      ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E)) ∧
      (∀ x, (f x).1 = x.1 + T) ∧
      (∀ x, x.2 ∉ U → (f x).2 = x.2) ∧
      (∀ x, x.2 ∈ U → (f x).2 ∈ U ∧ ∀ a b,
        B (f x) (fderiv ℝ (f : (ℝ × E) → (ℝ × E)) x a)
          (fderiv ℝ (f : (ℝ × E) → (ℝ × E)) x b) = B x a b) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (‖T‖ * (K : ℝ)) 0)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  let h : ℝ := T / N
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖ * (K : ℝ) < (1 : ℝ)
    dsimp [h]
    rw [abs_div, abs_of_pos hN0, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  let f := stepHomeomorph hV hVs h hh
  have hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E)) := contDiff_step hV hVs h hh
  have hfi : ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E)) :=
    contDiff_step hV hVs (-h) (by simpa using hh)
  have hm : ∀ x, x.2 ∈ U → (f x).2 ∈ U := by
    intro x hx
    simpa only [Prod.mk.eta, curve_one, f, stepHomeomorph_apply] using
      curve_spaceTime_mapsTo hV h hh hTime hOut x hx ⟨1, by constructor <;> norm_num⟩
  have ho : ∀ x, x.2 ∉ U → (f x).2 = x.2 := by
    intro x hx
    have he := curve_spaceTime_outside hV h hh hTime hOut x hx ⟨1, by constructor <;> norm_num⟩
    simpa only [curve_one, f, stepHomeomorph_apply] using congrArg Prod.snd he
  refine ⟨f ^ N, contDiff_homeomorph_pow f hf N, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ ((f ^ N)⁻¹ : (ℝ × E) ≃ₜ (ℝ × E))
    rw [← inv_pow]
    exact contDiff_homeomorph_pow f⁻¹ hfi N
  · intro x
    have hs : (N : ℝ) * h = T := by dsimp [h]; field_simp
    have he := homeomorph_pow_linear_component f (ContinuousLinearMap.fst ℝ ℝ E) h
      (by intro z; simpa only [smul_eq_mul, mul_one, f, stepHomeomorph_apply] using
        step_linear_component hV h hh (ContinuousLinearMap.fst ℝ ℝ E) 1 hTime z) N x
    simpa only [ContinuousLinearMap.coe_fst', nsmul_eq_mul, hs] using he
  · intro x hx
    have hi : ∀ n : ℕ, ((f ^ n) x).2 = x.2 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Homeomorph.mul_apply, ho _ (by simpa only [ih] using hx), ih]
    exact hi N
  · intro x hx
    apply homeomorph_pow_preserves_tensor_on f hf (U := Prod.snd ⁻¹' U)
      (fun _ hz => hm _ hz) (fun z hz a b => ?_) N x hx
    exact step_preserves_tensor_on hV hVs h hh (U := Prod.snd ⁻¹' U)
      (fun y hy => hB y hy) (fun y hy => hInv y hy) z
      (fun t => curve_spaceTime_mapsTo hV h hh hTime hOut z hz t) a b

end
end SmoothODE

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.TensorCalculus


namespace OAI

universe u17 u18 u19 u20 u21 u22

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

open Set Filter Function
open scoped Topology ContDiff

namespace TensorCalculus

variable {E : Type u17} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

abbrev TwoTensor (E : Type u18) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

def evalTensor (a b : E) : TwoTensor E →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ b).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)

@[simp] theorem evalTensor_apply (a b : E) (B : TwoTensor E) :
    evalTensor a b B = B a b := rfl

theorem fderiv_evalTensor {D : Type u19} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → TwoTensor E} {x : D} (hB : DifferentiableAt ℝ B x)
    (d : D) (a b : E) : fderiv ℝ (fun y => B y a b) x d = fderiv ℝ B x d a b := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const a))
    (differentiableAt_const b)]
  rw [fderiv_clm_apply hB (differentiableAt_const a)]
  simp

theorem fderiv_skew {B : E → TwoTensor E} (hB : Differentiable ℝ B)
    (hsk : ∀ x a b, B x a b = -B x b a) (x d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) = fun y => -B y b a := funext (fun y => hsk y a b)
  have he' := congrArg (fun f : E → ℝ => fderiv ℝ f x d) he
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor (hB x), neg_apply] using he'

theorem derivative_kernel {B : E → TwoTensor E} {V : E → E}
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V)
    (hker : ∀ x, B x (V x) = 0) (x a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    (hB x).hasFDerivAt.clm_apply (hV x).hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hker)
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he

theorem invariant_of_closed_kernel {B : E → TwoTensor E} {V : E → E}
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V)
    (hsk : ∀ x a b, B x a b = -B x b a)
    (hclosed : ∀ x a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ x, B x (V x) = 0) (x a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel hB hV hker x a b
  have h2 := derivative_kernel hB hV hker x b a
  have h3 := hclosed x (V x) a b
  have h4 := fderiv_skew hB hsk x a b (V x)
  have h5 := hsk x a (fderiv ℝ V x b)
  linarith

theorem fderiv_skew_at {B : E → TwoTensor E} {x : E} (hB : DifferentiableAt ℝ B x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a) (d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) =ᶠ[𝓝 x] (fun y => -B y b a) :=
    hsk.mono (fun y hy => hy a b)
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L d) he.fderiv_eq
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor hB, neg_apply] using he'

theorem derivative_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    hB.hasFDerivAt.clm_apply hV.hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq hker
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he

theorem invariant_of_closed_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a)
    (hclosed : ∀ a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel_at hB hV hker a b
  have h2 := derivative_kernel_at hB hV hker b a
  have h3 := hclosed (V x) a b
  have h4 := fderiv_skew_at hB hsk a b (V x)
  have h5 := (hsk.self_of_nhds) a (fderiv ℝ V x b)
  linarith

def alt : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ) -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap

@[simp] theorem alt_apply (B : TwoTensor E) (a b : E) :
    alt B a b = B a b - B b a := rfl

def exteriorD (γ : E → E →L[ℝ] ℝ) (x : E) : TwoTensor E :=
  alt (fderiv ℝ γ x)

@[simp] theorem exteriorD_apply (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = fderiv ℝ γ x a b - fderiv ℝ γ x b a := rfl

theorem exteriorD_skew (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = -exteriorD γ x b a := by
  simp only [exteriorD_apply]; ring

theorem fderiv_exteriorD {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : DifferentiableAt ℝ (fderiv ℝ γ) x) (d a b : E) :
    fderiv ℝ (exteriorD γ) x d a b =
      fderiv ℝ (fderiv ℝ γ) x d a b - fderiv ℝ (fderiv ℝ γ) x d b a := by
  change fderiv ℝ (alt ∘ fderiv ℝ γ) x d a b = _
  rw [fderiv_comp x (ContinuousLinearMap.differentiableAt (alt (E := E))) hγ]
  simp

theorem contDiff_exteriorD {γ : E → E →L[ℝ] ℝ}
    (hγ : ContDiff ℝ ∞ γ) : ContDiff ℝ ∞ (exteriorD γ) := by
  change ContDiff ℝ ∞ ((alt (E := E)) ∘ fderiv ℝ γ)
  exact (alt (E := E)).contDiff.comp (hγ.fderiv_right (m := ∞) (by simp))

theorem exteriorD_closed {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : ContDiffAt ℝ ∞ γ x) (a b c : E) :
    fderiv ℝ (exteriorD γ) x a b c + fderiv ℝ (exteriorD γ) x b c a +
      fderiv ℝ (exteriorD γ) x c a b = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ γ) x :=
    (hγ.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiableAt (by simp)
  have hs := hγ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [fderiv_exteriorD hd]
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L c) (hs.eq a b)
  have h2 := congrArg (fun L : E →L[ℝ] ℝ => L a) (hs.eq b c)
  have h3 := congrArg (fun L : E →L[ℝ] ℝ => L b) (hs.eq c a)
  linarith

end
end TensorCalculus

namespace TensorCalculus

open Set Filter Function
open scoped Topology ContDiff

variable {E : Type u20} {F : Type u21} {D : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable section

def pullLinear (L : F →L[ℝ] E) (B : TwoTensor E) : TwoTensor F :=
  B.bilinearComp L L

@[simp] theorem pullLinear_apply (L : F →L[ℝ] E) (B : TwoTensor E) (a b : F) :
    pullLinear L B a b = B (L a) (L b) := rfl

theorem contDiffAt_pullLinear (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun x => pullLinear L (B x)) z := by
  let P : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip L
  change ContDiffAt ℝ ∞ (fun x => P.comp ((B x).comp L)) z
  exact contDiffAt_const.clm_comp (hB.clm_comp contDiffAt_const)

theorem fderiv_pullLinear_eval (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : DifferentiableAt ℝ B z)
    (hP : DifferentiableAt ℝ (fun x => pullLinear L (B x)) z) (d : D) (a b : F) :
    fderiv ℝ (fun x => pullLinear L (B x)) z d a b =
      fderiv ℝ B z d (L a) (L b) := by
  rw [← fderiv_evalTensor hP, ← fderiv_evalTensor hB]
  rfl

theorem pullLinear_closed (L : F →L[ℝ] E) {B : E → TwoTensor E} {z : F}
    (hB : ContDiffAt ℝ ∞ B (L z))
    (hclosed : ∀ a b c, fderiv ℝ B (L z) a b c +
      fderiv ℝ B (L z) b c a + fderiv ℝ B (L z) c a b = 0) (a b c : F) :
    fderiv ℝ (fun x => pullLinear L (B (L x))) z a b c +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z b c a +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z c a b = 0 := by
  have hs : ContDiffAt ℝ ∞ (fun x => B (L x)) z := hB.comp z L.contDiff.contDiffAt
  have ht := contDiffAt_pullLinear L hs
  have he (d u v : F) :
      fderiv ℝ (fun x => pullLinear L (B (L x))) z d u v =
        fderiv ℝ B (L z) (L d) (L u) (L v) := by
    rw [fderiv_pullLinear_eval L (hs.differentiableAt (by simp))
      (ht.differentiableAt (by simp))]
    rw [fderiv_fun_comp z (hB.differentiableAt (by simp)) L.differentiableAt]
    simp
  simp only [he]
  exact hclosed (L a) (L b) (L c)

end
end TensorCalculus

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.MoserField


namespace OAI

universe u23 u24

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff NNReal

namespace Moser

variable {E : Type u23} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

def spatialField (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) : E :=
  -(ρ z.1) • (A z).inverse (γ z.2)

omit [CompleteSpace E] in
theorem spatialField_eq_zero_of_oneForm_eq_zero
    (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) (hz : γ z.2 = 0) :
    spatialField A γ ρ z = 0 := by simp [spatialField, hz]

omit [CompleteSpace E] in
theorem contract_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) (hA : (A z).IsInvertible) :
    A z (spatialField A γ ρ z) = -(ρ z.1) • γ z.2 := by
  simp only [spatialField, map_smul, hA.self_apply_inverse]

omit [CompleteSpace E] in

theorem oneForm_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E)
    (hA : (A z).IsInvertible) (hsk : ∀ a b, A z a b = -A z b a) :
    γ z.2 (spatialField A γ ρ z) = 0 := by
  let v := (A z).inverse (γ z.2)
  have he : A z v = γ z.2 := hA.self_apply_inverse _
  have hh := hsk v v
  have hz : A z v v = 0 := by linarith
  have hγv : γ z.2 v = 0 := by rw [← he]; exact hz
  simpa [spatialField, v, map_smul, smul_eq_mul] using
    congrArg (fun t : ℝ => -(ρ z.1) * t) hγv

theorem contDiff_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ} {U : Set E}
    (hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z)
    (hi : ∀ z, z.2 ∈ U → (A z).IsInvertible)
    (hγ : ContDiff ℝ ∞ γ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport γ ⊆ U) :
    ContDiff ℝ ∞ (spatialField A γ ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ U
  · have hv : ContDiffAt ℝ ∞ (fun x => (A x).inverse) z :=
      (hi z hz).contDiffAt_map_inverse.comp z (hA z hz)
    exact ((hρ.contDiffAt.comp z contDiffAt_fst).neg).smul
      (hv.clm_apply (hγ.contDiffAt.comp z contDiffAt_snd))
  · have ht : z.2 ∉ tsupport γ := fun hc => hz (hs hc)
    have he : ∀ᶠ y in 𝓝 z, y.2 ∉ tsupport γ :=
      continuous_snd.continuousAt ((isClosed_tsupport γ).isOpen_compl.mem_nhds ht)
    have heq : spatialField A γ ρ =ᶠ[𝓝 z] fun _ => 0 := he.mono (fun y hy =>
      spatialField_eq_zero_of_oneForm_eq_zero A γ ρ y (image_eq_zero_of_notMem_tsupport hy))
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [CompleteSpace E] in

theorem hasCompactSupport_spatialField
    (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ}
    (hγ : HasCompactSupport γ) (hρ : HasCompactSupport ρ) :
    HasCompactSupport (spatialField A γ ρ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hρ.prod hγ)
  intro z hz
  constructor
  · by_contra ht
    apply hz
    simp [spatialField, image_eq_zero_of_notMem_tsupport ht]
  · by_contra hx
    apply hz
    exact spatialField_eq_zero_of_oneForm_eq_zero A γ ρ z
      (image_eq_zero_of_notMem_tsupport hx)

theorem exists_lipschitz_spaceTimeField
    {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ} {U : Set E}
    (hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z)
    (hi : ∀ z, z.2 ∈ U → (A z).IsInvertible)
    (hγ : ContDiff ℝ ∞ γ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport γ ⊆ U)
    (hcγ : HasCompactSupport γ) (hcρ : HasCompactSupport ρ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun z => ((1 : ℝ), spatialField A γ ρ z)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_spatialField A hcγ hcρ)
    (contDiff_spatialField hA hi hγ hρ hs) (by simp)
  exact ⟨max 0 K, (LipschitzWith.const (1 : ℝ)).prodMk hK⟩

end
end Moser

namespace Moser

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u24} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def extendedOneForm (γ : E → E →L[ℝ] ℝ) (β : ℝ → ℝ) (z : ℝ × E) :
    (ℝ × E) →L[ℝ] ℝ :=
  β z.1 • (γ z.2).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem extendedOneForm_apply (γ : E → E →L[ℝ] ℝ) (β : ℝ → ℝ)
    (z a : ℝ × E) : extendedOneForm γ β z a = β z.1 * γ z.2 a.2 := rfl

theorem contDiff_extendedOneForm {γ : E → E →L[ℝ] ℝ} {β : ℝ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (extendedOneForm γ β) := by
  exact (hβ.comp contDiff_fst).smul ((hγ.comp contDiff_snd).clm_comp contDiff_const)

theorem fderiv_extendedOneForm {γ : E → E →L[ℝ] ℝ} {β : ℝ → ℝ} {z : ℝ × E}
    (hγ : DifferentiableAt ℝ γ z.2) (hβ : DifferentiableAt ℝ β z.1)
    (a b : ℝ × E) :
    fderiv ℝ (extendedOneForm γ β) z a b =
      deriv β z.1 * a.1 * γ z.2 b.2 + β z.1 * fderiv ℝ γ z.2 a.2 b.2 := by
  have hα : DifferentiableAt ℝ (extendedOneForm γ β) z :=
    (hβ.comp z differentiableAt_fst).smul
      ((hγ.comp z differentiableAt_snd).clm_comp (differentiableAt_const _))
  have he : fderiv ℝ (fun y => extendedOneForm γ β y b) z a =
      fderiv ℝ (extendedOneForm γ β) z a b := by
    rw [fderiv_clm_apply hα (differentiableAt_const b)]; simp
  rw [← he]
  simp only [extendedOneForm_apply]
  have hb : DifferentiableAt ℝ (fun y : ℝ × E => β y.1) z :=
    hβ.comp z differentiableAt_fst
  have hg : DifferentiableAt ℝ (fun y : ℝ × E => γ y.2 b.2) z :=
    (hγ.comp z differentiableAt_snd).clm_apply (differentiableAt_const b.2)
  rw [fderiv_fun_mul hb hg]
  rw [fderiv_fun_comp z hβ differentiableAt_fst]
  have hg' : DifferentiableAt ℝ (fun y : ℝ × E => γ y.2) z :=
    hγ.comp z differentiableAt_snd
  rw [fderiv_clm_apply hg' (differentiableAt_const b.2)]
  rw [fderiv_fun_comp z hγ differentiableAt_snd]
  simp [fderiv_eq_smul_deriv, fderiv_fst, fderiv_snd, mul_comm, add_comm]

def spatialTensor (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) (z : ℝ × E) : TwoTensor E :=
  W z.2 + β z.1 • exteriorD γ z.2

def spaceTimeTensor (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) (z : ℝ × E) : TwoTensor (ℝ × E) :=
  pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (W z.2) +
    exteriorD (extendedOneForm γ β) z

theorem contDiffAt_spatialTensor {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiffAt ℝ ∞ (spatialTensor W γ β) z := by
  have hd : ContDiff ℝ ∞ (exteriorD γ) :=
    contDiff_exteriorD hγ
  exact (hW.comp z contDiffAt_snd).add
    ((hβ.contDiffAt.comp z contDiffAt_fst).smul (hd.contDiffAt.comp z contDiffAt_snd))

theorem contDiffAt_spaceTimeTensor {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiffAt ℝ ∞ (spaceTimeTensor W γ β) z := by
  have hα := contDiff_extendedOneForm hγ hβ
  have hd : ContDiff ℝ ∞ (exteriorD (extendedOneForm γ β)) :=
    contDiff_exteriorD hα
  exact (contDiffAt_pullLinear (ContinuousLinearMap.snd ℝ ℝ E)
    (hW.comp z contDiffAt_snd)).add hd.contDiffAt

theorem spaceTimeTensor_apply {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hγ : DifferentiableAt ℝ γ z.2)
    (hβ : DifferentiableAt ℝ β z.1) (a b : ℝ × E) :
    spaceTimeTensor W γ β z a b = spatialTensor W γ β z a.2 b.2 +
      deriv β z.1 * (a.1 * γ z.2 b.2 - b.1 * γ z.2 a.2) := by
  simp only [spaceTimeTensor, add_apply, pullLinear_apply,
    ContinuousLinearMap.coe_snd', exteriorD_apply, fderiv_extendedOneForm hγ hβ,
    spatialTensor, smul_apply, smul_eq_mul]
  ring

theorem spaceTimeTensor_skew (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) {z : ℝ × E} (hW : ∀ a b, W z.2 a b = -W z.2 b a) (a b : ℝ × E) :
    spaceTimeTensor W γ β z a b = -spaceTimeTensor W γ β z b a := by
  simp only [spaceTimeTensor, add_apply, pullLinear_apply,
    ContinuousLinearMap.coe_snd']
  rw [hW a.2 b.2, exteriorD_skew (extendedOneForm γ β) z a b]
  ring

theorem spaceTimeTensor_closed {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β)
    (hclosed : ∀ a b c, fderiv ℝ W z.2 a b c +
      fderiv ℝ W z.2 b c a + fderiv ℝ W z.2 c a b = 0) (a b c : ℝ × E) :
    fderiv ℝ (spaceTimeTensor W γ β) z a b c +
      fderiv ℝ (spaceTimeTensor W γ β) z b c a +
      fderiv ℝ (spaceTimeTensor W γ β) z c a b = 0 := by
  have hα := contDiff_extendedOneForm hγ hβ
  have hd : ContDiff ℝ ∞ (exteriorD (extendedOneForm γ β)) :=
    contDiff_exteriorD hα
  have hp : ContDiffAt ℝ ∞ (fun y : ℝ × E =>
      pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (W y.2)) z :=
    contDiffAt_pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (hW.comp z contDiffAt_snd)
  have he := pullLinear_closed (ContinuousLinearMap.snd ℝ ℝ E) hW hclosed a b c
  have hf := exteriorD_closed (x := z) hα.contDiffAt a b c
  unfold spaceTimeTensor
  simp only [fderiv_fun_add (hp.differentiableAt (by simp))
    (hd.differentiable (by simp) z), add_apply]
  dsimp only [ContinuousLinearMap.coe_snd'] at he
  linarith

theorem spaceTimeTensor_kernel {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hγ : DifferentiableAt ℝ γ z.2)
    (hβ : DifferentiableAt ℝ β z.1)
    (hi : (spatialTensor W γ β z).IsInvertible)
    (hsk : ∀ a b, W z.2 a b = -W z.2 b a) :
    spaceTimeTensor W γ β z (1, spatialField (spatialTensor W γ β) γ (deriv β) z) = 0 := by
  have hs : ∀ a b, spatialTensor W γ β z a b = -spatialTensor W γ β z b a := by
    intro a b
    simp only [spatialTensor, add_apply, smul_apply,
      smul_eq_mul]
    rw [hsk a b, exteriorD_skew γ z.2 a b]; ring
  have hc := contract_spatialField γ (deriv β) z hi
  have hz := oneForm_spatialField γ (deriv β) z hi hs
  apply ContinuousLinearMap.ext
  intro a
  rw [spaceTimeTensor_apply hγ hβ]
  simp only [one_mul, hz, mul_zero, sub_zero]
  have hc' := congrArg (fun L : E →L[ℝ] ℝ => L a.2) hc
  simp only [smul_apply, smul_eq_mul] at hc'
  simp only [zero_apply]
  linarith

end
end Moser

open Set Filter
open scoped Topology ContDiff

namespace Moser

noncomputable section

def timeCutoff : ℝ → ℝ := Real.smoothTransition

theorem timeCutoff_smooth : ContDiff ℝ ∞ timeCutoff := Real.smoothTransition.contDiff

theorem timeCutoff_mem (t : ℝ) : timeCutoff t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

@[simp] theorem timeCutoff_zero : timeCutoff 0 = 0 := Real.smoothTransition.zero

@[simp] theorem timeCutoff_one : timeCutoff 1 = 1 := Real.smoothTransition.one

theorem timeCutoff_deriv_smooth : ContDiff ℝ ∞ (deriv timeCutoff) :=
  (show ContDiff ℝ (∞ + 1) timeCutoff by simpa using timeCutoff_smooth).deriv'

theorem timeCutoff_deriv_hasCompactSupport : HasCompactSupport (deriv timeCutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  intro t ht
  by_contra h
  have hd : deriv timeCutoff t = 0 := by
    rw [mem_Icc, not_and_or] at h
    rcases h with h | h
    · have hn : ∀ᶠ y in 𝓝 t, y < 0 := Iio_mem_nhds (lt_of_not_ge h)
      have he : timeCutoff =ᶠ[𝓝 t] fun _ => 0 :=
        hn.mono (fun y hy =>
          Real.smoothTransition.zero_of_nonpos hy.le)
      rw [he.deriv_eq, deriv_const]
    · have hn : ∀ᶠ y in 𝓝 t, 1 < y := Ioi_mem_nhds (lt_of_not_ge h)
      have he : timeCutoff =ᶠ[𝓝 t] fun _ => 1 :=
        hn.mono (fun y hy =>
          Real.smoothTransition.one_of_one_le hy.le)
      rw [he.deriv_eq, deriv_const]
  exact ht hd

end
end Moser

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.MoserFlow


namespace OAI

universe u25 u26

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff

namespace SmoothODE

variable {E : Type u25} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

def fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) : E ≃ₜ E where
  toFun x := (f (t, x)).2
  invFun y := (f.symm (t + T, y)).2
  left_inv x := by
    have he : (t + T, (f (t, x)).2) = f (t, x) := by
      ext
      · exact (hTime (t, x)).symm
      · rfl
    change (f.symm (t + T, (f (t, x)).2)).2 = x
    rw [he, f.symm_apply_apply]
  right_inv y := by
    have he : (f.symm (t + T, y)).1 = t := by
      have h := hTime (f.symm (t + T, y))
      rw [f.apply_symm_apply] at h
      dsimp at h
      linarith
    have he' : (t, (f.symm (t + T, y)).2) = f.symm (t + T, y) := by
      ext
      · exact he.symm
      · rfl
    change (f (t, (f.symm (t + T, y)).2)).2 = y
    rw [he', f.apply_symm_apply]
  continuous_toFun := continuous_snd.comp (f.continuous.comp (continuous_const.prodMk continuous_id))
  continuous_invFun := continuous_snd.comp
    (f.symm.continuous.comp (continuous_const.prodMk continuous_id))

omit [NormedSpace ℝ E] in
@[simp] theorem fiberHomeomorph_apply (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) (x : E) :
    fiberHomeomorph f T hTime t x = (f (t, x)).2 := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem fiberHomeomorph_symm_apply (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) (x : E) :
    (fiberHomeomorph f T hTime t).symm x = (f.symm (t + T, x)).2 := rfl

theorem contDiff_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) :
    ContDiff ℝ ∞ (fiberHomeomorph f T hTime t : E → E) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).snd

theorem contDiff_fiberHomeomorph_symm (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E))) :
    ContDiff ℝ ∞ ((fiberHomeomorph f T hTime t).symm : E → E) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).snd

theorem fderiv_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) (x a : E) :
    fderiv ℝ (f : (ℝ × E) → (ℝ × E)) (t, x) (0, a) =
      (0, fderiv ℝ (fiberHomeomorph f T hTime t : E → E) x a) := by
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    have hh := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
    have he : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.inr ℝ ℝ E := by
      ext y <;> rfl
    rw [he] at hh
    exact hh
  have hd := (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp x hi
  change HasFDerivAt (fun y : E => f (t, y)) _ x at hd
  have he : (fun y : E => f (t, y)) =
      fun y => (t + T, fiberHomeomorph f T hTime t y) := by
    funext y
    exact Prod.ext (hTime (t, y)) rfl
  have hd' := (hasFDerivAt_const (𝕜 := ℝ) (t + T) x).prodMk
    ((contDiff_fiberHomeomorph f T hTime t hf).differentiable (by simp) x).hasFDerivAt
  have hu := congrArg (fun L : E →L[ℝ] (ℝ × E) => L a)
    ((he ▸ hd).unique hd')
  simpa using hu

omit [NormedSpace ℝ E] in

theorem fiberHomeomorph_mapsTo (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) {U : Set E}
    (hOut : ∀ z, z.2 ∉ U → (f z).2 = z.2) :
    ∀ x, fiberHomeomorph f T hTime t x ∈ U ↔ x ∈ U := by
  intro x
  constructor
  · intro hx
    by_contra hc
    rw [fiberHomeomorph_apply, hOut (t, x) hc] at hx
    exact hc hx
  · intro hx
    by_contra hc
    have he : fiberHomeomorph f T hTime t (fiberHomeomorph f T hTime t x) =
        fiberHomeomorph f T hTime t x := hOut _ hc
    have hu := (fiberHomeomorph f T hTime t).injective he
    exact hc (hu.symm ▸ hx)

end
end SmoothODE

namespace Moser

open Set Filter Function TensorCalculus SmoothODE
open scoped Topology ContDiff NNReal

variable {E : Type u26} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem compactlySupported_deformation {U : Set E} (hU : IsOpen U)
    {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    (hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x)
    (hsk : ∀ x ∈ U, ∀ a b, W x a b = -W x b a)
    (hclosed : ∀ x ∈ U, ∀ a b c,
      fderiv ℝ W x a b c + fderiv ℝ W x b c a + fderiv ℝ W x c a b = 0)
    (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ) (hs : tsupport γ ⊆ U)
    (hi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        (W (F x) + exteriorD γ (F x)) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = W x a b := by
  let A := spatialTensor W γ timeCutoff
  let Y := spatialField A γ (deriv timeCutoff)
  let V : (ℝ × E) → (ℝ × E) := fun z => (1, Y z)
  let B := spaceTimeTensor W γ timeCutoff
  have hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z := by
    intro z hz
    exact contDiffAt_spatialTensor (hW z.2 hz) hγ timeCutoff_smooth
  have hAi : ∀ z, z.2 ∈ U → (A z).IsInvertible := by
    intro z hz
    exact hi z.2 hz _ (timeCutoff_mem z.1)
  have hY : ContDiff ℝ ∞ Y :=
    contDiff_spatialField hA hAi hγ timeCutoff_deriv_smooth hs
  have hV : ContDiff ℝ ∞ V := contDiff_const.prodMk hY
  obtain ⟨K, hK⟩ := exists_lipschitz_spaceTimeField hA hAi hγ
    timeCutoff_deriv_smooth hs hcγ timeCutoff_deriv_hasCompactSupport
  have hOut : ∀ z, z.2 ∉ U → (V z).2 = 0 := by
    intro z hz
    exact spatialField_eq_zero_of_oneForm_eq_zero A γ (deriv timeCutoff) z
      (image_eq_zero_of_notMem_tsupport (fun hc => hz (hs hc)))
  have hB : ∀ z, z.2 ∈ U → DifferentiableAt ℝ B z := by
    intro z hz
    exact (contDiffAt_spaceTimeTensor (hW z.2 hz) hγ timeCutoff_smooth).differentiableAt
      (by simp)
  have hIv : ∀ z, z.2 ∈ U → ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0 := by
    intro z hz a b
    have hn : ∀ᶠ y in 𝓝 z, y.2 ∈ U := continuous_snd.continuousAt (hU.mem_nhds hz)
    apply invariant_of_closed_kernel_at (hB z hz) (hV.differentiable (by simp) z)
      (hn.mono (fun y hy => spaceTimeTensor_skew W γ timeCutoff (hsk y.2 hy)))
      (spaceTimeTensor_closed (hW z.2 hz) hγ timeCutoff_smooth (hclosed z.2 hz))
      (hn.mono (fun y hy => spaceTimeTensor_kernel (hγ.differentiable (by simp) y.2)
        (timeCutoff_smooth.differentiable (by simp) y.1) (hAi y hy) (hsk y.2 hy)))
  obtain ⟨f, hf, hfi, htime, hout, htrans⟩ :=
    exists_spaceTime_transport hK hV (fun _ => rfl) hOut hB hIv 1
  let F := fiberHomeomorph f 1 htime 0
  have hF : ContDiff ℝ ∞ (F : E → E) := contDiff_fiberHomeomorph f 1 htime 0 hf
  have hFi : ContDiff ℝ ∞ (F.symm : E → E) := contDiff_fiberHomeomorph_symm f 1 htime 0 hfi
  refine ⟨F, hF, hFi, ?_, fiberHomeomorph_mapsTo f 1 htime 0 hout, ?_⟩
  · intro x hx
    exact hout (0, x) hx
  · intro x hx a b
    have hh := (htrans (0, x) hx).2 (0, a) (0, b)
    rw [fderiv_fiberHomeomorph f 1 htime 0 hf x a,
      fderiv_fiberHomeomorph f 1 htime 0 hf x b] at hh
    have he : f (0, x) = (1, F x) := by
      apply Prod.ext
      · simpa using htime (0, x)
      · rfl
    rw [he] at hh
    have hb (z : ℝ × E) (a b : E) : B z (0, a) (0, b) = A z a b := by
      dsimp only [B, A]
      rw [spaceTimeTensor_apply (hγ.differentiable (by simp) z.2)
        (timeCutoff_smooth.differentiable (by simp) z.1)]
      simp
    rw [hb, hb] at hh
    simpa only [A, spatialTensor, timeCutoff_zero, timeCutoff_one,
      one_smul, zero_smul, add_zero, add_apply, smul_apply, smul_eq_mul, zero_mul] using hh

end
end Moser

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.PotentialForms


namespace OAI

universe u27 u28 u29

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped Topology ContDiff

variable {E : Type u27} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def dcOp (J : E →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 4 : ℝ) • (ContinuousLinearMap.compL ℝ E E ℝ).flip J

def dc (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  dcOp J (fderiv ℝ φ x)

def ddc (J : E →L[ℝ] E) (φ : E → ℝ) : E → TwoTensor E := exteriorD (dc J φ)

@[simp] theorem dcOp_apply (J : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (a : E) :
    dcOp J L a = -(L (J a)) / 4 := by
  simp only [dcOp, smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

@[simp] theorem dc_apply (J : E →L[ℝ] E) (φ : E → ℝ) (x a : E) :
    dc J φ x a = -(fderiv ℝ φ x (J a)) / 4 := dcOp_apply J _ a

theorem contDiffAt_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (dc J φ) x := by
  change ContDiffAt ℝ ∞ (dcOp J ∘ fderiv ℝ φ) x
  exact (dcOp J).contDiff.contDiffAt.comp x (hφ.fderiv_right (m := ∞) (by simp))

theorem contDiff_dc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (dc J φ) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => contDiffAt_dc J (hφ.contDiffAt (x := x))

theorem fderiv_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a b : E) :
    fderiv ℝ (dc J φ) x a b = -(fderiv ℝ (fderiv ℝ φ) x a (J b)) / 4 := by
  change fderiv ℝ (dcOp J ∘ fderiv ℝ φ) x a b = _
  rw [fderiv_comp x (dcOp J).differentiableAt hφ]
  simp

theorem ddc_apply (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a b : E) :
    ddc J φ x a b =
      (fderiv ℝ (fderiv ℝ φ) x b (J a) - fderiv ℝ (fderiv ℝ φ) x a (J b)) / 4 := by
  simp only [ddc, exteriorD_apply, fderiv_dc J hφ]
  ring

theorem ddc_skew (J : E →L[ℝ] E) (φ : E → ℝ) (x a b : E) :
    ddc J φ x a b = -ddc J φ x b a := exteriorD_skew _ _ _ _

theorem contDiffAt_ddc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (ddc J φ) x := by
  change ContDiffAt ℝ ∞ (alt ∘ fderiv ℝ (dc J φ)) x
  exact (alt (E := E)).contDiff.contDiffAt.comp x
    ((contDiffAt_dc J hφ).fderiv_right (m := ∞) (by simp))

theorem contDiff_ddc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (ddc J φ) :=
  contDiff_exteriorD (contDiff_dc J hφ)

theorem ddc_closed (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (a b c : E) :
    fderiv ℝ (ddc J φ) x a b c + fderiv ℝ (ddc J φ) x b c a +
      fderiv ℝ (ddc J φ) x c a b = 0 := exteriorD_closed (contDiffAt_dc J hφ) a b c

theorem ddc_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a : E) :
    ddc J φ x a (J a) =
      (fderiv ℝ (fderiv ℝ φ) x a a + fderiv ℝ (fderiv ℝ φ) x (J a) (J a)) / 4 := by
  rw [ddc_apply J hφ, hJ]
  simp only [map_neg]
  ring

def IsPSHAt (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : Prop :=
  ContDiffAt ℝ ∞ φ x ∧ ∀ a, 0 ≤ ddc J φ x a (J a)

theorem dc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : dc J φ x = dc J ψ x := by
  rw [dc, dc, h.fderiv_eq]

theorem ddc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : ddc J φ x = ddc J ψ x := by
  have he : dc J φ =ᶠ[𝓝 x] dc J ψ := h.eventuallyEq_nhds.mono (fun y hy => dc_congr J hy)
  simpa only [ddc, exteriorD] using congrArg alt he.fderiv_eq

theorem dc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    dc J (fun y => φ y + ψ y) x = dc J φ x + dc J ψ x := by
  simp only [dc, fderiv_fun_add hφ hψ, map_add]

theorem ddc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y + ψ y) x = ddc J φ x + ddc J ψ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => φ y + ψ y) =ᶠ[𝓝 x] fun y => dc J φ y + dc J ψ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      (hψ.of_le h1).eventually (by simp)] with y hy hz
    exact dc_add J (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))
  unfold ddc exteriorD
  rw [he.fderiv_eq, fderiv_fun_add
    ((contDiffAt_dc J hφ).differentiableAt (by simp))
    ((contDiffAt_dc J hψ).differentiableAt (by simp)), map_add]

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus
open scoped ContDiff Topology

variable {E : Type u28} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

def standardTensor (J : E →L[ℝ] E) : TwoTensor E := (innerSL ℝ).comp J

@[simp] theorem standardTensor_apply (J : E →L[ℝ] E) (a b : E) :
    standardTensor J a b = inner (𝕜 := ℝ) (J a) b := rfl

theorem dc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    dc J (fun x : E => ‖x‖^2) x = (1 / 2 : ℝ) • standardTensor J x := by
  ext a
  rw [dc_apply, fderiv_norm_sq_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, standardTensor_apply]
  rw [hsk]
  ring

theorem ddc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    ddc J (fun x : E => ‖x‖^2) x = standardTensor J := by
  have he : dc J (fun x : E => ‖x‖^2) = fun x => (1 / 2 : ℝ) • standardTensor J x :=
    funext (dc_norm_sq J hsk)
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [ddc, he, exteriorD_apply]
  have hd : fderiv ℝ (fun x => (1 / 2 : ℝ) • standardTensor J x) x =
      (1 / 2 : ℝ) • standardTensor J := by
    exact ((standardTensor J).hasFDerivAt.const_smul (1 / 2 : ℝ)).fderiv
  rw [hd]
  simp only [smul_apply, smul_eq_mul, standardTensor_apply]
  have hh : inner (𝕜 := ℝ) (J b) a = -inner (𝕜 := ℝ) (J a) b := by
    rw [real_inner_comm, hsk]
  rw [hh]
  ring

theorem standardTensor_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, ‖J a‖ = ‖a‖) (a : E) :
    standardTensor J a (J a) = ‖a‖^2 := by
  rw [standardTensor_apply, real_inner_self_eq_norm_sq, hJ]

theorem isInvertible_of_positive_complex_line [FiniteDimensional ℝ E]
    (B : TwoTensor E) (J : E →L[ℝ] E) (hp : ∀ a : E, a ≠ 0 → 0 < B a (J a)) :
    B.IsInvertible := by
  have hi : Function.Injective B := by
    intro a b hab
    have hz : B (a - b) = 0 := by rw [map_sub, hab, sub_self]
    by_contra hn
    have hpos := hp (a - b) (sub_ne_zero.mpr hn)
    rw [hz, zero_apply] at hpos
    exact (lt_irrefl 0) hpos
  let e := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv
  let L : E →L[ℝ] E := e.symm.toContinuousLinearMap.comp B
  have hL : Function.Injective L := e.symm.injective.comp hi
  have hsL : Function.Surjective L := LinearMap.surjective_of_injective hL
  have hs : Function.Surjective B := by
    intro v
    obtain ⟨x, hx⟩ := hsL (e.symm v)
    refine ⟨x, ?_⟩
    exact e.symm.injective hx
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem isInvertible_ddc_norm_sq_add [FiniteDimensional ℝ E]
    (J : E →L[ℝ] E) (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) {φ : E → ℝ} {x : E} (hφ : IsPSHAt J φ x) :
    (ddc J (fun y => ‖y‖^2 + φ y) x).IsInvertible := by
  apply isInvertible_of_positive_complex_line _ J
  intro a ha
  rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt hφ.1, add_apply, add_apply,
    ddc_norm_sq J hsk, standardTensor_complex_line J hJ]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr ha)) (hφ.2 a)

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u29} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance linearOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance linearOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance linearTwoGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearTwoSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

@[simp] theorem dc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    dc J (fun _ => c) x = 0 := by
  simp [dc]

@[simp] theorem ddc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    ddc J (fun _ => c) x = 0 := by
  simp [ddc, exteriorD, show dc J (fun _ : E => c) = fun _ => 0 by funext y; simp]

theorem dc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    dc J (fun y => c * φ y) x = c • dc J φ x := by
  ext a
  rw [dc_apply, fderiv_const_mul hφ]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring

theorem ddc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => c * φ y) x = c • ddc J φ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => c * φ y) =ᶠ[𝓝 x] fun y => c • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp)] with y hy
    exact dc_const_smul J c (hy.differentiableAt one_ne_zero)
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  have hd : fderiv ℝ (fun y => c • dc J φ y) x = c • fderiv ℝ (dc J φ) x :=
    (((contDiffAt_dc J hφ).differentiableAt (by simp)).hasFDerivAt.const_smul c).fderiv
  rw [hd, map_smul]

theorem ddc_neg (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => -φ y) x = -ddc J φ x := by
  simpa only [neg_one_mul, neg_one_smul] using ddc_const_smul J (-1) hφ

theorem ddc_sub (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y - ψ y) x = ddc J φ x - ddc J ψ x := by
  simp_rw [sub_eq_add_neg]
  rw [ddc_add J hφ hψ.neg, ddc_neg J hψ]

theorem ddc_add_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y + c) x = ddc J φ x := by
  rw [ddc_add J hφ contDiffAt_const, ddc_const, add_zero]

theorem ddc_sub_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y - c) x = ddc J φ x := by
  rw [ddc_sub J hφ contDiffAt_const, ddc_const, sub_zero]

theorem IsPSHAt.add {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => φ y + ψ y) x := by
  refine ⟨hφ.1.add hψ.1, fun a => ?_⟩
  rw [ddc_add J hφ.1 hψ.1, add_apply, add_apply]
  exact add_nonneg (hφ.2 a) (hψ.2 a)

theorem IsPSHAt.const_smul {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) {c : ℝ} (hc : 0 ≤ c) :
    IsPSHAt J (fun y => c * φ y) x := by
  refine ⟨contDiffAt_const.mul hφ.1, fun a => ?_⟩
  rw [ddc_const_smul J c hφ.1]
  simpa only [smul_apply, smul_eq_mul] using mul_nonneg hc (hφ.2 a)

theorem IsPSHAt.sub_const {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (c : ℝ) : IsPSHAt J (fun y => φ y - c) x := by
  refine ⟨hφ.1.sub contDiffAt_const, fun a => ?_⟩
  rw [ddc_sub_const J hφ.1 c]
  exact hφ.2 a

end
end ComplexPotential

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.PotentialDeformation


namespace OAI

universe u30 u31 u32 u33 u34 u35

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

open Set Filter Function
open scoped ContDiff Topology

namespace CompactExtension
noncomputable section

variable {E : Type u30} {F : Type u31} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def extend (U : Set E) (f : E → F) : E → F := by
  classical
  exact U.indicator f

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem eventuallyEq_extend {U : Set E} (hU : IsOpen U) (f : E → F) {x : E} (hx : x ∈ U) :
    extend U f =ᶠ[𝓝 x] f := by
  classical
  filter_upwards [hU.mem_nhds hx] with y hy
  exact indicator_of_mem hy f

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem tsupport_extend_subset {U C : Set E} (hC : IsClosed C) {f : E → F}
    (hf : ∀ x ∈ U, x ∉ C → f x = 0) : tsupport (extend U f) ⊆ C := by
  classical
  apply closure_minimal _ hC
  intro x hx
  by_contra hn
  have hh : extend U f x = 0 := by
    by_cases hU : x ∈ U
    · exact (indicator_of_mem hU f).trans (hf x hU hn)
    · exact indicator_of_notMem hU f
  exact hx hh

theorem contDiff_extend {U C : Set E} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    {f : E → F} (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x)
    (hzero : ∀ x ∈ U, x ∉ C → f x = 0) : ContDiff ℝ ∞ (extend U f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf x hx).congr_of_eventuallyEq (eventuallyEq_extend hU f hx)
  · have hxc : x ∉ C := fun hc => hx (hCU hc)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hC.isOpen_compl.mem_nhds hxc] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun ht => hy (tsupport_extend_subset hC hzero ht))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem hasCompactSupport_extend {U C : Set E} (hC : IsCompact C) {f : E → F}
    (hzero : ∀ x ∈ U, x ∉ C → f x = 0) : HasCompactSupport (extend U f) :=
  hC.of_isClosed_subset (isClosed_tsupport _) (tsupport_extend_subset hC.isClosed hzero)

end
end CompactExtension

namespace ComplexPotential

open TensorCalculus Set Filter Function
open scoped ContDiff Topology

noncomputable section

variable {E : Type u32} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance moserOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance moserOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance moserTwoGroup : NormedAddCommGroup (TwoTensor E) := inferInstance
local instance moserTwoSpace : NormedSpace ℝ (TwoTensor E) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem tsupport_dc_subset (J : E →L[ℝ] E) (φ : E → ℝ) :
    tsupport (dc J φ) ⊆ tsupport φ :=
  (tsupport_comp_subset (map_zero (dcOp J)) (fderiv ℝ φ)).trans (tsupport_fderiv_subset ℝ)

omit [FiniteDimensional ℝ E] in
theorem fderiv_homeomorph_apply_symm (F : E ≃ₜ E)
    (hF : ContDiff ℝ ∞ (F : E → E)) (hFi : ContDiff ℝ ∞ (F.symm : E → E)) (x a : E) :
    fderiv ℝ (F : E → E) (F.symm x) (fderiv ℝ (F.symm : E → E) x a) = a := by
  have he : (F : E → E) ∘ (F.symm : E → E) = id := funext F.apply_symm_apply
  have hd := fderiv_comp x (hF.differentiable (by simp) (F.symm x))
    (hFi.differentiable (by simp) x)
  rw [he, fderiv_id] at hd
  exact (congrArg (fun L : E →L[ℝ] E => L a) hd).symm

theorem exists_potential_transport (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖)
    {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {τ T : E → ℝ} (hτ : ∀ x ∈ U, IsPSHAt J τ x) (hT : ∀ x ∈ U, IsPSHAt J T x)
    (heq : ∀ x ∈ U, x ∉ C → T x = τ x) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        ddc J (fun y => ‖y‖^2 + τ y) (F x) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = ddc J (fun y => ‖y‖^2 + T y) x a b := by
  let g := CompactExtension.extend U (fun y => T y - τ y)
  have hz : ∀ x ∈ U, x ∉ C → T x - τ x = 0 := by
    intro x hx hxc
    rw [heq x hx hxc, sub_self]
  have hg : ContDiff ℝ ∞ g := CompactExtension.contDiff_extend hU hC.isClosed hCU
    (fun x hx => (hT x hx).1.sub (hτ x hx).1) hz
  have hgs : tsupport g ⊆ C := CompactExtension.tsupport_extend_subset hC.isClosed hz
  let γ := dc J g
  let W := ddc J (fun y => ‖y‖^2 + τ y)
  have hγ : ContDiff ℝ ∞ γ := contDiff_dc J hg
  have hsγ : tsupport γ ⊆ C := (tsupport_dc_subset J g).trans hgs
  have hcγ : HasCompactSupport γ := hC.of_isClosed_subset (isClosed_tsupport _) hsγ
  have hdiff (x : E) (hx : x ∈ U) :
      exteriorD γ x = ddc J T x - ddc J τ x := by
    change ddc J g x = _
    rw [ddc_congr J (CompactExtension.eventuallyEq_extend hU _ hx)]
    exact ddc_sub J (hT x hx).1 (hτ x hx).1
  have hnorm (x : E) (hx : x ∈ U) : W x = standardTensor J + ddc J τ x := by
    dsimp [W]
    rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt (hτ x hx).1, ddc_norm_sq J hsk]
  have hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x := fun x hx =>
    contDiffAt_ddc J ((contDiff_norm_sq ℝ).contDiffAt.add (hτ x hx).1)
  have hWi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible := by
    intro x hx s hs
    apply isInvertible_of_positive_complex_line _ J
    intro a ha
    rw [hnorm x hx, hdiff x hx]
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul,
      standardTensor_complex_line J hJ]
    have hn : 0 < ‖a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
    have h₀ := mul_nonneg (sub_nonneg.mpr hs.2) ((hτ x hx).2 a)
    have h₁ := mul_nonneg hs.1 ((hT x hx).2 a)
    nlinarith
  obtain ⟨F, hF, hFi, hout, hmap, hpull⟩ := Moser.compactlySupported_deformation hU hW
    (fun x _ a b => ddc_skew J _ x a b)
    (fun x hx a b c => ddc_closed J ((contDiff_norm_sq ℝ).contDiffAt.add (hτ x hx).1) a b c)
    hγ hcγ (hsγ.trans hCU) hWi
  refine ⟨F.symm, hFi, hF, ?_, ?_, ?_⟩
  · intro x hx
    exact (F.symm_apply_eq.mpr (hout x hx).symm)
  · intro x
    simpa using (hmap (F.symm x)).symm
  · intro x hx a b
    have hix : F.symm x ∈ U := (hmap (F.symm x)).mp (by simpa using hx)
    have hh := hpull (F.symm x) hix (fderiv ℝ (F.symm : E → E) x a)
      (fderiv ℝ (F.symm : E → E) x b)
    rw [F.apply_symm_apply, fderiv_homeomorph_apply_symm F hF hFi,
      fderiv_homeomorph_apply_symm F hF hFi, hnorm x hx, hdiff x hx] at hh
    have hend : standardTensor J + ddc J τ x + (ddc J T x - ddc J τ x) =
        ddc J (fun y => ‖y‖^2 + T y) x := by
      rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt (hT x hx).1, ddc_norm_sq J hsk]
      abel
    rw [hend] at hh
    exact hh.symm

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u33} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

theorem dc_scalar_comp (J : E →L[ℝ] E) {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h (φ x)) :
    dc J (h ∘ φ) x = deriv h (φ x) • dc J φ x := by
  have hd := (hh.hasDerivAt.comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  ext a
  rw [dc_apply, hd]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring

theorem exteriorD_smul_one {γ : E → E →L[ℝ] ℝ} {s : E → ℝ} {x : E}
    (hs : DifferentiableAt ℝ s x) (hγ : DifferentiableAt ℝ γ x) (a b : E) :
    exteriorD (fun y => s y • γ y) x a b = s x * exteriorD γ x a b +
      fderiv ℝ s x a * γ x b - fderiv ℝ s x b * γ x a := by
  simp only [exteriorD_apply, fderiv_fun_smul hs hγ, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem ddc_scalar_comp (J : E →L[ℝ] E) {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hh : ContDiffAt ℝ ∞ h (φ x)) (a b : E) :
    ddc J (h ∘ φ) x a b = deriv h (φ x) * ddc J φ x a b +
      deriv (deriv h) (φ x) *
        (fderiv ℝ φ x b * fderiv ℝ φ x (J a) -
          fderiv ℝ φ x a * fderiv ℝ φ x (J b)) / 4 := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (h ∘ φ) =ᶠ[𝓝 x] fun y => deriv h (φ y) • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      hφ.continuousAt ((hh.of_le h1).eventually (by simp))] with y hy hz
    exact dc_scalar_comp J (hy.differentiableAt one_ne_zero)
      ((show ContDiffAt ℝ (1 : ℕ∞ω) h (φ y) from hz).differentiableAt one_ne_zero)
  have hdh := (hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => deriv h (φ y)) x :=
    hdh.comp x (hφ.differentiableAt (by simp))
  have hd : fderiv ℝ (fun y => deriv h (φ y)) x =
      deriv (deriv h) (φ x) • fderiv ℝ φ x :=
    (hdh.hasDerivAt.comp_hasFDerivAt x (hφ.differentiableAt (by simp)).hasFDerivAt).fderiv
  have heD : exteriorD (dc J (h ∘ φ)) x =
      exteriorD (fun y => deriv h (φ y) • dc J φ y) x := by
    unfold exteriorD
    rw [he.fderiv_eq]
  rw [ddc, heD, exteriorD_smul_one hs ((contDiffAt_dc J hφ).differentiableAt (by simp))]
  rw [hd]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  change _ = deriv h (φ x) * exteriorD (dc J φ) x a b + _
  ring

theorem ddc_scalar_comp_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hh : ContDiffAt ℝ ∞ h (φ x)) (a : E) :
    ddc J (h ∘ φ) x a (J a) = deriv h (φ x) * ddc J φ x a (J a) +
      deriv (deriv h) (φ x) * ((fderiv ℝ φ x a)^2 + (fderiv ℝ φ x (J a))^2) / 4 := by
  rw [ddc_scalar_comp J hφ hh, hJ, map_neg]
  ring

theorem IsPSHAt.scalar_comp (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {h : ℝ → ℝ} {x : E} (hφ : IsPSHAt J φ x)
    (hh : ContDiffAt ℝ ∞ h (φ x)) (hmono : 0 ≤ deriv h (φ x))
    (hconv : 0 ≤ deriv (deriv h) (φ x)) : IsPSHAt J (h ∘ φ) x := by
  refine ⟨hh.comp x hφ.1, fun a => ?_⟩
  rw [ddc_scalar_comp_complex_line J hJ hφ.1 hh]
  exact add_nonneg (mul_nonneg hmono (hφ.2 a))
    (div_nonneg (mul_nonneg hconv (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num))

end
end ComplexPotential

namespace ComplexPotential

variable {E : Type u34} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complex_line_inner_sq_le (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (x a : E) :
    (inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2 ≤ ‖x‖^2 * ‖a‖^2 := by
  let p := inner (𝕜 := ℝ) x a
  let q := inner (𝕜 := ℝ) x (J a)
  have hxa : inner (𝕜 := ℝ) (J x) a = -q := by
    dsimp [q]
    linarith [hsk x a]
  have hxj : inner (𝕜 := ℝ) x (J x) = 0 := by
    linarith [hsk x x, real_inner_comm x (J x)]
  have hjx : inner (𝕜 := ℝ) (J x) x = 0 := by rw [real_inner_comm, hxj]
  let w := p • x - q • J x
  have hw : inner (𝕜 := ℝ) w a = p^2 + q^2 := by
    dsimp [w]
    simp only [inner_sub_left, real_inner_smul_left, hxa]
    change p * p - q * (-q) = _
    ring
  have hww : inner (𝕜 := ℝ) w w = (p^2 + q^2) * ‖x‖^2 := by
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hxj, hjx]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hJ]
    ring
  have hcs := real_inner_mul_inner_self_le w a
  rw [hw, hww, real_inner_self_eq_norm_sq] at hcs
  change p^2 + q^2 ≤ ‖x‖^2 * ‖a‖^2
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg p) (sq_nonneg q)) with hs | hs
  · rw [← hs]
    positivity
  · exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith [hcs])

end ComplexPotential

namespace ComplexPotential

open Set Filter
open scoped ContDiff Topology

noncomputable section

@[simp] theorem deriv_log_add (δ t : ℝ) :
    deriv (fun s => Real.log (s + δ)) t = (t + δ)⁻¹ := by
  rw [deriv_comp_add_const, Real.deriv_log]

theorem second_deriv_log_add (δ t : ℝ) (ht : t + δ ≠ 0) :
    deriv (deriv (fun s => Real.log (s + δ))) t = -1 / (t + δ)^2 := by
  have he : deriv (fun s => Real.log (s + δ)) = fun t => (t + δ)⁻¹ :=
    funext (deriv_log_add δ)
  rw [he]
  exact ((hasDerivAt_id t).add_const δ |>.inv ht).deriv

variable {E : Type u35} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logNormSq (δ : ℝ) (x : E) : ℝ := Real.log (‖x‖^2 + δ)

theorem contDiffAt_logNormSq (δ : ℝ) {x : E} (hx : ‖x‖^2 + δ ≠ 0) :
    ContDiffAt ℝ ∞ (logNormSq δ) x :=
  ((contDiff_norm_sq ℝ).contDiffAt.add contDiffAt_const).log hx

theorem ddc_logNormSq_complex_line (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    (δ : ℝ) {x : E} (hx : ‖x‖^2 + δ ≠ 0) (a : E) :
    ddc J (logNormSq δ) x a (J a) = ‖a‖^2 / (‖x‖^2 + δ) -
      ((inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2) / (‖x‖^2 + δ)^2 := by
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => Real.log (t + δ)) (‖x‖^2) :=
    (contDiffAt_id.add contDiffAt_const).log hx
  have he := ddc_scalar_comp_complex_line J hJJ (contDiff_norm_sq ℝ).contDiffAt hl a
  rw [ddc_norm_sq J hsk, standardTensor_complex_line J hJ,
    deriv_log_add, second_deriv_log_add δ _ hx, fderiv_norm_sq_apply] at he
  simp only [smul_apply, innerSL_apply_apply] at he
  change ddc J (logNormSq δ) x a (J a) = _ at he
  rw [he]
  ring

theorem isPSHAt_logNormSq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    {δ : ℝ} (hδ : 0 ≤ δ) {x : E} (hx : 0 < ‖x‖^2 + δ) :
    IsPSHAt J (logNormSq δ) x := by
  refine ⟨contDiffAt_logNormSq δ hx.ne', fun a => ?_⟩
  rw [ddc_logNormSq_complex_line J hsk hJ hJJ δ hx.ne']
  have hineq := complex_line_inner_sq_le J hsk hJ x a
  have hnum : (inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2 ≤
      ‖a‖^2 * (‖x‖^2 + δ) := by
    nlinarith [mul_nonneg (sq_nonneg ‖a‖) hδ]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (sq_pos_of_pos hx) hx).mpr
  nlinarith [mul_le_mul_of_nonneg_right hnum hx.le]

end
end ComplexPotential

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.RegularizedMaximum


namespace OAI

universe u36 u37

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothPositivePart

noncomputable section

def primitive (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.smoothTransition s

theorem hasDerivAt_primitive (t : ℝ) : HasDerivAt primitive (Real.smoothTransition t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact Real.smoothTransition.continuous.intervalIntegrable _ _
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun _ _ => Real.smoothTransition.continuousAt) t (mem_univ t)
  · exact Real.smoothTransition.continuousAt

@[simp] theorem deriv_primitive : deriv primitive = Real.smoothTransition :=
  funext (fun t => (hasDerivAt_primitive t).deriv)

theorem primitive_smooth : ContDiff ℝ ∞ primitive := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (hasDerivAt_primitive t).differentiableAt,
    deriv_primitive ▸ Real.smoothTransition.contDiff⟩

theorem primitive_of_nonpos {t : ℝ} (ht : t ≤ 0) : primitive t = 0 := by
  calc
    primitive t = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply Real.smoothTransition.zero_of_nonpos
      exact le_trans hs.2 (max_eq_left ht).le
    _ = 0 := intervalIntegral.integral_zero

theorem primitive_one_mem : primitive 1 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro s _
    exact Real.smoothTransition.nonneg s
  · calc
      primitive 1 ≤ ∫ s in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact Real.smoothTransition.continuous.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro s _
          exact Real.smoothTransition.le_one s
      _ = 1 := by simp

theorem primitive_of_one_le {t : ℝ} (ht : 1 ≤ t) : primitive t = t + (primitive 1 - 1) := by
  have he : (∫ s in (1 : ℝ)..t, Real.smoothTransition s) = t - 1 := by
    calc
      _ = ∫ s in (1 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact Real.smoothTransition.one_of_one_le (le_trans (by simp [ht]) hs.1)
      _ = t - 1 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (Real.smoothTransition.continuous.intervalIntegrable (μ := volume) (0 : ℝ) 1)
    (Real.smoothTransition.continuous.intervalIntegrable (1 : ℝ) t)
  change primitive 1 + _ = primitive t at hadd
  rw [he] at hadd
  linarith

def shift : ℝ := primitive 1 - 1

theorem shift_mem : shift ∈ Icc (-1 : ℝ) 0 := by
  have h := primitive_one_mem
  change -1 ≤ primitive 1 - 1 ∧ primitive 1 - 1 ≤ 0
  constructor <;> linarith [h.1, h.2]

def positivePart (t : ℝ) : ℝ := primitive (t - shift)

theorem positivePart_smooth : ContDiff ℝ ∞ positivePart :=
  primitive_smooth.comp (contDiff_id.sub contDiff_const)

theorem positivePart_zero {t : ℝ} (ht : t ≤ -1) : positivePart t = 0 := by
  apply primitive_of_nonpos
  linarith [shift_mem.1]

theorem positivePart_eq_self {t : ℝ} (ht : 1 ≤ t) : positivePart t = t := by
  rw [positivePart, primitive_of_one_le (by linarith [shift_mem.2])]
  unfold shift
  ring

theorem deriv_positivePart (t : ℝ) : deriv positivePart t = Real.smoothTransition (t - shift) := by
  change deriv (fun t => primitive (t - shift)) t = _
  simpa only [mul_one, Function.comp_def, id_eq] using
    ((hasDerivAt_primitive (t - shift)).comp t ((hasDerivAt_id t).sub_const shift)).deriv

theorem deriv_positivePart_mem (t : ℝ) : deriv positivePart t ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_positivePart]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem second_deriv_positivePart_nonneg (t : ℝ) : 0 ≤ deriv (deriv positivePart) t := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  rw [deriv_positivePart, deriv_positivePart]
  exact Real.smoothTransition.monotone (sub_le_sub_right hxy _)

def smoothMax (h p : ℝ) : ℝ := p + positivePart (h - p)

theorem smoothMax_left {h p : ℝ} (hp : p + 1 ≤ h) : smoothMax h p = h := by
  rw [smoothMax, positivePart_eq_self (by linarith)]
  ring

theorem smoothMax_right {h p : ℝ} (hp : h + 1 ≤ p) : smoothMax h p = p := by
  rw [smoothMax, positivePart_zero (by linarith), add_zero]

end
end SmoothPositivePart

namespace ComplexPotential

open TensorCalculus SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u36} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance maxOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance maxOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance maxTwoGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance maxTwoSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem IsPSHAt.smoothMax {J : E →L[ℝ] E} (hJ : ∀ a, J (J a) = -a)
    {φ ψ : E → ℝ} {x : E} (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => smoothMax (φ y) (ψ y)) x := by
  have hdiff := hφ.1.sub hψ.1
  have hs : ContDiffAt ℝ ∞ (positivePart ∘ fun y => φ y - ψ y) x :=
    positivePart_smooth.contDiffAt.comp x hdiff
  refine ⟨hψ.1.add hs, fun a => ?_⟩
  change 0 ≤ ddc J (fun y => ψ y + (positivePart ∘ fun z => φ z - ψ z) y) x a (J a)
  rw [ddc_add J hψ.1 hs, add_apply, add_apply,
    ddc_scalar_comp_complex_line J hJ hdiff positivePart_smooth.contDiffAt,
    ddc_sub J hφ.1 hψ.1, sub_apply, sub_apply]
  have hβ := deriv_positivePart_mem (φ x - ψ x)
  have h2 := second_deriv_positivePart_nonneg (φ x - ψ x)
  have hpos : 0 ≤ (1 - deriv positivePart (φ x - ψ x)) * ddc J ψ x a (J a) +
      deriv positivePart (φ x - ψ x) * ddc J φ x a (J a) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hβ.2) (hψ.2 a))
      (mul_nonneg hβ.1 (hφ.2 a))
  have hquad : 0 ≤ deriv (deriv positivePart) (φ x - ψ x) *
      ((fderiv ℝ (fun y => φ y - ψ y) x a)^2 +
        (fderiv ℝ (fun y => φ y - ψ y) x (J a))^2) / 4 := by positivity
  nlinarith

theorem IsPSHAt.congr {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (he : ψ =ᶠ[𝓝 x] φ) : IsPSHAt J ψ x := by
  refine ⟨hφ.1.congr_of_eventuallyEq he, fun a => ?_⟩
  rw [ddc_congr J he]
  exact hφ.2 a

end
end ComplexPotential

namespace ComplexPotential

open SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u37} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

omit [NormedSpace ℝ E] in

def gluedPotential (R : ℝ) (H P : E → ℝ) (x : E) : ℝ := by
  classical
  exact if ‖x‖ < R then if x = 0 then P x else smoothMax (H x) (P x) else H x

omit [NormedSpace ℝ E] in
theorem gluedPotential_outer (R : ℝ) (H P : E → ℝ) {x : E} (hx : R ≤ ‖x‖) :
    gluedPotential R H P x = H x := by
  classical
  simp [gluedPotential, not_lt.mpr hx]

omit [NormedSpace ℝ E] in
theorem gluedPotential_inner {r R : ℝ} (hrR : r < R) (H P : E → ℝ)
    (hdom : ∀ x : E, x ≠ 0 → ‖x‖ ≤ r → H x + 1 ≤ P x) {x : E} (hx : ‖x‖ ≤ r) :
    gluedPotential R H P x = P x := by
  classical
  have hR : ‖x‖ < R := hx.trans_lt hrR
  by_cases hzero : x = 0
  · rw [gluedPotential, if_pos hR, if_pos hzero]
  · rw [gluedPotential, if_pos hR, if_neg hzero, smoothMax_right (hdom x hzero hx)]

theorem isPSHAt_gluedPotential (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {U : Set E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (H P : E → ℝ)
    (hH : ∀ x ∈ U, x ≠ 0 → IsPSHAt J H x)
    (hP : ∀ x ∈ U, IsPSHAt J P x)
    (hinner : ∀ x : E, x ≠ 0 → ‖x‖ ≤ r → H x + 1 ≤ P x)
    (houter : ∀ x ∈ U, ‖x‖ = R → P x + 1 < H x)
    {x : E} (hx : x ∈ U) : IsPSHAt J (gluedPotential R H P) x := by
  classical
  have hRpos : 0 < R := hr.trans hrR
  by_cases hzero : x = 0
  · have hn : ‖x‖ < r := by simpa [hzero] using hr
    apply (hP x hx).congr
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hn] with y hy
    exact gluedPotential_inner hrR H P hinner hy.le
  have hHx := hH x hx hzero
  have hPx := hP x hx
  rcases lt_trichotomy ‖x‖ R with hn | hn | hn
  · apply (hHx.smoothMax hJ hPx).congr
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hn,
      eventually_ne_nhds hzero] with y hy hy0
    simp [gluedPotential, hy, hy0]
  · apply hHx.congr
    have hlt := houter x hx hn
    filter_upwards [(hPx.1.continuousAt.add continuousAt_const).eventually_lt
      hHx.1.continuousAt hlt, eventually_ne_nhds hzero] with y hy hy0
    by_cases hny : ‖y‖ < R
    · simp [gluedPotential, hny, hy0, smoothMax_left hy.le]
    · simp [gluedPotential, hny]
  · apply hHx.congr
    filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hn] with y hy
    exact gluedPotential_outer R H P hy.le

end
end ComplexPotential

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.RadialMap


namespace OAI

universe u38 u39 u40

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace RadialSymplectic

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u38} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def radialMap (α : E → ℝ) (x : E) : E := α x • x

def radialPrimitive (B : TwoTensor E) (α : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  (α x ^ 2 / 2) • B x

theorem fderiv_radialMap {α : E → ℝ} {x : E} (hα : DifferentiableAt ℝ α x) (a : E) :
    fderiv ℝ (radialMap α) x a = α x • a + (fderiv ℝ α x a) • x := by
  have hh := hα.hasFDerivAt.smul (hasFDerivAt_id x)
  have he := congrArg (fun L : E →L[ℝ] E => L a) hh.fderiv
  change fderiv ℝ (radialMap α) x a = _ at he
  simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, id_eq] using he

theorem fderiv_radialPrimitive (B : TwoTensor E) {α : E → ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (a b : E) :
    fderiv ℝ (radialPrimitive B α) x a b =
      (α x ^ 2 / 2) * B a b + α x * fderiv ℝ α x a * B x b := by
  have hs : HasFDerivAt (fun y => α y ^ 2 / 2) (α x • fderiv ℝ α x) x := by
    convert! (hα.hasFDerivAt.pow 2).mul_const (1 / 2 : ℝ) using 1 <;>
      simp [div_eq_mul_inv, smul_smul]
  have hh := hs.smul B.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) hh.fderiv
  change fderiv ℝ (radialPrimitive B α) x a b = _ at he
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_assoc] using he

theorem radial_pullback (B : TwoTensor E) (hsk : ∀ a b, B a b = -B b a)
    {α : E → ℝ} {x : E} (hα : DifferentiableAt ℝ α x) (a b : E) :
    B (fderiv ℝ (radialMap α) x a) (fderiv ℝ (radialMap α) x b) =
      exteriorD (radialPrimitive B α) x a b := by
  have hz : B x x = 0 := by have hh := hsk x x; linarith
  simp only [fderiv_radialMap hα, exteriorD_apply, fderiv_radialPrimitive B hα,
    map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
  rw [hsk a x, hsk b a]
  ring

end
end RadialSymplectic

open Set
open scoped Topology ContDiff

namespace RadialSymplectic

noncomputable section

def radiusSq (μ δ s : ℝ) : ℝ := s + μ * (s / (s + δ))

def inverseScaleSq (μ δ t : ℝ) : ℝ :=
  2 * δ / (μ + δ - t + Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t))

theorem radiusSq_strictMonoOn {μ δ : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    StrictMonoOn (radiusSq μ δ) (Ici 0) := by
  intro s hs t ht hst
  have hsδ : 0 < s + δ := add_pos_of_nonneg_of_pos hs hδ
  have htδ : 0 < t + δ := add_pos_of_nonneg_of_pos ht hδ
  have hf : s / (s + δ) ≤ t / (t + δ) := by
    apply (div_le_div_iff₀ hsδ htδ).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hf hμ
  dsimp only [radiusSq]
  linarith

theorem radial_discriminant_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (t : ℝ) :
    0 < (μ + δ - t) ^ 2 + 4 * δ * t := by
  nlinarith [sq_nonneg (t + δ - μ), mul_pos hμ hδ]

theorem inverseScaleSq_den_pos {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (_ht : 0 ≤ t) : 0 < μ + δ - t + Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) := by
  have hsq := Real.sq_sqrt (radial_discriminant_pos hμ hδ t).le
  have hr := Real.sqrt_nonneg ((μ + δ - t) ^ 2 + 4 * δ * t)
  by_contra hc
  have hc' : Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) ≤ -(μ + δ - t) := by
    linarith
  have htt : 0 < t := by linarith
  have hmul := mul_self_le_mul_self hr hc'
  nlinarith [mul_pos hδ htt]

theorem inverseScaleSq_pos {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 < inverseScaleSq μ δ t :=
  div_pos (mul_pos (by norm_num) hδ) (inverseScaleSq_den_pos hμ hδ ht)

theorem inverseScaleSq_quadratic {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    t * (inverseScaleSq μ δ t) ^ 2 + (μ + δ - t) * inverseScaleSq μ δ t - δ = 0 := by
  have hD := (inverseScaleSq_den_pos hμ hδ ht).ne'
  have hsq := Real.sq_sqrt (radial_discriminant_pos hμ hδ t).le
  unfold inverseScaleSq
  generalize Real.sqrt ((μ + δ - t) ^ 2 + 4 * δ * t) = R at hD hsq ⊢
  field_simp [hD]
  nlinarith

theorem radiusSq_inverse {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    radiusSq μ δ (inverseScaleSq μ δ t * t) = t := by
  have hq := inverseScaleSq_pos hμ hδ ht
  have hquad := inverseScaleSq_quadratic hμ hδ ht
  have hd : 0 < inverseScaleSq μ δ t * t + δ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le ht) hδ
  unfold radiusSq
  field_simp [hd.ne']
  nlinarith [mul_eq_zero_of_left hquad t]

theorem inverseScaleSq_factor {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    (1 + μ / (inverseScaleSq μ δ t * t + δ)) * inverseScaleSq μ δ t = 1 := by
  have hq := inverseScaleSq_pos hμ hδ ht
  have hquad := inverseScaleSq_quadratic hμ hδ ht
  have hd : 0 < inverseScaleSq μ δ t * t + δ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le ht) hδ
  field_simp [hd.ne']
  nlinarith

theorem contDiffAt_inverseScaleSq {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (inverseScaleSq μ δ) t := by
  have hs : ContDiffAt ℝ ∞ (fun y => Real.sqrt ((μ + δ - y) ^ 2 + 4 * δ * y)) t :=
    (Real.contDiffAt_sqrt (radial_discriminant_pos hμ hδ t).ne').comp t
      (((contDiffAt_const.sub contDiffAt_id).pow 2).add (contDiffAt_const.mul contDiffAt_id))
  exact contDiffAt_const.div ((contDiffAt_const.sub contDiffAt_id).add hs)
    (inverseScaleSq_den_pos hμ hδ ht).ne'

end
end RadialSymplectic

namespace RadialSymplectic

open Set
open scoped Topology ContDiff

variable {E : Type u39} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

def expansionScale (μ δ : ℝ) (x : E) : ℝ := Real.sqrt (1 + μ / (‖x‖ ^ 2 + δ))
def radialExpansion (μ δ : ℝ) : E → E := radialMap (expansionScale μ δ)
def contractionScale (μ δ : ℝ) (x : E) : ℝ :=
  Real.sqrt (inverseScaleSq μ δ (‖x‖ ^ 2))
def radialContraction (μ δ : ℝ) : E → E := radialMap (contractionScale μ δ)

omit [InnerProductSpace ℝ E] in
theorem expansionScale_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    0 < expansionScale μ δ x := by
  unfold expansionScale
  apply Real.sqrt_pos.mpr
  have hd : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  positivity

omit [InnerProductSpace ℝ E] in
theorem expansionScale_sq {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    expansionScale μ δ x ^ 2 = 1 + μ / (‖x‖ ^ 2 + δ) := by
  unfold expansionScale
  apply Real.sq_sqrt
  have hd : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  positivity

theorem norm_sq_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    ‖radialExpansion μ δ x‖ ^ 2 = radiusSq μ δ (‖x‖ ^ 2) := by
  simp only [radialExpansion, radialMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [expansionScale_sq hμ hδ]
  unfold radiusSq
  ring

theorem radialExpansion_injective {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    Function.Injective (radialExpansion μ δ : E → E) := by
  intro x y h
  have hh := congrArg (fun z : E => ‖z‖ ^ 2) h
  rw [norm_sq_radialExpansion hμ hδ, norm_sq_radialExpansion hμ hδ] at hh
  have hnorm := (radiusSq_strictMonoOn hμ.le hδ).injOn (sq_nonneg ‖x‖) (sq_nonneg ‖y‖) hh
  have hscale : expansionScale μ δ x = expansionScale μ δ y := by
    unfold expansionScale
    rw [hnorm]
  dsimp only [radialExpansion, radialMap] at h
  rw [hscale] at h
  exact (smul_right_injective E (expansionScale_pos hμ hδ y).ne') h

omit [InnerProductSpace ℝ E] in
theorem contractionScale_pos {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    0 < contractionScale μ δ x :=
  Real.sqrt_pos.mpr (inverseScaleSq_pos hμ hδ (sq_nonneg _))

theorem norm_sq_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    ‖radialContraction μ δ x‖ ^ 2 = inverseScaleSq μ δ (‖x‖ ^ 2) * ‖x‖ ^ 2 := by
  simp only [radialContraction, radialMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [contractionScale, Real.sq_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg _)).le]

theorem expansionScale_mul_contractionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : expansionScale μ δ (radialContraction μ δ x) * contractionScale μ δ x = 1 := by
  have hp := expansionScale_pos hμ hδ (radialContraction μ δ x)
  have hq := contractionScale_pos hμ hδ x
  have hsq : (expansionScale μ δ (radialContraction μ δ x) * contractionScale μ δ x)^2 = 1 := by
    rw [mul_pow, expansionScale_sq hμ hδ, contractionScale,
      Real.sq_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg _)).le,
      norm_sq_radialContraction hμ hδ]
    exact inverseScaleSq_factor hμ hδ (sq_nonneg _)
  nlinarith [mul_pos hp hq]

theorem radialExpansion_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : radialExpansion μ δ (radialContraction μ δ x) = x := by
  change expansionScale μ δ (radialContraction μ δ x) • (contractionScale μ δ x • x) = x
  rw [smul_smul, expansionScale_mul_contractionScale hμ hδ, one_smul]

theorem radialContraction_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (x : E) : radialContraction μ δ (radialExpansion μ δ x) = x :=
  radialExpansion_injective hμ hδ (radialExpansion_radialContraction hμ hδ _)

theorem contDiff_expansionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (expansionScale μ δ : E → ℝ) := by
  have hn : ContDiff ℝ ∞ (fun x : E => ‖x‖^2 + δ) := (contDiff_norm_sq ℝ).add contDiff_const
  have hd (x : E) : ‖x‖ ^ 2 + δ ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne'
  have hp (x : E) : 1 + μ / (‖x‖ ^ 2 + δ) ≠ 0 := by
    have hpp : 0 < ‖x‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
    positivity
  exact (contDiff_const.add (contDiff_const.div hn hd)).sqrt hp

theorem contDiff_contractionScale {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (contractionScale μ δ : E → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hi : ContDiffAt ℝ ∞ (fun z : E => inverseScaleSq μ δ (‖z‖ ^ 2)) x :=
    (contDiffAt_inverseScaleSq hμ hδ (sq_nonneg ‖x‖)).comp (f := fun z : E => ‖z‖^2) x
      (contDiff_norm_sq ℝ).contDiffAt
  exact (Real.contDiffAt_sqrt (inverseScaleSq_pos hμ hδ (sq_nonneg ‖x‖)).ne').comp
    (f := fun z : E => inverseScaleSq μ δ (‖z‖ ^ 2)) x hi

theorem contDiff_radialExpansion {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (radialExpansion μ δ : E → E) :=
  (contDiff_expansionScale hμ hδ).smul contDiff_id

theorem contDiff_radialContraction {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (radialContraction μ δ : E → E) :=
  (contDiff_contractionScale hμ hδ).smul contDiff_id

def radialHomeomorph {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) : E ≃ₜ E where
  toFun := radialExpansion μ δ
  invFun := radialContraction μ δ
  left_inv := radialContraction_radialExpansion hμ hδ
  right_inv := radialExpansion_radialContraction hμ hδ
  continuous_toFun := (contDiff_radialExpansion hμ hδ).continuous
  continuous_invFun := (contDiff_radialContraction hμ hδ).continuous

theorem radialContraction_mapsTo {μ δ a r : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (hbound : a ≤ radiusSq μ δ (r^2)) :
    MapsTo (radialContraction μ δ : E → E) {x | ‖x‖^2 < a} {x | ‖x‖^2 < r^2} := by
  intro x hx
  have hi := radiusSq_inverse hμ hδ (sq_nonneg ‖x‖)
  have hh : radiusSq μ δ (‖radialContraction μ δ x‖^2) < radiusSq μ δ (r^2) := by
    rw [norm_sq_radialContraction hμ hδ, hi]
    exact lt_of_lt_of_le hx hbound
  exact ((radiusSq_strictMonoOn hμ.le hδ).lt_iff_lt
    (show ‖radialContraction μ δ x‖^2 ∈ Ici (0 : ℝ) from sq_nonneg ‖radialContraction μ δ x‖)
    (show r^2 ∈ Ici (0 : ℝ) from sq_nonneg r)).mp hh

end
end RadialSymplectic

namespace RadialSymplectic

open ComplexPotential TensorCalculus
open scoped ContDiff

noncomputable section

variable {E : Type u40} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def modelPotential (μ δ : ℝ) (x : E) : ℝ := ‖x‖^2 + μ * Real.log (‖x‖^2 + δ)

theorem contDiff_modelPotential (μ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (modelPotential μ δ : E → ℝ) :=
  (contDiff_norm_sq ℝ).add (contDiff_const.mul
    (((contDiff_norm_sq ℝ).add contDiff_const).log
      (fun x => (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hδ).ne')))

theorem dc_modelPotential (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    dc J (modelPotential μ δ) x = radialPrimitive (standardTensor J) (expansionScale μ δ) x := by
  let h : ℝ → ℝ := fun t => t + μ * Real.log (t + δ)
  have hp : ‖x‖^2 + δ ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne'
  have hd : HasDerivAt h (1 + μ * (‖x‖^2 + δ)⁻¹) (‖x‖^2) := by
    convert (hasDerivAt_id (‖x‖^2)).add
      ((((hasDerivAt_id (‖x‖^2)).add_const δ).log hp).const_mul μ) using 1 <;> first | rfl | simp [one_div]
  change dc J (h ∘ (fun y : E => ‖y‖^2)) x = _
  rw [dc_scalar_comp J ((contDiff_norm_sq ℝ).differentiable (show (∞ : ℕ∞ω) ≠ 0 by simp) x)
    hd.differentiableAt, hd.deriv, dc_norm_sq J hsk, smul_smul]
  unfold radialPrimitive
  rw [expansionScale_sq hμ hδ]
  congr 1
  ring

theorem radialExpansion_pullback (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x a b : E) :
    standardTensor J (fderiv ℝ (radialExpansion μ δ : E → E) x a)
      (fderiv ℝ (radialExpansion μ δ : E → E) x b) = ddc J (modelPotential μ δ) x a b := by
  have hsk' (a b : E) : standardTensor J a b = -standardTensor J b a := by
    change inner (𝕜 := ℝ) (J a) b = -inner (𝕜 := ℝ) (J b) a
    rw [← real_inner_comm (J a) b, hsk]
  have he : dc J (modelPotential μ δ) = radialPrimitive (standardTensor J) (expansionScale μ δ) :=
    funext (dc_modelPotential J hsk hμ hδ)
  rw [ddc, he]
  exact radial_pullback (standardTensor J) hsk' ((contDiff_expansionScale hμ hδ).differentiable
    (by simp) x) a b

theorem radialContraction_pullback (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x a b : E) :
    ddc J (modelPotential μ δ) (radialContraction μ δ x)
      (fderiv ℝ (radialContraction μ δ : E → E) x a)
      (fderiv ℝ (radialContraction μ δ : E → E) x b) = standardTensor J a b := by
  have hd (v : E) : fderiv ℝ (radialExpansion μ δ : E → E) (radialContraction μ δ x)
      (fderiv ℝ (radialContraction μ δ : E → E) x v) = v := by
    have he : (radialExpansion μ δ : E → E) ∘ radialContraction μ δ = id :=
      funext (radialExpansion_radialContraction hμ hδ)
    have hh := fderiv_comp x ((contDiff_radialExpansion hμ hδ).differentiable (by simp)
      (radialContraction μ δ x)) ((contDiff_radialContraction hμ hδ).differentiable (by simp) x)
    rw [he, fderiv_id] at hh
    exact (congrArg (fun L : E →L[ℝ] E => L v) hh).symm
  rw [← radialExpansion_pullback J hsk hμ hδ, hd, hd]

end
end RadialSymplectic

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.HolomorphicBalls


namespace OAI

universe u41 u42 u43 u44 u45 u46 u47 u48 u49

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff

open Set
namespace SingularComparison
noncomputable section

theorem exists_inner_radius {μ α R : ℝ} (hμ : 0 ≤ μ) (hμα : μ < α)
    (hR : 0 < R) (M C : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ (t δ H : ℝ), 0 < t → t ≤ r^2 → 0 < δ →
      H ≤ α * Real.log t + C → H + 2 ≤ μ * Real.log (t + δ) - M := by
  let L := (-M - C - 2) / (α - μ)
  obtain ⟨r, hr, hrsmall⟩ := exists_between (show (0 : ℝ) < min R (Real.sqrt (Real.exp L)) by
    exact lt_min hR (Real.sqrt_pos.mpr (Real.exp_pos L)))
  refine ⟨r, hr, hrsmall.trans_le (min_le_left _ _), ?_⟩
  intro t δ H ht htr hδ hH
  have hre : r < Real.sqrt (Real.exp L) := hrsmall.trans_le (min_le_right _ _)
  have hr2 : r^2 ≤ Real.exp L := by
    have hs := Real.sq_sqrt (Real.exp_pos L).le
    nlinarith [Real.sqrt_nonneg (Real.exp L)]
  have htL : Real.log t ≤ L := by
    calc
      Real.log t ≤ Real.log (Real.exp L) := Real.log_le_log ht (htr.trans hr2)
      _ = L := Real.log_exp L
  have hlog : Real.log t ≤ Real.log (t + δ) := Real.log_le_log ht (by linarith)
  have hcoef : (α - μ) * Real.log t ≤ -M - C - 2 := by
    calc
      _ ≤ (α - μ) * L := mul_le_mul_of_nonneg_left htL (sub_nonneg.mpr hμα.le)
      _ = -M - C - 2 := by dsimp [L]; field_simp [sub_ne_zero.mpr hμα.ne']
  have hmono := mul_le_mul_of_nonneg_left hlog hμ
  linarith

theorem outer_comparison {μ R δ H L M : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hH : L ≤ H)
    (hM : μ * Real.log (R^2 + 1) - L + 2 < M) :
    μ * Real.log (R^2 + δ) - M + 2 < H := by
  have hp : 0 < R^2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg R) hδ
  have hlog := Real.log_le_log hp (show R^2 + δ ≤ R^2 + 1 by linarith)
  have hh := mul_le_mul_of_nonneg_left hlog hμ
  linarith

theorem radius_bound {a μ r δ : ℝ} (ha : 0 < a) (_ham : a < μ) (hr : 0 < r)
    (hδ : 0 < δ) (hδb : δ < r^2 * (μ / a - 1)) :
    a < r^2 * (1 + μ / (r^2 + δ)) := by
  have hd : 0 < r^2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg r) hδ
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hδa : δ * a < r^2 * (μ - a) := by
    calc
      δ * a < (r^2 * (μ / a - 1)) * a := mul_lt_mul_of_pos_right hδb ha
      _ = r^2 * (μ - a) := by field_simp
  have hfrac : a < r^2 * μ / (r^2 + δ) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  calc
    a < r^2 * μ / (r^2 + δ) := hfrac
    _ < r^2 * (1 + μ / (r^2 + δ)) := by
      rw [mul_add, mul_one, mul_div_assoc]
      linarith

end
end SingularComparison

namespace ComplexPotential

open Set Filter RadialSymplectic
open scoped ContDiff Topology

noncomputable section

variable {E : Type u41} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_ball_from_logarithmic_pole (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    {U : Set E} (hU : IsOpen U) (hU0 : (0 : E) ∈ U)
    {τ H : E → ℝ} (hτ : ∀ x ∈ U, IsPSHAt J τ x) (hτ0 : τ 0 = 0)
    (hH : ∀ x ∈ U, x ≠ 0 → IsPSHAt J H x)
    (hcompact : ∀ s : ℝ, 0 < s → s < 1 → IsCompact {x | x ∈ U ∧ τ x ≤ s})
    {s₀ α C ρ : ℝ} (hs₀ : s₀ < 1) (hρ : 0 < ρ)
    (htail : ∀ x ∈ U, s₀ ≤ τ x → H x = τ x)
    (hpole : ∀ x ∈ U, x ≠ 0 → ‖x‖ ≤ ρ → H x ≤ α * Real.log (‖x‖^2) + C)
    {a : ℝ} (ha : 0 < a) (haα : a < α) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x : E, ‖x‖^2 < a → F x ∈ U) ∧
      ∀ x : E, ‖x‖^2 < a → ∀ v w : E,
        ddc J (fun y => ‖y‖^2 + τ y) (F x) (fderiv ℝ (F : E → E) x v)
          (fderiv ℝ (F : E → E) x w) = standardTensor J v w := by
  obtain ⟨μ, haμ, hμα⟩ := exists_between haα
  have hμ : 0 < μ := ha.trans haμ
  have hn : {x : E | x ∈ U ∧ τ x < 1/2} ∈ 𝓝 (0 : E) := by
    exact inter_mem (hU.mem_nhds hU0)
      ((hτ 0 hU0).1.continuousAt.eventually_lt continuousAt_const (by norm_num [hτ0]))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hn
  let R := ε / 2
  have hR : 0 < R := half_pos hε
  have hRball (x : E) (hx : ‖x‖ ≤ R) : x ∈ U ∧ τ x < 1/2 := by
    apply hεball
    rw [Metric.mem_ball, dist_zero_right]
    exact hx.trans_lt (half_lt_self hε)
  have hsp : IsCompact {x : E | ‖x‖ = R} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) R
  have hcont : ContinuousOn H {x : E | ‖x‖ = R} := by
    intro x hx
    apply ((hH x (hRball x hx.le).1 ?_).1.continuousAt).continuousWithinAt
    intro hz
    have : R = 0 := by simpa [hz] using hx.symm
    exact hR.ne' this
  obtain ⟨L, hL⟩ := hsp.bddBelow_image hcont
  let M := μ * Real.log (R^2 + 1) - L + 3
  obtain ⟨r, hr, hrlt, hrdom⟩ := SingularComparison.exists_inner_radius hμ.le hμα
    (lt_min hR hρ) M C
  have hrR : r < R := hrlt.trans_le (min_le_left _ _)
  have hrρ : r < ρ := hrlt.trans_le (min_le_right _ _)
  have hδmax : 0 < min (1 : ℝ) (r^2 * (μ / a - 1)) := by
    apply lt_min zero_lt_one
    exact mul_pos (sq_pos_of_pos hr) (sub_pos.mpr ((one_lt_div ha).mpr haμ))
  obtain ⟨δ, hδ, hδlt⟩ := exists_between hδmax
  have hδ1 : δ ≤ 1 := (hδlt.trans_le (min_le_left _ _)).le
  have hδb : δ < r^2 * (μ / a - 1) := hδlt.trans_le (min_le_right _ _)
  let P : E → ℝ := fun x => μ * logNormSq δ x - M
  have hP (x : E) : IsPSHAt J P x :=
    ((isPSHAt_logNormSq J hsk hJ hJJ hδ.le
      (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ)).const_smul hμ.le).sub_const M
  have hinner (x : E) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ r) : H x + 1 ≤ P x := by
    have hxu := (hRball x (hx.trans hrR.le)).1
    have hh := hrdom (‖x‖^2) δ (H x) (sq_pos_of_pos (norm_pos_iff.mpr hx0))
      ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr hx) hδ
      (hpole x hxu hx0 (hx.trans hrρ.le))
    change H x + 1 ≤ μ * Real.log (‖x‖^2 + δ) - M
    linarith
  have houter (x : E) (_hx : x ∈ U) (hnorm : ‖x‖ = R) : P x + 1 < H x := by
    have hh := SingularComparison.outer_comparison hμ.le hδ hδ1
      (hL ⟨x, hnorm, rfl⟩) (show μ * Real.log (R^2 + 1) - L + 2 < M by dsimp [M]; linarith)
    change μ * Real.log (‖x‖^2 + δ) - M + 1 < H x
    rw [hnorm]
    linarith
  let T := gluedPotential R H P
  have hT (x : E) (hx : x ∈ U) : IsPSHAt J T x :=
    isPSHAt_gluedPotential J hJJ hr hrR H P hH (fun x _ => hP x) hinner houter hx
  obtain ⟨σ, hσmin, hσ1⟩ := exists_between (show max s₀ (1/2 : ℝ) < 1 from
    max_lt hs₀ (by norm_num))
  have hσ0 : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2)
    ((le_max_right _ _).trans_lt hσmin)
  let K : Set E := {x | x ∈ U ∧ τ x ≤ σ}
  have hK : IsCompact K := hcompact σ hσ0 hσ1
  have heq (x : E) (hx : x ∈ U) (hxK : x ∉ K) : T x = τ x := by
    have hστ : σ < τ x := lt_of_not_ge (fun h => hxK ⟨hx, h⟩)
    have hnorm : R ≤ ‖x‖ := by
      by_contra hh
      have hhalf := (hRball x (not_le.mp hh).le).2
      linarith [(le_max_right s₀ (1/2 : ℝ)).trans_lt hσmin]
    exact (gluedPotential_outer R H P hnorm).trans (htail x hx
      (((le_max_left _ _).trans_lt hσmin).le.trans hστ.le))
  obtain ⟨Q, hQ, hQi, _hout, hQmap, hQpull⟩ := exists_potential_transport J hsk hJ
    hU hK (fun _ hx => hx.1) hτ hT heq
  let F := (radialHomeomorph (E := E) hμ hδ).symm.trans Q
  have hF : ContDiff ℝ ∞ (F : E → E) := hQ.comp (contDiff_radialContraction hμ hδ)
  have hFi : ContDiff ℝ ∞ (F.symm : E → E) := (contDiff_radialExpansion hμ hδ).comp hQi
  have hmap (x : E) (hx : ‖x‖^2 < a) : ‖radialContraction μ δ x‖ < r := by
    apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
    apply radialContraction_mapsTo hμ hδ _ hx
    calc
      a ≤ r^2 * (1 + μ / (r^2 + δ)) := (SingularComparison.radius_bound ha haμ hr hδ hδb).le
      _ = radiusSq μ δ (r^2) := by unfold radiusSq; ring
  have hUmap (x : E) (hx : ‖x‖^2 < a) : radialContraction μ δ x ∈ U :=
    (hRball _ ((hmap x hx).trans hrR).le).1
  refine ⟨F, hF, hFi, fun x hx => (hQmap _).mpr (hUmap x hx), ?_⟩
  intro x hx v w
  change ddc J (fun y => ‖y‖^2 + τ y) (Q (radialContraction μ δ x))
    (fderiv ℝ ((Q : E → E) ∘ radialContraction μ δ) x v)
    (fderiv ℝ ((Q : E → E) ∘ radialContraction μ δ) x w) = _
  rw [fderiv_comp x (hQ.differentiable (by simp) _) ((contDiff_radialContraction hμ hδ).differentiable
    (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hQpull _ (hUmap x hx)]
  have heT : (fun z : E => ‖z‖^2 + T z) =ᶠ[𝓝 (radialContraction μ δ x)]
      fun z => modelPotential μ δ z - M := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const (hmap x hx)] with z hz
    dsimp only [T]
    rw [gluedPotential_inner hrR H P hinner hz.le]
    dsimp [P, logNormSq, modelPotential]
    ring
  rw [ddc_congr J heT, ddc_sub_const J (contDiff_modelPotential μ hδ).contDiffAt,
    radialContraction_pullback J hsk hμ hδ]

end
end ComplexPotential

namespace TensorCalculus

open Set Filter
open scoped Topology ContDiff

variable {E : Type u42} {F : Type u43} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

local instance pullbackOneTensorGroup : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance pullbackOneTensorSpace : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance pullbackTwoTensorGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance pullbackTwoTensorSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

def pullbackOneForm (f : E → F) (γ : F → F →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℝ :=
  (γ (f x)).comp (fderiv ℝ f x)

@[simp] theorem pullbackOneForm_apply (f : E → F) (γ : F → F →L[ℝ] ℝ) (x a : E) :
    pullbackOneForm f γ x a = γ (f x) (fderiv ℝ f x a) := rfl

theorem fderiv_pullbackOneForm {f : E → F} {γ : F → F →L[ℝ] ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hd : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hγ : DifferentiableAt ℝ γ (f x)) (a b : E) :
    fderiv ℝ (pullbackOneForm f γ) x a b =
      fderiv ℝ γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) +
        γ (f x) (fderiv ℝ (fderiv ℝ f) x a b) := by
  unfold pullbackOneForm
  rw [fderiv_clm_comp (c := fun y => γ (f y)) (hγ.comp x hf) hd]
  rw [show fderiv ℝ (fun y => γ (f y)) x = (fderiv ℝ γ (f x)).comp (fderiv ℝ f x) by
    exact fderiv_comp x hγ hf]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  ring

theorem exteriorD_pullbackOneForm {f : E → F} {γ : F → F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hγ : DifferentiableAt ℝ γ (f x)) (a b : E) :
    exteriorD (pullbackOneForm f γ) x a b =
      exteriorD γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hf' := hf.differentiableAt (by simp)
  have hs := hf.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [exteriorD_apply, fderiv_pullbackOneForm hf' hd hγ]
  rw [hs.eq a b]
  ring

end
end TensorCalculus

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u44} {F : Type u45} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

theorem dc_comp (J : E →L[ℝ] E) (K : F →L[ℝ] F) {f : E → F} {φ : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x))
    (hCR : ∀ a, fderiv ℝ f x (J a) = K (fderiv ℝ f x a)) :
    dc J (φ ∘ f) x = pullbackOneForm f (dc K φ) x := by
  ext a
  rw [dc_apply, fderiv_comp x hφ hf, ContinuousLinearMap.comp_apply, hCR,
    pullbackOneForm_apply, dc_apply]

theorem ddc_comp (J : E →L[ℝ] E) (K : F →L[ℝ] F) {f : E → F} {φ : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hφ : ContDiffAt ℝ ∞ φ (f x))
    (hCR : ∀ᶠ y in 𝓝 x, ∀ a, fderiv ℝ f y (J a) = K (fderiv ℝ f y a)) (a b : E) :
    ddc J (φ ∘ f) x a b = ddc K φ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (φ ∘ f) =ᶠ[𝓝 x] pullbackOneForm f (dc K φ) := by
    filter_upwards [(hf.of_le h1).eventually (by simp),
      hf.continuousAt ((hφ.of_le h1).eventually (by simp)), hCR] with y hy hz hc
    exact dc_comp J K (hy.differentiableAt one_ne_zero)
      ((show ContDiffAt ℝ (1 : ℕ∞ω) φ (f y) from hz).differentiableAt one_ne_zero) hc
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  exact exteriorD_pullbackOneForm hf ((contDiffAt_dc K hφ).differentiableAt (by simp)) a b

end
end ComplexPotential

namespace ComplexPotential

open Set Filter TensorCalculus
open scoped ContDiff Topology

noncomputable section

variable {E : Type u46} {F : Type u47} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexStructure (E : Type u48) [NormedAddCommGroup E] [NormedSpace ℂ E] : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] theorem complexStructure_apply (a : E) : complexStructure E a = Complex.I • a := rfl

theorem complexStructure_sq (a : E) : complexStructure E (complexStructure E a) = -a := by
  simp [complexStructure_apply, smul_smul]

theorem complexStructure_norm (a : E) : ‖complexStructure E a‖ = ‖a‖ := by
  simp [complexStructure_apply, norm_smul]

theorem fderiv_commutes_complexStructure {f : E → F} {x : E}
    (hf : DifferentiableAt ℂ f x) (a : E) :
    fderiv ℝ f x (complexStructure E a) = complexStructure F (fderiv ℝ f x a) := by
  rw [hf.fderiv_restrictScalars ℝ]
  simp [complexStructure_apply]

theorem complexStructure_skew {G : Type u49} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (a b : G) :
    let : InnerProductSpace ℝ G := InnerProductSpace.complexToReal
    inner (𝕜 := ℝ) a (complexStructure G b) = -inner (𝕜 := ℝ) (complexStructure G a) b := by
  let : InnerProductSpace ℝ G := InnerProductSpace.complexToReal
  simp [real_inner_eq_re_inner ℂ, inner_smul_right, inner_smul_left]

theorem IsPSHAt.holomorphic_comp {f : E → F} {φ : F → ℝ} {x : E}
    (hφ : IsPSHAt (complexStructure F) φ (f x))
    (hf : ContDiffAt ℝ ∞ f x) (hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y) :
    IsPSHAt (complexStructure E) (φ ∘ f) x := by
  refine ⟨hφ.1.comp x hf, fun a => ?_⟩
  rw [ddc_comp (complexStructure E) (complexStructure F) hf hφ.1
    (hhol.mono (fun y hy => fderiv_commutes_complexStructure hy)),
    fderiv_commutes_complexStructure hhol.self_of_nhds]
  exact hφ.2 _

end
end ComplexPotential

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.LogProfile


namespace OAI

universe u50 u51

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothLogProfile
noncomputable section

variable (b l u : ℝ)

def cutoff (t : ℝ) : ℝ := Real.smoothTransition ((t - l) / (u - l))

def slope (t : ℝ) : ℝ := b + cutoff l u t * (Real.exp t - b)

def profile (t : ℝ) : ℝ := Real.exp u + ∫ s in u..t, slope b l u s

theorem cutoff_smooth : ContDiff ℝ ∞ (cutoff l u) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem slope_smooth : ContDiff ℝ ∞ (slope b l u) :=
  contDiff_const.add ((cutoff_smooth l u).mul (Real.contDiff_exp.sub contDiff_const))

theorem cutoff_mem (t : ℝ) : cutoff l u t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_zero (hlu : l < u) {t : ℝ} (ht : t ≤ l) : cutoff l u t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu.le)

theorem cutoff_one (hlu : l < u) {t : ℝ} (ht : u ≤ t) : cutoff l u t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hlu)).mpr (by linarith)

theorem cutoff_monotone (hlu : l < u) : Monotone (cutoff l u) := by
  intro x y hxy
  exact Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hxy l) (sub_nonneg.mpr hlu.le))

theorem slope_left (hlu : l < u) {t : ℝ} (ht : t ≤ l) : slope b l u t = b := by
  simp [slope, cutoff_zero l u hlu ht]

theorem slope_right (hlu : l < u) {t : ℝ} (ht : u ≤ t) : slope b l u t = Real.exp t := by
  simp [slope, cutoff_one l u hlu ht]

theorem slope_pos (hb : 0 < b) (t : ℝ) : 0 < slope b l u t := by
  have hc := cutoff_mem l u t
  have he := Real.exp_pos t
  by_cases h : cutoff l u t = 1
  · simpa [slope, h] using he
  have hp : 0 < (1 - cutoff l u t) * b := mul_pos (sub_pos.mpr (lt_of_le_of_ne hc.2 h)) hb
  have hq : 0 ≤ cutoff l u t * Real.exp t := mul_nonneg hc.1 he.le
  unfold slope
  nlinarith

theorem slope_monotone (hlu : l < u) (hbl : b ≤ Real.exp l) : Monotone (slope b l u) := by
  intro x y hxy
  by_cases hyl : y ≤ l
  · rw [slope_left b l u hlu (hxy.trans hyl), slope_left b l u hlu hyl]
  have hly : l ≤ y := (not_le.mp hyl).le
  have hey : b ≤ Real.exp y := hbl.trans (Real.exp_le_exp.mpr hly)
  by_cases hxl : x ≤ l
  · rw [slope_left b l u hlu hxl]
    exact le_add_of_nonneg_right (mul_nonneg (cutoff_mem l u y).1 (sub_nonneg.mpr hey))
  have hlx : l ≤ x := (not_le.mp hxl).le
  have hex : b ≤ Real.exp x := hbl.trans (Real.exp_le_exp.mpr hlx)
  unfold slope
  apply add_le_add le_rfl
  exact mul_le_mul (cutoff_monotone l u hlu hxy)
    (sub_le_sub_right (Real.exp_le_exp.mpr hxy) b) (sub_nonneg.mpr hex) (cutoff_mem l u y).1

theorem hasDerivAt_profile (t : ℝ) : HasDerivAt (profile b l u) (slope b l u t) t := by
  have hd : HasDerivAt (fun t => ∫ s in u..t, slope b l u s) (slope b l u t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (slope_smooth b l u).continuous.intervalIntegrable _ _
    · exact (slope_smooth b l u).continuous.stronglyMeasurableAtFilter _ _
    · exact (slope_smooth b l u).continuous.continuousAt
  exact hd.const_add _

@[simp] theorem deriv_profile : deriv (profile b l u) = slope b l u :=
  funext (fun t => (hasDerivAt_profile b l u t).deriv)

theorem profile_smooth : ContDiff ℝ ∞ (profile b l u) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (hasDerivAt_profile b l u t).differentiableAt,
    deriv_profile b l u ▸ slope_smooth b l u⟩

theorem deriv_profile_pos (hb : 0 < b) (t : ℝ) : 0 < deriv (profile b l u) t := by
  rw [deriv_profile]
  exact slope_pos b l u hb t

theorem second_deriv_profile_nonneg (hlu : l < u) (hbl : b ≤ Real.exp l) (t : ℝ) :
    0 ≤ deriv (deriv (profile b l u)) t := by
  rw [deriv_profile]
  exact (slope_monotone b l u hlu hbl).deriv_nonneg

theorem profile_sub (s t : ℝ) :
    profile b l u t - profile b l u s = ∫ x in s..t, slope b l u x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((slope_smooth b l u).continuous.intervalIntegrable (μ := volume) u s)
    ((slope_smooth b l u).continuous.intervalIntegrable s t)
  unfold profile
  linarith

theorem profile_right (hlu : l < u) {t : ℝ} (ht : u ≤ t) :
    profile b l u t = Real.exp t := by
  have he : (∫ s in u..t, slope b l u s) = Real.exp t - Real.exp u := by
    calc
      _ = ∫ s in u..t, Real.exp s := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact slope_right b l u hlu (le_trans (by simp [ht]) hs.1)
      _ = Real.exp t - Real.exp u := by simp
  simp [profile, he]

theorem profile_left (hlu : l < u) {t : ℝ} (ht : t ≤ l) :
    profile b l u t = b * t + (profile b l u l - b * l) := by
  have he : (∫ s in t..l, slope b l u s) = (l - t) * b := by
    calc
      _ = ∫ s in t..l, b := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact slope_left b l u hlu (le_trans hs.2 (by simp [ht]))
      _ = (l - t) * b := by simp
  have hdiff := profile_sub b l u t l
  rw [he] at hdiff
  nlinarith

end
end SmoothLogProfile

namespace ComplexPotential

open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u50} {F : Type u51} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem exists_ball_from_holomorphic_zero {Ω : Set E} (hΩ : IsOpen Ω) (hΩ0 : (0 : E) ∈ Ω)
    {f : E → F} (hf : AnalyticOnNhd ℂ f Ω)
    (hfzero : ∀ x ∈ Ω, f x = 0 ↔ x = 0)
    {k : ℕ} (hk : 1 ≤ k) (ho : f =O[𝓝 (0 : E)] (fun x : E => ‖x‖^k))
    (hcompact : ∀ s : ℝ, 0 < s → s < 1 → IsCompact {x | x ∈ Ω ∧ ‖f x‖^2 ≤ s})
    {a : ℝ} (ha : 0 < a) (hak : a < (k : ℝ)) :
    let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ∃ Q : E ≃ₜ E, ContDiff ℝ ∞ (Q : E → E) ∧ ContDiff ℝ ∞ (Q.symm : E → E) ∧
      (∀ x : E, ‖x‖^2 < a → Q x ∈ Ω ∧ ‖f (Q x)‖^2 < 1) ∧
      ∀ x : E, ‖x‖^2 < a → ∀ v w : E,
        ddc (complexStructure E) (fun y => ‖y‖^2 + ‖f y‖^2) (Q x)
          (fderiv ℝ (Q : E → E) x v) (fderiv ℝ (Q : E → E) x w) =
            standardTensor (complexStructure E) v w := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  let τ : E → ℝ := fun x => ‖f x‖^2
  let U : Set E := {x | x ∈ Ω ∧ τ x < 1}
  have hτsmooth (x : E) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ τ x :=
    (contDiff_norm_sq ℝ).contDiffAt.comp x ((hf x hx).contDiffAt.restrict_scalars ℝ)
  have hτcont : ContinuousOn τ Ω := fun x hx => (hτsmooth x hx).continuousAt.continuousWithinAt
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact inter_mem (hΩ.mem_nhds hx.1)
      ((hτsmooth x hx.1).continuousAt.eventually_lt continuousAt_const hx.2)
  have hf0 : f 0 = 0 := (hfzero 0 hΩ0).mpr rfl
  have hτ0 : τ 0 = 0 := by simp [τ, hf0]
  have hU0 : (0 : E) ∈ U := ⟨hΩ0, by rw [hτ0]; norm_num⟩
  have hτpsh (x : E) (hx : x ∈ U) : IsPSHAt (complexStructure E) τ x := by
    have hn : IsPSHAt (complexStructure F) (fun z : F => ‖z‖^2) (f x) := by
      refine ⟨(contDiff_norm_sq ℝ).contDiffAt, fun v => ?_⟩
      rw [ddc_norm_sq _ (complexStructure_skew), standardTensor_complex_line _ complexStructure_norm]
      exact sq_nonneg _
    apply hn.holomorphic_comp ((hf x hx.1).contDiffAt.restrict_scalars ℝ)
    filter_upwards [hΩ.mem_nhds hx.1] with y hy
    exact (hf y hy).differentiableAt
  have hpos (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) : 0 < τ x := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (fun hh => hx0 ((hfzero x hx.1).mp hh)))
  have hlogpsh (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) :
      IsPSHAt (complexStructure E) (Real.log ∘ τ) x := by
    have hn := isPSHAt_logNormSq (complexStructure F) complexStructure_skew
      complexStructure_norm complexStructure_sq (δ := 0) le_rfl
        (show 0 < ‖f x‖^2 + 0 by simpa [τ] using hpos x hx hx0)
    have hh := hn.holomorphic_comp ((hf x hx.1).contDiffAt.restrict_scalars ℝ) (by
      filter_upwards [hΩ.mem_nhds hx.1] with y hy
      exact (hf y hy).differentiableAt)
    simpa only [logNormSq, add_zero, Function.comp_def, τ] using hh
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  obtain ⟨b, hab, hb1⟩ := exists_between ((div_lt_one hkpos).mpr hak)
  have hb : 0 < b := (div_pos ha hkpos).trans hab
  obtain ⟨l, hbl, hl0⟩ := exists_between (Real.log_neg hb hb1)
  obtain ⟨u, hlu, hu0⟩ := exists_between hl0
  have hble : b ≤ Real.exp l := by
    exact ((Real.log_le_iff_le_exp hb).mp hbl.le)
  let H : E → ℝ := SmoothLogProfile.profile b l u ∘ Real.log ∘ τ
  have hH (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) : IsPSHAt (complexStructure E) H x := by
    exact (hlogpsh x hx hx0).scalar_comp _ complexStructure_sq
      (SmoothLogProfile.profile_smooth b l u).contDiffAt
      (SmoothLogProfile.deriv_profile_pos b l u hb _).le
      (SmoothLogProfile.second_deriv_profile_nonneg b l u hlu hble _)
  have htail (x : E) (hx : x ∈ U) (ht : Real.exp u ≤ τ x) : H x = τ x := by
    have htpos : 0 < τ x := (Real.exp_pos u).trans_le ht
    have hlog : u ≤ Real.log (τ x) := by
      simpa using Real.log_le_log (Real.exp_pos u) ht
    change SmoothLogProfile.profile b l u (Real.log (τ x)) = τ x
    rw [SmoothLogProfile.profile_right b l u hlu hlog, Real.exp_log htpos]
  obtain ⟨C, hC, hCb⟩ := ho.exists_pos
  have hev : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖^k ∧ τ x < Real.exp l := by
    filter_upwards [hCb.bound,
      (hτsmooth 0 hΩ0).continuousAt.eventually_lt continuousAt_const
        (show τ 0 < Real.exp l by rw [hτ0]; exact Real.exp_pos l)] with x hx ht
    exact ⟨by simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hx, ht⟩
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hev
  let ρ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  let C₁ := b * (2 * Real.log C) + (SmoothLogProfile.profile b l u l - b * l)
  have hpole (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) (hnorm : ‖x‖ ≤ ρ) :
      H x ≤ (b * k) * Real.log (‖x‖^2) + C₁ := by
    have hdist : dist x 0 < ε := by rw [dist_zero_right]; exact hnorm.trans_lt (half_lt_self hε)
    obtain ⟨hbound, hsmall⟩ := hεprop hdist
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfxp : 0 < ‖f x‖ := norm_pos_iff.mpr (fun hh => hx0 ((hfzero x hx.1).mp hh))
    have hlogl : Real.log (τ x) ≤ l := (Real.log_le_iff_le_exp (hpos x hx hx0)).mpr hsmall.le
    change SmoothLogProfile.profile b l u (Real.log (τ x)) ≤ _
    rw [SmoothLogProfile.profile_left b l u hlu hlogl]
    have hlg := Real.log_le_log hfxp hbound
    rw [Real.log_mul hC.ne' (pow_pos hxp k).ne', Real.log_pow] at hlg
    have hmul := mul_le_mul_of_nonneg_left hlg hb.le
    dsimp [τ, C₁]
    rw [Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  apply exists_ball_from_logarithmic_pole (complexStructure E) complexStructure_skew
    complexStructure_norm complexStructure_sq hU hU0 hτpsh hτ0 hH
  · intro s hs hs1
    have he : {x | x ∈ U ∧ τ x ≤ s} = {x | x ∈ Ω ∧ ‖f x‖^2 ≤ s} := by
      ext x
      constructor
      · exact fun hx => ⟨hx.1.1, hx.2⟩
      · exact fun hx => ⟨⟨hx.1, hx.2.trans_lt hs1⟩, hx.2⟩
    rw [he]
    exact hcompact s hs hs1
  · exact Real.exp_lt_one_iff.mpr hu0
  · exact hρ
  · exact htail
  · exact hpole
  · exact ha
  · exact (div_lt_iff₀ hkpos).mp hab

end
end ComplexPotential

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.LensMap


namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology

open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
noncomputable section

def term (n : ℕ) (w : ℂ) : ℂ := (-1)^n * w^(2*n+1) / (2*n+1)^2

def termDeriv (n : ℕ) (w : ℂ) : ℂ := (-1)^n * w^(2*n) / (2*n+1)

def F (w : ℂ) : ℂ := (8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, term n w

theorem hasDerivAt_term (n : ℕ) (w : ℂ) : HasDerivAt (term n) (termDeriv n w) w := by
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  convert (((hasDerivAt_id w).pow (2*n+1)).const_mul ((-1 : ℂ)^n)).div_const
    ((2*(n : ℂ)+1)^2) using 1 <;> try rfl
  simp only [termDeriv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.add_sub_cancel]
  field_simp [hn]
  rfl

@[simp] theorem term_zero (n : ℕ) : term n 0 = 0 := by simp [term]

@[simp] theorem F_zero : F 0 = 0 := by simp [F]

theorem norm_termDeriv_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ r) (n : ℕ) : ‖termDeriv n w‖ ≤ r^n := by
  have hn : (1 : ℝ) ≤ 2 * n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  calc
    ‖termDeriv n w‖ = ‖w‖^(2*n) / (2*n+1) := by
      simp only [termDeriv, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 1
      norm_cast
    _ ≤ r^(2*n) := (div_le_self (pow_nonneg (norm_nonneg _) _) hn).trans
      (pow_le_pow_left₀ (norm_nonneg _) hw _)
    _ ≤ r^n := pow_le_pow_of_le_one hr hr1 (by omega)

theorem summable_termDeriv {w : ℂ} (hw : ‖w‖ < 1) : Summable (fun n => termDeriv n w) := by
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg w) hw)
    (norm_termDeriv_le (norm_nonneg w) hw.le le_rfl)

theorem hasDerivAt_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt F ((8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, termDeriv n w) w := by
  obtain ⟨r, hwr, hr1⟩ := exists_between hw
  have hr : 0 < r := (norm_nonneg w).trans_lt hwr
  have hh := hasDerivAt_tsum_of_isPreconnected
    (summable_geometric_of_lt_one hr.le hr1) Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n z _ => hasDerivAt_term n z)
    (fun n z hz => norm_termDeriv_le hr.le hr1.le ((by simpa [Metric.mem_ball] using hz : ‖z‖ < r).le) n)
    (show (0 : ℂ) ∈ Metric.ball 0 r by simpa using hr)
    (show Summable (fun n => term n (0 : ℂ)) by simp)
    (show w ∈ Metric.ball 0 r by simpa using hwr)
  exact hh.const_mul _

theorem analyticOnNhd_F : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro w hw
  exact (hasDerivAt_F (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    w * deriv F w = (8 / (Real.pi^2) : ℝ) * Complex.arctan w := by
  rw [(hasDerivAt_F hw).deriv, mul_left_comm, ← tsum_mul_left]
  congr 1
  have he : (fun n : ℕ => w * termDeriv n w) =
      (fun n : ℕ => (-1)^n * w^(2*n+1) / (2*n+1)) := by
    funext n
    dsimp [termDeriv]
    rw [pow_succ]
    ring
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using (Complex.hasSum_arctan hw).tsum_eq

theorem norm_term_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖term n w‖ ≤ 1 / ((n : ℝ)+1)^2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  calc
    ‖term n w‖ = ‖w‖^(2*n+1) / (2*(n : ℝ)+1)^2 := by
      simp only [term, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 2
      norm_cast
    _ ≤ 1 / (2*(n : ℝ)+1)^2 := div_le_div_of_nonneg_right
      (pow_le_one₀ (norm_nonneg _) hw) (sq_nonneg _)
    _ ≤ 1 / ((n : ℝ)+1)^2 := one_div_le_one_div_of_le (sq_pos_of_pos hn)
      (pow_le_pow_left₀ hn.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) 2)

theorem summable_bound : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))

theorem summable_term {w : ℂ} (hw : ‖w‖ ≤ 1) : Summable (fun n => term n w) :=
  Summable.of_norm_bounded summable_bound (norm_term_le hw)

theorem continuousOn_F_closedBall : ContinuousOn F (Metric.closedBall 0 1) := by
  apply ContinuousOn.const_mul _ _
  apply continuousOn_tsum (fun n => (by unfold term; fun_prop : Continuous (term n)).continuousOn)
    summable_bound
  intro n w hw
  exact norm_term_le (by simpa using hw) n

theorem F_norm_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖F w‖ ≤ (8 / Real.pi^2) * ∑' n : ℕ, 1 / ((n : ℝ)+1)^2 := by
  have hc : 0 ≤ 8 / Real.pi^2 := by positivity
  rw [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (norm_tsum_le_tsum_norm (summable_term hw).norm).trans
    (Summable.tsum_le_tsum (norm_term_le hw) (summable_term hw).norm summable_bound)

@[simp] theorem F_neg (w : ℂ) : F (-w) = -F w := by
  have he : (fun n : ℕ => term n (-w)) = fun n : ℕ => -term n w := by
    funext n
    simp only [term]
    rw [(show Odd (2*n+1) by exact ⟨n, by omega⟩).neg_pow]
    ring
  simp only [F, he, tsum_neg, mul_neg]

@[simp] theorem F_conj (w : ℂ) : F ((starRingEnd ℂ) w) = (starRingEnd ℂ) (F w) := by
  have he : (fun n : ℕ => term n ((starRingEnd ℂ) w)) = fun n : ℕ => conjCLE (term n w) := by
    funext n
    simp [term, map_ofNat]
  simp only [F, he, ← conjCLE.map_tsum]
  simp [map_ofNat]

def cayley (w : ℂ) : ℂ := (1 + w*I)/(1-w*I)

theorem cayley_re (w : ℂ) : (cayley w).re = (1 - ‖w‖^2) / normSq (1-w*I) := by
  rw [cayley, div_re, Complex.sq_norm]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add, normSq_apply]
  ring

theorem cayley_im (w : ℂ) : (cayley w).im = 2*w.re / normSq (1-w*I) := by
  rw [cayley, div_im]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add]
  ring

theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  have hn : 1-w*I ≠ 0 := by
    intro h
    have he := congr_arg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, norm_I, mul_one] at he
    linarith
  rw [cayley_re]
  exact div_pos (by nlinarith [norm_nonneg w]) (normSq_pos.mpr hn)

theorem arctan_re_eq {w : ℂ} (hw : ‖w‖ < 1) :
    (Complex.arctan w).re = (1/2 : ℝ) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (cayley_re_pos hw)))
  have ht := Real.arctan_tan harg.1 harg.2
  rw [Complex.tan_arg, cayley_re, cayley_im] at ht
  have hn : normSq (1-w*I) ≠ 0 := by
    apply ne_of_gt
    have h := cayley_re_pos hw
    rw [cayley_re] at h
    exact (div_pos_iff.mp h).resolve_right (by rintro ⟨_, hneg⟩; exact (normSq_nonneg _).not_gt hneg) |>.2
  have he : (2*w.re/normSq (1-w*I)) / ((1-‖w‖^2)/normSq (1-w*I)) =
      2*w.re/(1-‖w‖^2) := by field_simp
  rw [he] at ht
  rw [Complex.arctan, mul_re]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, log_im]
  change 0 - (-1/2) * (cayley w).arg = _
  rw [← ht]
  ring

theorem re_mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    (w * deriv F w).re = (4 / Real.pi^2) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  rw [mul_deriv_F hw, re_ofReal_mul, arctan_re_eq hw]
  ring

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem norm_one_add_mul_I_sq (w : ℂ) : ‖1+w*I‖^2 = 1-2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, add_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, add_im, one_im, mul_im, zero_add, add_zero]
  ring

theorem norm_one_sub_mul_I_sq (w : ℂ) : ‖1-w*I‖^2 = 1+2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, sub_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, sub_im, one_im, mul_im, add_zero]
  ring

theorem one_add_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1+w*I ≠ 0 := by
  intro h
  have he : w*I = -1 := eq_neg_of_add_eq_zero_right h
  have hh := congr_arg norm he
  simp only [norm_mul, norm_I, mul_one, norm_neg, norm_one] at hh
  linarith

theorem one_sub_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1-w*I ≠ 0 := by
  have h := one_add_mul_I_ne_zero (w := -w) (by simpa using hw)
  simpa only [neg_mul, sub_eq_add_neg] using h

theorem arctan_im_eq (w : ℂ) :
    (Complex.arctan w).im = -(1/2 : ℝ) * Real.log (‖1+w*I‖/‖1-w*I‖) := by
  rw [Complex.arctan, mul_im]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, zero_add, log_re, norm_div]
  ring

theorem arctan_im_pos {w : ℂ} (hw : ‖w‖ < 1) (hi : 0 < w.im) :
    0 < (Complex.arctan w).im := by
  have ha : 0 < ‖1+w*I‖ := norm_pos_iff.mpr (one_add_mul_I_ne_zero hw)
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1+w*I‖ < ‖1-w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_neg (div_pos ha hb) ((div_lt_one hb).mpr hab)
  linarith

theorem arctan_im_neg {w : ℂ} (hw : ‖w‖ < 1) (hi : w.im < 0) :
    (Complex.arctan w).im < 0 := by
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1-w*I‖ < ‖1+w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_pos ((one_lt_div hb).mpr hab)
  linarith

theorem arctan_im_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).im * w.im := by
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · exact mul_nonneg_of_nonpos_of_nonpos (arctan_im_neg hw hi).le hi.le
  · simp [hi]
  · exact (mul_pos (arctan_im_pos hw hi) hi).le

theorem arctan_re_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).re * w.re := by
  rw [arctan_re_eq hw]
  have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rcases lt_trichotomy w.re 0 with hi | hi | hi
  · have hr : Real.arctan (2*w.re/(1-‖w‖^2)) < 0 :=
      Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hn)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hi.le
  · simp [hi]
  · have hr : 0 < Real.arctan (2*w.re/(1-‖w‖^2)) :=
      Real.arctan_pos.mpr (div_pos (by linarith) hn)
    positivity

theorem arctan_div_re_pos {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    0 < (Complex.arctan w / w).re := by
  rw [div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hr := arctan_re_mul_nonneg hw
  have hi := arctan_im_mul_nonneg hw
  by_cases hre : w.re = 0
  · have him : w.im ≠ 0 := by
      intro h; apply hw0; exact Complex.ext (by simpa using hre) (by simpa using h)
    rcases lt_or_gt_of_ne him with him | him
    · have := mul_pos_of_neg_of_neg (arctan_im_neg hw him) him
      linarith
    · have := mul_pos (arctan_im_pos hw him) him
      linarith
  · have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have hp : 0 < (Complex.arctan w).re * w.re := by
      rw [arctan_re_eq hw]
      rcases lt_or_gt_of_ne hre with hre | hre
      · have h := Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos
          (by linarith : 2*w.re < 0) hn)
        exact mul_pos_of_neg_of_neg (by linarith) hre
      · have h := Real.arctan_pos.mpr (div_pos (by linarith : 0 < 2*w.re) hn)
        positivity
    linarith

@[simp] theorem deriv_F_zero : deriv F 0 = (8 / Real.pi^2 : ℝ) := by
  rw [(hasDerivAt_F (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
  have he : (∑' n : ℕ, termDeriv n 0) = 1 := by
    rw [tsum_eq_single 0]
    · simp [termDeriv]
    · intro n hn
      have h : 2*n ≠ 0 := by omega
      simp [termDeriv, h]
  rw [he, mul_one]

theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  by_cases hw0 : w = 0
  · rw [hw0, deriv_F_zero, ofReal_re]
    positivity
  · have he : deriv F w = (8 / Real.pi^2 : ℝ) * (Complex.arctan w / w) := by
      apply (mul_left_cancel₀ hw0)
      rw [mul_deriv_F hw]
      field_simp
    rw [he, re_ofReal_mul]
    exact mul_pos (by positivity) (arctan_div_re_pos hw hw0)

theorem F_injOn : InjOn F (Metric.ball 0 1) := by
  intro x hx y hy hxy
  by_contra hn
  have hd : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖x+(t : ℂ)*(y-x)‖ < 1 := by
    intro t ht
    have hh := (convex_ball (0 : ℂ) 1).add_smul_sub_mem hx hy ht
    simpa only [Metric.mem_ball, dist_zero_right, Complex.real_smul] using hh
  let H : ℝ → ℝ := fun t => (F (x+(t : ℂ)*(y-x))/(y-x)).re
  have hh : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt H (deriv F (x+(t : ℂ)*(y-x))).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hc := ((hasDerivAt_id (t : ℂ)).mul_const (y-x)).const_add x
    have hm := (hf.comp (t : ℂ) hc).div_const (y-x)
    have he : deriv F (x+(t : ℂ)*(y-x)) * (1*(y-x)) / (y-x) =
        deriv F (x+(t : ℂ)*(y-x)) := by field_simp
    rw [he] at hm
    exact hm.real_of_complex
  have hmono : StrictMonoOn H (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  simp only [H, ofReal_zero, zero_mul, add_zero, ofReal_one, one_mul, add_sub_cancel] at hlt
  rw [hxy] at hlt
  exact lt_irrefl _ hlt

theorem re_F_imaginary (t : ℝ) : (F ((t : ℂ)*I)).re = 0 := by
  have h : (starRingEnd ℂ) ((t : ℂ)*I) = -((t : ℂ)*I) := by simp
  have he := F_conj ((t : ℂ)*I)
  rw [h, F_neg] at he
  have hre := congr_arg Complex.re he
  simp only [neg_re, conj_re] at hre
  linarith

theorem re_F_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < (F w).re := by
  let H : ℝ → ℝ := fun t => (F ((t : ℂ)+(w.im : ℂ)*I)).re
  have hseg : ∀ t ∈ Icc 0 w.re, ‖(t : ℂ)+(w.im : ℂ)*I‖ < 1 := by
    intro t ht
    have he : ‖(t : ℂ)+(w.im : ℂ)*I‖^2 = t^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hh : ‖w‖^2 = w.re^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hn : ‖w‖^2 < 1 := by nlinarith [norm_nonneg w]
    nlinarith [norm_nonneg ((t : ℂ)+(w.im : ℂ)*I), ht.1, ht.2]
  have hh : ∀ t ∈ Icc 0 w.re, HasDerivAt H (deriv F ((t : ℂ)+(w.im : ℂ)*I)).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hm := hf.comp (t : ℂ) ((hasDerivAt_id _).add_const ((w.im : ℂ)*I))
    convert hm.real_of_complex using 1 <;> first | rfl | simp
  have hmono : StrictMonoOn H (Icc 0 w.re) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 w.re)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    exact fun t ht => deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  have he : (w.re : ℂ)+(w.im : ℂ)*I = w := by simp
  simpa only [H, ofReal_zero, zero_add, re_F_imaginary, he] using hlt

theorem re_F_neg {w : ℂ} (hw : ‖w‖ < 1) (hr : w.re < 0) : (F w).re < 0 := by
  have h := re_F_pos (w := -w) (by simpa using hw) (by simpa using neg_pos.mpr hr)
  simpa only [F_neg, neg_re, neg_pos] using h

theorem re_F_eq_zero {w : ℂ} (hr : w.re = 0) : (F w).re = 0 := by
  have he : w = (w.im : ℂ)*I := by apply Complex.ext <;> simp [hr]
  rw [he, re_F_imaginary]

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.LensArea


namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def D : Set ℂ := F '' Metric.ball 0 1

def g : ℂ → ℂ := Function.invFunOn F (Metric.ball 0 1)

theorem g_F {w : ℂ} (hw : ‖w‖ < 1) : g (F w) = w :=
  F_injOn.leftInvOn_invFunOn (by simpa using hw)

theorem F_g {z : ℂ} (hz : z ∈ D) : F (g z) = z :=
  Function.invFunOn_eq hz

theorem norm_g_lt {z : ℂ} (hz : z ∈ D) : ‖g z‖ < 1 := by
  have h := Function.invFunOn_mem hz
  simpa [g] using h

theorem zero_mem_D : (0 : ℂ) ∈ D := ⟨0, by simp, F_zero⟩

@[simp] theorem g_zero : g 0 = 0 := by
  simpa using g_F (by simp : ‖(0 : ℂ)‖ < 1)

theorem g_eq_zero_iff {z : ℂ} (hz : z ∈ D) : g z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [← F_g hz, h, F_zero]
  · rintro rfl; exact g_zero

theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  intro h
  have hh := deriv_F_re_pos hw
  rw [h, zero_re] at hh
  exact lt_irrefl _ hh

theorem analyticOnNhd_g : AnalyticOnNhd ℂ g D := by
  rintro z ⟨w, hw, rfl⟩
  have hw' : ‖w‖ < 1 := by simpa using hw
  apply (analyticAt_comp_iff_of_deriv_ne_zero (analyticOnNhd_F w hw)
    (deriv_F_ne_zero hw')).mp
  apply analyticAt_id.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
  exact (g_F (by simpa using hv)).symm

theorem isOpen_D : IsOpen D := by
  rcases analyticOnNhd_F.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with h | h
  · obtain ⟨c, hc⟩ := h
    have hz : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
    have hh : (1/2 : ℂ) ∈ Metric.ball 0 1 := by norm_num [Metric.mem_ball, norm_div]
    have he := F_injOn hz hh ((hc 0 hz).trans (hc _ hh).symm)
    norm_num at he
  · exact h _ Subset.rfl Metric.isOpen_ball

theorem isBounded_D : Bornology.IsBounded D := by
  apply ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn continuousOn_F_closedBall).isBounded.subset
  exact image_mono Metric.ball_subset_closedBall

theorem continuousOn_g : ContinuousOn g D := analyticOnNhd_g.continuousOn

theorem g_injOn : InjOn g D := by
  intro z hz w hw he
  rw [← F_g hz, ← F_g hw, he]

theorem deriv_g_F {w : ℂ} (hw : ‖w‖ < 1) : deriv g (F w) = (deriv F w)⁻¹ := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hg := (analyticOnNhd_g _ hFw).differentiableAt.hasDerivAt
  have hf := (hasDerivAt_F hw).differentiableAt.hasDerivAt
  have hc := hg.comp w hf
  have he : g ∘ F =ᶠ[𝓝 w] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hw : w ∈ Metric.ball 0 1)] with z hz
    exact g_F (by simpa using hz)
  have hid := hc.congr_of_eventuallyEq he.symm
  have hm : deriv g (F w) * deriv F w = 1 := hid.unique (hasDerivAt_id w)
  apply mul_right_cancel₀ (deriv_F_ne_zero hw)
  rw [hm, inv_mul_cancel₀ (deriv_F_ne_zero hw)]

theorem deriv_g_ne_zero {z : ℂ} (hz : z ∈ D) : deriv g z ≠ 0 := by
  rw [← F_g hz, deriv_g_F (norm_g_lt hz)]
  exact inv_ne_zero (deriv_F_ne_zero (norm_g_lt hz))

theorem re_g_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) : 0 < (g z).re := by
  by_contra h
  rcases (le_of_not_gt h).eq_or_lt with he | he
  · have hh := re_F_eq_zero he
    rw [F_g hz] at hh
    linarith
  · have hh := re_F_neg (norm_g_lt hz) he
    rw [F_g hz] at hh
    linarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def T (r : ℝ) : ℝ := (F ((r : ℂ)*I)).im

theorem F_imaginary (r : ℝ) : F ((r : ℂ)*I) = (T r : ℂ)*I := by
  apply Complex.ext <;> simp [T, re_F_imaginary]

@[simp] theorem T_zero : T 0 = 0 := by simp [T]

@[simp] theorem T_neg (r : ℝ) : T (-r) = -T r := by simp [T]

theorem summable_odd_sq : Summable (fun n : ℕ => 1/(2*(n : ℝ)+1)^2) := by
  have h := hasSum_zeta_two.summable.comp_injective (i := fun n : ℕ => 2*n+1)
    (by intro n m h; dsimp at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

theorem tsum_odd_sq : (∑' n : ℕ, 1/(2*(n : ℝ)+1)^2) = Real.pi^2/8 := by
  have he : HasSum (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^2) (Real.pi^2/24) := by
    have hh : HasSum (fun n : ℕ => (1/4 : ℝ) * (1/(n : ℝ)^2))
        ((1/4 : ℝ)*(Real.pi^2/6)) := hasSum_zeta_two.mul_left _
    have eqf : (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^2) =
        (fun n : ℕ => (1/4 : ℝ)*(1/(n : ℝ)^2)) := by
      funext n
      push_cast
      simp only [mul_pow, div_mul_eq_div_div]
      norm_num
      ring
    rw [eqf, show Real.pi^2/24 = (1/4 : ℝ)*(Real.pi^2/6) by ring]
    exact hh
  have ho : HasSum (fun n : ℕ => 1/((2*n+1 : ℕ) : ℝ)^2)
      (∑' n : ℕ, 1/(2*(n : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using summable_odd_sq.hasSum
  have h := (HasSum.even_add_odd (f := fun n : ℕ => 1/(n : ℝ)^2) he ho).unique hasSum_zeta_two
  linarith

@[simp] theorem F_I : F (I : ℂ) = (I : ℂ) := by
  have he : (fun n : ℕ => term n I) = (fun n : ℕ => (I : ℂ) * ((1/(2*(n : ℝ)+1)^2 : ℝ) : ℂ)) := by
    funext n
    have hp : (-1 : ℂ)^n * (I : ℂ)^(2*n+1) = (I : ℂ) := by
      rw [pow_succ, pow_mul, I_sq]
      have h1 : (-1 : ℂ)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
      linear_combination I * h1
    simp only [term, hp, ofReal_div, ofReal_one, ofReal_pow, ofReal_add, ofReal_mul,
      ofReal_ofNat, ofReal_natCast]
    ring
  rw [F, he, tsum_mul_left, ← Complex.ofReal_tsum, tsum_odd_sq]
  push_cast
  field_simp [Real.pi_ne_zero]

@[simp] theorem T_one : T 1 = 1 := by simp [T]

theorem continuousOn_T : ContinuousOn T (Icc (-1) 1) := by
  have hh : ContinuousOn (fun r : ℝ => F ((r : ℂ)*I)) (Icc (-1) 1) := by
    apply continuousOn_F_closedBall.comp (by fun_prop)
    intro r hr
    simpa [Metric.mem_closedBall, norm_mul, norm_real, Real.norm_eq_abs, abs_le] using hr
  exact Complex.continuous_im.comp_continuousOn hh

theorem hasDerivAt_T {r : ℝ} (hr : |r| < 1) :
    HasDerivAt T (deriv F ((r : ℂ)*I)).re r := by
  have hf := (hasDerivAt_F (w := (r : ℂ)*I) (by simpa [norm_mul] using hr)).differentiableAt.hasDerivAt
  have hc := hf.comp (r : ℂ) ((hasDerivAt_id _).mul_const I)
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hc.comp_ofReal
  convert hm using 1 <;> first | rfl | simp

theorem strictMonoOn_T : StrictMonoOn T (Icc (-1) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) continuousOn_T
  · intro r hr
    have h : |r| < 1 := by simpa only [interior_Icc, mem_Ioo, abs_lt] using hr
    exact (hasDerivAt_T h).hasDerivWithinAt
  · intro r hr
    have h : |r| < 1 := by simpa only [interior_Icc, mem_Ioo, abs_lt] using hr
    exact deriv_F_re_pos (by simpa [norm_mul] using h)

theorem T_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 0 < T r := by
  have h := strictMonoOn_T (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) ⟨by linarith, hr1⟩ hr
  simpa using h

theorem T_lt_one {r : ℝ} (hr : -1 ≤ r) (hr1 : r < 1) : T r < 1 := by
  have h := strictMonoOn_T ⟨hr, hr1.le⟩ (by norm_num : (1 : ℝ) ∈ Icc (-1) 1) hr1
  simpa using h

theorem exists_T_eq {t : ℝ} (ht : |t| < 1) : ∃ r ∈ Ioo (-1) 1, T r = t := by
  have hh : t ∈ Icc (T (-1)) (T 1) := by simpa using
    ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) continuousOn_T hh
  refine ⟨r, ⟨hr.1.lt_of_ne ?_, hr.2.lt_of_ne ?_⟩, he⟩
  · intro h
    rw [← h] at he
    have h' : T (-1) = -1 := by simp
    rw [h'] at he
    linarith [abs_lt.mp ht |>.1]
  · intro h
    rw [h, T_one] at he
    linarith [abs_lt.mp ht |>.2]

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def A (w : ℂ) : ℝ := (w * deriv F w).re

theorem A_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < A w := by
  rw [A, re_mul_deriv_F hw]
  apply mul_pos (by positivity)
  apply Real.arctan_pos.mpr
  apply div_pos (by linarith)
  nlinarith [norm_nonneg w]

theorem hasDerivAt_horizontal_g {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => g ((h : ℂ)+(t : ℂ)*I))
      (deriv g ((v : ℂ)+(t : ℂ)*I)) v := by
  have hg := (analyticOnNhd_g _ hz).differentiableAt.hasDerivAt
  have hc := hg.comp (v : ℂ) ((hasDerivAt_id _).add_const ((t : ℂ)*I))
  convert hc.comp_ofReal using 1 <;> first | rfl | simp only [mul_one]

theorem horizontal_normSq_deriv {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2)
      (2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2) v := by
  have hh := (hasDerivAt_horizontal_g hz).norm_sq
  have he : deriv g ((v : ℂ)+(t : ℂ)*I) = (deriv F (g ((v : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [he] at hh
  convert hh using 1
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  simp only [A, Complex.sq_norm, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.conj_re, Complex.conj_im, RCLike.re_to_complex]
  ring

theorem horizontal_normSq_deriv_pos {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 < v) :
    0 < 2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2 := by
  apply div_pos
  · exact mul_pos (by norm_num) (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hv)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz)))

theorem horizontal_segment_mem {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (_hv : 0 ≤ v) {h : ℝ} (hh : h ∈ Icc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  let R := ‖g ((v : ℂ)+(t : ℂ)*I)‖
  have hR : R < 1 := norm_g_lt hz
  let C := F '' Metric.closedBall (0 : ℂ) R
  have hCD : C ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    simpa using hw'.trans_lt hR
  have hCc : IsCompact C := by
    apply (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    exact continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hR.le)
  have hCm {a : ℝ} : (a : ℂ)+(t : ℂ)*I ∈ C ↔
      (a : ℂ)+(t : ℂ)*I ∈ D ∧ ‖g ((a : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    constructor
    · rintro ⟨w, hw, he⟩
      have hw' : ‖w‖ ≤ R := by simpa using hw
      refine ⟨hCD ⟨w, hw, he⟩, ?_⟩
      rw [← he, g_F (hw'.trans_lt hR)]
      exact hw'
    · rintro ⟨ha, hr⟩
      exact ⟨g _, by simpa using hr, F_g ha⟩
  let S := Icc h v ∩ (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) ⁻¹' C
  have hSc : IsCompact S := isCompact_Icc.inter_right (hCc.isClosed.preimage (by fun_prop))
  have hvS : v ∈ S := ⟨⟨hh.2, le_rfl⟩, hCm.mpr ⟨hz, le_rfl⟩⟩
  obtain ⟨a, ha, hmin⟩ := hSc.exists_isMinOn ⟨v, hvS⟩ (continuous_id.continuousOn)
  have haD := (hCm.mp ha.2).1
  have haR := (hCm.mp ha.2).2
  have hha : h ≤ a := ha.1.1
  by_cases he : a = h
  · simpa only [he] using haD
  have hha' : h < a := lt_of_le_of_ne hha (Ne.symm he)
  have ha0 : 0 < a := hh.1.trans_lt hha'
  have hopen : IsOpen ((fun b : ℝ => (b : ℂ)+(t : ℂ)*I) ⁻¹' D) :=
    isOpen_D.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a haD
  let d := min (a-h) ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdh : d < a-h := by dsimp [d]; linarith [min_le_left (a-h) ε]
  have hdε : d < ε := by dsimp [d]; linarith [min_le_right (a-h) ε]
  let b := a-d
  have hhb : h < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hseg : ∀ x ∈ Icc b a, (x : ℂ)+(t : ℂ)*I ∈ D := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hx.2] : x-a ≤ 0)]
    have hxb : a-d ≤ x := hx.1
    linarith
  have hmono : StrictMonoOn (fun x : ℝ => ‖g ((x : ℂ)+(t : ℂ)*I)‖^2) (Icc b a) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc b a)
      (fun x hx => (horizontal_normSq_deriv (hseg x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (horizontal_normSq_deriv (hseg x (interior_subset hx))).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    apply horizontal_normSq_deriv_pos (hseg x hx')
    linarith [hx'.1, hh.1]
  have hnorm : ‖g ((b : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    have hm := hmono ⟨le_rfl, hba.le⟩ ⟨hba.le, le_rfl⟩ hba
    have hR0 : 0 ≤ R := norm_nonneg _
    nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I))]
  have hbS : b ∈ S := ⟨⟨hhb.le, hba.le.trans ha.1.2⟩,
    hCm.mpr ⟨hseg b ⟨le_rfl, hba.le⟩, hnorm⟩⟩
  have ham : a ≤ b := hmin hbS
  exact False.elim (not_le_of_gt hba ham)

theorem neg_conj_mem_D {z : ℂ} (hz : z ∈ D) : -(starRingEnd ℂ) z ∈ D := by
  rcases hz with ⟨w, hw, rfl⟩
  refine ⟨-(starRingEnd ℂ) w, by simpa using hw, ?_⟩
  simp

theorem g_neg_conj {z : ℂ} (hz : z ∈ D) : g (-(starRingEnd ℂ) z) = -(starRingEnd ℂ) (g z) := by
  apply F_injOn (by simpa using norm_g_lt (neg_conj_mem_D hz))
    (by simpa using norm_g_lt hz)
  rw [F_g (neg_conj_mem_D hz)]
  simp [F_g hz]

theorem conj_mem_D {z : ℂ} (hz : z ∈ D) : (starRingEnd ℂ) z ∈ D := by
  rcases hz with ⟨w, hw, rfl⟩
  exact ⟨(starRingEnd ℂ) w, by simpa using hw, by simp⟩

theorem g_conj {z : ℂ} (hz : z ∈ D) : g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z) := by
  apply F_injOn (by simpa using norm_g_lt (conj_mem_D hz))
    (by simpa using norm_g_lt hz)
  simp [F_g (conj_mem_D hz), F_g hz]

theorem horizontal_segment_mem_signed {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    {h : ℝ} (hh : h ∈ uIcc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  rcases le_total 0 v with hv | hv
  · rw [uIcc_of_le hv] at hh
    exact horizontal_segment_mem hz hv hh
  · rw [uIcc_of_ge hv] at hh
    have he (a : ℝ) : -((starRingEnd ℂ) ((a : ℂ)+(t : ℂ)*I)) = ((-a : ℝ) : ℂ)+(t : ℂ)*I := by
      apply Complex.ext <;> simp
    have hz' := neg_conj_mem_D hz
    rw [he] at hz'
    have hh' : -h ∈ Icc 0 (-v) := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have hhD := horizontal_segment_mem hz' (by linarith) hh'
    have hneg := neg_conj_mem_D hhD
    simpa only [he, neg_neg] using hneg

theorem axis_mem_D {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) : (t : ℂ)*I ∈ D := by
  simpa using horizontal_segment_mem_signed hz (left_mem_uIcc (a := 0) (b := v))

theorem g_axis_re_zero {t : ℝ} (ht : (t : ℂ)*I ∈ D) : (g ((t : ℂ)*I)).re = 0 := by
  have he : -(starRingEnd ℂ) ((t : ℂ)*I) = (t : ℂ)*I := by simp
  have hh := g_neg_conj ht
  rw [he] at hh
  have hr := congr_arg Complex.re hh
  simp only [neg_re, conj_re] at hr
  linarith

theorem axis_image {t : ℝ} (ht : (t : ℂ)*I ∈ D) :
    ∃ r ∈ Ioo (-1 : ℝ) 1, g ((t : ℂ)*I) = (r : ℂ)*I ∧ T r = t := by
  let r := (g ((t : ℂ)*I)).im
  have he : g ((t : ℂ)*I) = (r : ℂ)*I := by
    apply Complex.ext <;> simp [r, g_axis_re_zero ht]
  have hr : |r| < 1 := by
    have hh := norm_g_lt ht
    rw [he] at hh
    simpa [norm_mul] using hh
  refine ⟨r, abs_lt.mp hr, he, ?_⟩
  have hh := congr_arg Complex.im (F_g ht)
  rw [he] at hh
  simpa [T] using hh

theorem im_mem_Ioo {z : ℂ} (hz : z ∈ D) : z.im ∈ Ioo (-1 : ℝ) 1 := by
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa using hz
  obtain ⟨r, hr, _, ht⟩ := axis_image (axis_mem_D hz')
  rw [← ht]
  refine ⟨?_, T_lt_one hr.1.le hr.2⟩
  have h := strictMonoOn_T (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1) ⟨hr.1.le, hr.2.le⟩ hr.1
  simpa using h

theorem imaginary_mem_D {t : ℝ} (ht : |t| < 1) : (t : ℂ)*I ∈ D := by
  obtain ⟨r, hr, he⟩ := exists_T_eq ht
  exact ⟨(r : ℂ)*I, by simpa [Metric.mem_ball, norm_mul, abs_lt] using hr,
    by rw [F_imaginary r, he]⟩

theorem horizontal_radius_strictMono {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 ≤ v) : StrictMonoOn (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖) (Icc 0 v) := by
  have hm : StrictMonoOn (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2) (Icc 0 v) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 v)
      (fun h hh => (horizontal_normSq_deriv (horizontal_segment_mem hz hv hh)).continuousAt.continuousWithinAt)
      (fun h hh => (horizontal_normSq_deriv (horizontal_segment_mem hz hv (interior_subset hh))).hasDerivWithinAt)
    intro h hh
    apply horizontal_normSq_deriv_pos (horizontal_segment_mem hz hv (interior_subset hh))
    have hh' : h ∈ Ioo 0 v := by simpa only [interior_Icc] using hh
    exact hh'.1
  intro a ha b hb hab
  have hh := hm ha hb hab
  nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I)), norm_nonneg (g ((b : ℂ)+(t : ℂ)*I))]

theorem T_norm_g_axis {t : ℝ} (ht : (t : ℂ)*I ∈ D) : T ‖g ((t : ℂ)*I)‖ = |t| := by
  obtain ⟨r, hr, he, hT⟩ := axis_image ht
  rw [he]
  simp only [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
  rcases le_total 0 r with hr0 | hr0
  · rw [abs_of_nonneg hr0, ← hT, abs_of_nonneg]
    have h := strictMonoOn_T.monotoneOn (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
      ⟨hr.1.le, hr.2.le⟩ hr0
    simpa using h
  · rw [abs_of_nonpos hr0, T_neg, ← hT, abs_of_nonpos]
    have h := strictMonoOn_T.monotoneOn ⟨hr.1.le, hr.2.le⟩
      (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) hr0
    simpa using h

theorem vertical_gap_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) :
    0 < T ‖g z‖ - |z.im| := by
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa using hz
  have hnorm := horizontal_radius_strictMono hz' hr.le
    (left_mem_Icc.mpr hr.le) (right_mem_Icc.mpr hr.le) hr
  simp only [ofReal_zero, zero_add, re_add_im] at hnorm
  rw [← T_norm_g_axis (axis_mem_D hz')]
  have hh := strictMonoOn_T
    ⟨by linarith [norm_nonneg (g ((z.im : ℂ)*I))], (norm_g_lt (axis_mem_D hz')).le⟩
    ⟨by linarith [norm_nonneg (g z)], (norm_g_lt hz).le⟩ hnorm
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.LensEstimates


namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex MeasureTheory intervalIntegral
open scoped Topology ContDiff
noncomputable section

theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hi := integral_mono_on (μ := volume) hx (hc.intervalIntegrable 0 x)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun t _ => by
      apply (div_le_one (by positivity : 0 < 1+t^2)).mpr
      nlinarith [sq_nonneg t])
  simpa [integral_one_div_one_add_sq] using hi

theorem half_le_arctan {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x/2 ≤ Real.arctan x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hi := integral_mono_on (μ := volume) hx (intervalIntegrable_const (c := (1/2 : ℝ)))
    (hc.intervalIntegrable 0 x) (fun t ht => by
      apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
      have h0 := ht.1
      have h1 := ht.2.trans hx1
      nlinarith)
  simpa [integral_one_div_one_add_sq, div_eq_mul_inv] using hi

theorem reciprocal_arctan {x : ℝ} (hx : 0 < x) :
    1 / Real.arctan x ≤ 2 / Real.pi + 2/x := by
  have ha : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  rcases le_total x 1 with hx1 | hx1
  · have hh := half_le_arctan hx.le hx1
    have hdiv : 1 / Real.arctan x ≤ 2/x := by
      apply (div_le_div_iff₀ ha hx).mpr
      linarith
    apply hdiv.trans
    have hp : 0 < 2 / Real.pi := by positivity
    linarith
  · have hh : Real.pi / 2 - Real.arctan x ≤ 1/x := by
      rw [← Real.arctan_inv_of_pos hx]
      simpa only [one_div] using arctan_le_self (inv_nonneg.mpr hx.le)
    have hA : Real.pi / 4 ≤ Real.arctan x := by
      simpa using Real.arctan_strictMono.monotone hx1
    have hπA : 1 ≤ Real.pi * Real.arctan x := by
      have hp := Real.pi_gt_three
      nlinarith [mul_le_mul_of_nonneg_left hA Real.pi_pos.le]
    have hfirst : (Real.pi/2-Real.arctan x) / Real.arctan x ≤ (1/x)/Real.arctan x :=
      div_le_div_of_nonneg_right hh ha.le
    have hsecond : (2/Real.pi)*((1/x)/Real.arctan x) ≤ 2/x := by
      apply (le_div_iff₀ hx).mpr
      have he : (2/Real.pi)*((1/x)/Real.arctan x)*x = 2/(Real.pi*Real.arctan x) := by
        field_simp
      rw [he]
      apply (div_le_iff₀ (mul_pos Real.pi_pos ha)).mpr
      linarith
    have hthird := mul_le_mul_of_nonneg_left hfirst
      (by positivity : 0 ≤ 2/Real.pi)
    have he : (2/Real.pi)*((Real.pi/2-Real.arctan x)/Real.arctan x) =
        1/Real.arctan x - 2/Real.pi := by field_simp
    rw [he] at hthird
    linarith

def circleTop (r s : ℝ) : ℂ := (r : ℂ) * ((Real.sin s : ℂ)+(Real.cos s : ℂ)*I)

@[simp] theorem circleTop_re (r s : ℝ) : (circleTop r s).re = r * Real.sin s := by
  simp only [circleTop, mul_re, add_re, ofReal_re, ofReal_im, I_im, I_re,
    mul_zero, mul_one, sub_zero, zero_mul, add_zero]

@[simp] theorem circleTop_im (r s : ℝ) : (circleTop r s).im = r * Real.cos s := by
  simp only [circleTop, mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_im, I_re,
    mul_zero, mul_one, zero_add, zero_mul, add_zero]

theorem norm_circleTop (r s : ℝ) : ‖circleTop r s‖ = |r| := by
  have hh : ‖circleTop r s‖^2 = r^2 := by
    rw [Complex.sq_norm, normSq_apply, circleTop_re, circleTop_im]
    nlinarith [Real.sin_sq_add_cos_sq s]
  nlinarith [sq_abs r, norm_nonneg (circleTop r s), abs_nonneg r]

@[simp] theorem circleTop_zero (r : ℝ) : circleTop r 0 = (r : ℂ)*I := by
  simp [circleTop]

@[simp] theorem circleTop_pi_half (r : ℝ) : circleTop r (Real.pi/2) = (r : ℂ) := by
  simp [circleTop]

theorem continuous_circleTop (r : ℝ) : Continuous (circleTop r) := by
  unfold circleTop; fun_prop

theorem hasDerivAt_F_im_circleTop {r : ℝ} (hr : |r| < 1) (s : ℝ) :
    HasDerivAt (fun s => (F (circleTop r s)).im) (-A (circleTop r s)) s := by
  have hnorm : ‖(r : ℂ)*(Complex.sin s+Complex.cos s*I)‖ < 1 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    change ‖circleTop r s‖ < 1
    rw [norm_circleTop]
    exact hr
  have hd := ((Complex.hasDerivAt_sin (s : ℂ)).add
    ((Complex.hasDerivAt_cos (s : ℂ)).mul_const I)).const_mul (r : ℂ)
  have hf := (hasDerivAt_F hnorm).differentiableAt.hasDerivAt
  have hh := hf.comp (s : ℂ) hd
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hh.comp_ofReal
  convert hm using 1 <;> try rfl
  · funext x
    simp only [circleTop, ofReal_sin, ofReal_cos, Function.comp_apply, Pi.add_apply,
      Complex.imCLM_apply]
  · simp only [Complex.imCLM_apply, A, circleTop, ← ofReal_sin, ← ofReal_cos,
      mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, add_zero, zero_add, zero_sub, neg_re, neg_im]
    ring

theorem continuous_A_circleTop {r : ℝ} (hr : |r| < 1) :
    Continuous (fun s => A (circleTop r s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hs : circleTop r s ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, norm_circleTop] using hr
  exact Complex.continuous_re.continuousAt.comp
    (((continuous_circleTop r).continuousAt).mul
      (((analyticOnNhd_F _ hs).deriv.continuousAt).comp (continuous_circleTop r).continuousAt))

theorem gap_integral {r : ℝ} (hr : |r| < 1) (s : ℝ) :
    T r - (F (circleTop r s)).im = ∫ x in 0..s, A (circleTop r x) := by
  have hh := integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_F_im_circleTop hr x)
    ((continuous_A_circleTop hr).neg.intervalIntegrable 0 s)
  rw [intervalIntegral.integral_neg, circleTop_zero] at hh
  change -(∫ x in 0..s, A (circleTop r x)) = (F (circleTop r s)).im - T r at hh
  linarith

theorem A_circleTop_le {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : 0 ≤ s) (hs1 : s ≤ Real.pi/2) :
    A (circleTop r s) ≤ (8*r/(Real.pi^2*(1-r^2)))*s := by
  have hrabs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hr1
  have hnorm : ‖circleTop r s‖ < 1 := by simpa only [norm_circleTop] using hrabs
  rw [A, re_mul_deriv_F hnorm, circleTop_re, norm_circleTop, sq_abs]
  have hd : 0 < 1-r^2 := by nlinarith
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc ⟨hs, by linarith [Real.pi_pos]⟩
  have hx : 0 ≤ 2*(r*Real.sin s)/(1-r^2) := by positivity
  calc
    _ ≤ (4/Real.pi^2) * (2*(r*Real.sin s)/(1-r^2)) := by
      exact mul_le_mul_of_nonneg_left (arctan_le_self hx) (by positivity)
    _ ≤ (4/Real.pi^2) * (2*(r*s)/(1-r^2)) := by
      gcongr
      exact Real.sin_le hs
    _ = _ := by field_simp; ring

theorem gap_le_square {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : 0 ≤ s) (hs1 : s ≤ Real.pi/2) :
    T r - (F (circleTop r s)).im ≤ s^2/(1-r) := by
  have hrabs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hr1
  rw [gap_integral hrabs]
  have hh := integral_mono_on (μ := volume) hs ((continuous_A_circleTop hrabs).intervalIntegrable 0 s)
    ((show Continuous (fun x : ℝ => (8*r/(Real.pi^2*(1-r^2)))*x) from by fun_prop).intervalIntegrable 0 s)
    (fun x hx => A_circleTop_le hr hr1 hx.1 (hx.2.trans hs1))
  have he : (∫ x in 0..s, (8*r/(Real.pi^2*(1-r^2)))*x) =
      (4*r/(Real.pi^2*(1-r^2)))*s^2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [he] at hh
  apply hh.trans
  have hd : 0 < 1-r^2 := by nlinarith
  have h1 : 0 < 1-r := by linarith
  have hco : 4*r/(Real.pi^2*(1-r^2)) ≤ 1/(1-r) := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos Real.pi_pos) hd) h1).mpr
    have hp := Real.pi_gt_three
    have heq : 1-r^2 = (1-r)*(1+r) := by ring
    rw [heq]
    have haux : 4*r ≤ Real.pi^2*(1+r) := by
      have hp4 : 0 ≤ Real.pi^2-4 := by nlinarith
      nlinarith [mul_nonneg hp4 hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr haux) h1.le]
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using mul_le_mul_of_nonneg_right hco (sq_nonneg s)

theorem reciprocal_A_circleTop {r s : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hs : 0 < s) (hs1 : s ≤ Real.pi/2) :
    1 / A (circleTop r s) ≤ Real.pi/2 + Real.pi^3*(1-r)/s := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < 1-r^2 := by nlinarith
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs (by linarith [Real.pi_pos])
  have hnorm : ‖circleTop r s‖ < 1 := by simpa [norm_circleTop, abs_of_pos hr0] using hr1
  let X := 2*(r*Real.sin s)/(1-r^2)
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 < Real.arctan X := Real.arctan_pos.mpr hX
  have he : 1 / A (circleTop r s) = (Real.pi^2/4) * (1/Real.arctan X) := by
    rw [A, re_mul_deriv_F hnorm, circleTop_re, norm_circleTop, sq_abs]
    dsimp [X]
    field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (reciprocal_arctan hX)
    (by positivity : 0 ≤ Real.pi^2/4)
  apply hh.trans
  have hratio : (1+r)/r ≤ 4 := by
    apply (div_le_iff₀ hr0).mpr
    linarith
  have hsinbound : (1-r)/Real.sin s ≤ (Real.pi/2)*((1-r)/s) := by
    apply (div_le_iff₀ hsin).mpr
    have hx := Real.mul_le_sin hs.le hs1
    have hy : s ≤ (Real.pi/2)*Real.sin s := by
      have hp := mul_le_mul_of_nonneg_left hx (Real.pi_pos.le)
      field_simp at hp
      linarith
    have hz := mul_le_mul_of_nonneg_left hy (show 0 ≤ (1-r)/s by positivity)
    have heq : (1-r)/s*s = 1-r := by field_simp
    rw [heq] at hz
    nlinarith
  calc
    _ = Real.pi/2 + (Real.pi^2/4)*((1+r)/r)*((1-r)/Real.sin s) := by
      dsimp [X]
      field_simp
      ring
    _ ≤ Real.pi/2 + Real.pi^2*((1-r)/Real.sin s) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hratio (show 0 ≤ Real.pi^2/4 by positivity)]
    _ ≤ Real.pi/2 + Real.pi^2*((Real.pi/2)*((1-r)/s)) := by gcongr
    _ ≤ Real.pi/2 + Real.pi^3*(1-r)/s := by
      have hp : 0 ≤ Real.pi^3*(1-r)/s := by positivity
      have heq : Real.pi^2*((Real.pi/2)*((1-r)/s)) =
          (Real.pi^3*(1-r)/s)/2 := by ring
      rw [heq]
      linarith

theorem circleTop_arg {w : ℂ} (hr : 0 < w.re) (hi : 0 ≤ w.im) :
    ∃ s ∈ Ioc (0 : ℝ) (Real.pi/2), circleTop ‖w‖ s = w := by
  let s := Real.pi/2-w.arg
  have ha0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hi
  have ha1 : w.arg < Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  refine ⟨s, ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩, ?_⟩
  apply Complex.ext
  · rw [circleTop_re]
    dsimp [s]
    rw [Real.sin_pi_div_two_sub, Complex.norm_mul_cos_arg]
  · rw [circleTop_im]
    dsimp [s]
    rw [Real.cos_pi_div_two_sub, Complex.norm_mul_sin_arg]

lemma div_le_sqrt_of_gap {d δ s : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hs : 0 < s)
    (hg : δ ≤ s^2/d) : d/s ≤ Real.sqrt (d/δ) := by
  have hg' : δ*d ≤ s^2 := (le_div_iff₀ hd).mp hg
  have he : (d/s)^2 ≤ d/δ := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hg' hd.le]
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr he

theorem reciprocal_A_slice {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re)
    (hradius : 1/2 ≤ ‖w‖) :
    1 / A w ≤ Real.pi/2 + Real.pi^3 *
      Real.sqrt ((1-‖w‖)/(T ‖w‖ - |(F w).im|)) := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hdelta : 0 < T ‖w‖ - |(F w).im| := by
    have hh := vertical_gap_pos hFw (re_F_pos hw hr)
    simpa only [g_F hw] using hh
  have upper (z : ℂ) (hz : ‖z‖ < 1) (hzr : 0 < z.re) (hzi : 0 ≤ z.im)
      (hzlow : 1/2 ≤ ‖z‖) (hgap : 0 < T ‖z‖ - |(F z).im|) :
      1 / A z ≤ Real.pi/2 + Real.pi^3 *
        Real.sqrt ((1-‖z‖)/(T ‖z‖ - |(F z).im|)) := by
    obtain ⟨s, hs, he⟩ := circleTop_arg hzr hzi
    have hh := reciprocal_A_circleTop hzlow hz hs.1 hs.2
    rw [he] at hh
    apply hh.trans
    have hgs := gap_le_square (norm_nonneg z) hz hs.1.le hs.2
    rw [he] at hgs
    have hg : T ‖z‖ - |(F z).im| ≤ s^2/(1-‖z‖) := by
      linarith [le_abs_self (F z).im]
    have hb := div_le_sqrt_of_gap (sub_pos.mpr hz) hgap hs.1 hg
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.pi^3 by positivity)
    have heq : Real.pi^3*((1-‖z‖)/s) = Real.pi^3*(1-‖z‖)/s := by ring
    rw [heq] at hm
    linarith
  rcases le_total 0 w.im with hi | hi
  · exact upper w hw hr hi hradius hdelta
  · have hn : ‖(starRingEnd ℂ) w‖ = ‖w‖ := by simp
    have ha : A ((starRingEnd ℂ) w) = A w := by
      rw [A, re_mul_deriv_F (by simpa using hw), A, re_mul_deriv_F hw]
      simp
    have hh := upper ((starRingEnd ℂ) w) (by simpa using hw) (by simpa using hr)
      (by simpa using neg_nonneg.mpr hi) (by simpa using hradius) (by simpa using hdelta)
    simpa [ha] using hh

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem deriv_T_eq {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    deriv T r = (8 / Real.pi^2) * (Real.artanh r / r) := by
  have habs : |r| < 1 := by simpa only [abs_of_pos hr] using hr1
  rw [(hasDerivAt_T habs).deriv]
  have hh := congr_arg Complex.im (mul_deriv_F (w := (r : ℂ)*I) (by simpa [norm_mul] using habs))
  have hc : cayley ((r : ℂ)*I) = (((1-r)/(1+r) : ℝ) : ℂ) := by
    unfold cayley
    push_cast
    rw [mul_assoc, I_mul_I]
    ring
  have hai : (Complex.arctan ((r : ℂ)*I)).im = Real.artanh r := by
    rw [Complex.arctan]
    change ((-I/2) * Complex.log (cayley ((r : ℂ)*I))).im = _
    rw [hc, mul_im]
    have hp : 0 < (1-r)/(1+r) := by positivity
    have hre : (-I/2 : ℂ).re = 0 := by norm_num [div_re]
    have him : (-I/2 : ℂ).im = -1/2 := by norm_num [div_im]
    rw [hre, him, zero_mul, zero_add]
    rw [Complex.log_re, norm_real, Real.norm_eq_abs, abs_of_pos hp,
      Real.artanh_eq_half_log ⟨by linarith, hr1.le⟩]
    have hlog : Real.log ((1-r)/(1+r)) = -Real.log ((1+r)/(1-r)) := by
      rw [show (1-r)/(1+r) = ((1+r)/(1-r))⁻¹ by rw [inv_div], Real.log_inv]
    rw [hlog]
    norm_num
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    zero_mul, zero_sub, add_zero, neg_zero, zero_add] at hh
  rw [hai] at hh
  rw [mul_comm] at hh
  have hh := (eq_div_iff hr.ne').mpr hh
  calc
    _ = ((8 / Real.pi^2) * Real.artanh r)/r := hh
    _ = _ := by ring

theorem deriv_T_lower {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hr : r < 1) :
    (8/Real.pi^2) * Real.artanh a ≤ deriv T r := by
  have hr0 : 0 < r := ha.trans_le har
  rw [deriv_T_eq hr0 hr]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Real.artanh_le_artanh (by linarith) hr har).trans
  exact le_div_self (Real.artanh_nonneg hr0.le) hr0 hr.le

theorem T_tail_gap {a r s : ℝ} (ha : 0 < a) (har : a ≤ r) (hrs : r ≤ s)
    (hs : s < 1) :
    (8/Real.pi^2)*Real.artanh a * (s-r) ≤ T s-T r := by
  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc r s)
    (continuousOn_T.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2.trans hs.le⟩))
    (by intro x hx
        have hxabs : |x| < 1 := by
          simp only [interior_Icc, mem_Ioo] at hx
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        exact (hasDerivAt_T hxabs).differentiableAt.differentiableWithinAt)
    (by intro x hx
        simp only [interior_Icc, mem_Ioo] at hx
        exact deriv_T_lower ha (har.trans hx.1.le) (hx.2.trans hs))
    r ⟨le_rfl, hrs⟩ s ⟨hrs, le_rfl⟩ hrs

theorem exists_tail_cutoff (M : ℝ) : ∃ a ∈ Ioo (1/2 : ℝ) 1,
    M < (8/Real.pi^2)*Real.artanh a := by
  let y := max (Real.artanh (1/2)) ((Real.pi^2/8)*M) + 1
  let a := Real.tanh y
  have ha : a ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  have hy : Real.artanh a = y := Real.artanh_tanh y
  have hhalf : (1/2 : ℝ) < a := by
    apply (Real.artanh_lt_artanh_iff (by norm_num) ha).mp
    rw [hy]
    dsimp [y]
    have := le_max_left (Real.artanh (1/2)) ((Real.pi^2/8)*M)
    linarith
  refine ⟨a, ⟨hhalf, ha.2⟩, ?_⟩
  rw [hy]
  have hyy : (Real.pi^2/8)*M < y := by
    dsimp [y]
    have := le_max_right (Real.artanh (1/2)) ((Real.pi^2/8)*M)
    linarith
  have hm := mul_lt_mul_of_pos_left hyy (by positivity : 0 < 8/Real.pi^2)
  have he : (8/Real.pi^2)*((Real.pi^2/8)*M) = M := by field_simp
  rwa [he] at hm

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.HorizontalIntegrals


namespace OAI

universe u52 u53 u54

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace SmoothPaths
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

universe u
variable {E F : Type u} {H : Type u52} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def integralPath : C(SmoothODE.Time, F) →L[ℝ] F :=
  (ContinuousMap.evalCLM ℝ ⟨1, by norm_num⟩).comp SmoothODE.primitiveCLM

@[simp] theorem integralPath_apply (u : C(SmoothODE.Time, F)) :
    integralPath u = ∫ t in (0 : ℝ)..1, SmoothODE.extend u t := rfl

theorem contDiff_integralPath {f : E → F} (hf : ContDiff ℝ ∞ f)
    (L : H →L[ℝ] C(SmoothODE.Time, E)) :
    ContDiff ℝ ∞ (fun z => integralPath (superpose hf.continuous (L z))) :=
  (integralPath (F := F)).contDiff.comp ((contDiff_superpose hf).comp L.contDiff)

end
end SmoothPaths

namespace SmoothExtension
open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section

variable {E : Type u53} {F : Type u54} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_global_near_closed {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ f₁ : E → F, ContDiff ℝ ∞ f₁ ∧ f₁ =ᶠ[𝓝ˢ K] f := by
  obtain ⟨b, hb0, hb1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK
    (disjoint_left.mpr (by intro x hx hxK; exact hx (hKU hxK))) (n := ⊤)
  have hb : ContDiff ℝ ∞ b := contMDiff_iff_contDiff.mp b.contMDiff
  refine ⟨fun x => b x • f x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hh : ∀ᶠ y in 𝓝 x, b y = 0 := hb0.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hh] with y hy
      simp [hy]
  · filter_upwards [hb1] with x hx
    simp [hx]

end
end SmoothExtension

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def density (k : ℕ) (z : ℂ) : ℝ := ‖g z‖^(2*k-2) * ‖deriv g z‖^2

def J (k : ℕ) (v t : ℝ) : ℝ := (k : ℝ)^2 * ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I)

theorem density_nonneg (k : ℕ) (z : ℂ) : 0 ≤ density k z := by
  unfold density; positivity

theorem contDiffOn_density (k : ℕ) : ContDiffOn ℝ ∞ (density k) D := by
  have hg : ContDiffOn ℝ ∞ g D := (analyticOnNhd_g.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have hd : ContDiffOn ℝ ∞ (deriv g) D :=
    (analyticOnNhd_g.deriv.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have he : density k = fun z => (‖g z‖^2)^(k-1) * ‖deriv g z‖^2 := by
    funext z
    simp only [density, ← pow_mul]
    congr 2
    omega
  rw [he]
  exact ((hg.norm_sq ℂ).pow (k-1)).mul (hd.norm_sq ℂ)

theorem continuousOn_density (k : ℕ) : ContinuousOn (density k) D :=
  (contDiffOn_density k).continuousOn

theorem integrable_density {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume 0 v := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_density k).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem_signed hz hh

theorem hasDerivAt_J {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    HasDerivAt (fun v => J k v t) ((k : ℝ)^2*density k ((v : ℂ)+(t : ℂ)*I)) v := by
  have hc : ContinuousAt (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) v :=
    ((continuousOn_density k).continuousAt (isOpen_D.mem_nhds hz)).comp (f := fun h : ℝ => (h : ℂ)+(t : ℂ)*I)
      (show ContinuousAt (fun h : ℝ => (h : ℂ)+(t : ℂ)*I) v from by fun_prop)
  have hm : StronglyMeasurableAtFilter
      (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) (𝓝 v) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter
      (isOpen_D.preimage (show Continuous (fun h : ℝ => (h : ℂ)+(t : ℂ)*I) from by fun_prop))
      (fun h hh => ((continuousOn_density k).continuousAt (isOpen_D.mem_nhds hh)).comp (f := fun a : ℝ => (a : ℂ)+(t : ℂ)*I)
        (show ContinuousAt (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) h from by fun_prop))
      v hz
  exact (intervalIntegral.integral_hasDerivAt_right (integrable_density hz k) hm hc).const_mul _

@[simp] theorem J_zero (k : ℕ) (t : ℝ) : J k 0 t = 0 := by simp [J]

theorem J_nonneg {v t : ℝ} (hv : 0 ≤ v) (k : ℕ) : 0 ≤ J k v t := by
  apply mul_nonneg (sq_nonneg _)
  exact intervalIntegral.integral_nonneg hv (fun _ _ => density_nonneg _ _)

def horizontalPath : ℂ →L[ℝ] C(SmoothODE.Time, ℂ) := by
  let L : ℂ →ₗ[ℝ] C(SmoothODE.Time, ℂ) :=
    { toFun := fun z => ⟨fun a => ((a : ℝ)*z.re : ℝ) + (z.im : ℂ)*I, by fun_prop⟩
      map_add' := by intro z w; ext a; simp; ring
      map_smul' := by intro c z; ext a; simp; ring }
  apply L.mkContinuous 2
  intro z
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖(((a : ℝ)*z.re : ℝ) : ℂ)+(z.im : ℂ)*I‖ ≤ _
  calc
    _ ≤ ‖(((a : ℝ)*z.re : ℝ) : ℂ)‖ + ‖(z.im : ℂ)*I‖ := norm_add_le _ _
    _ = |(a : ℝ)| * |z.re| + |z.im| := by simp
    _ ≤ |z.re| + |z.im| := by
      rw [abs_of_nonneg a.2.1]
      nlinarith [a.2.2, abs_nonneg z.re]
    _ ≤ 2*‖z‖ := by linarith [abs_re_le_norm z, abs_im_le_norm z]

@[simp] theorem horizontalPath_apply (z : ℂ) (a : SmoothODE.Time) :
    horizontalPath z a = (((a : ℝ)*z.re : ℝ) : ℂ)+(z.im : ℂ)*I := rfl

theorem J_affine (k : ℕ) (v t : ℝ) :
    J k v t = (k : ℝ)^2*v*∫ a in (0 : ℝ)..1, density k (((a*v : ℝ) : ℂ)+(t : ℂ)*I) := by
  rw [J, mul_assoc]
  congr 1
  have hh := intervalIntegral.smul_integral_comp_mul_right
    (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) v (a := 0) (b := 1)
  simpa only [smul_eq_mul, zero_mul, one_mul] using hh.symm

theorem contDiffOn_J (k : ℕ) : ContDiffOn ℝ ∞ (fun z : ℂ => J k z.re z.im) D := by
  intro z hz
  let C := (fun a : ℝ => (((a*z.re : ℝ) : ℂ)+(z.im : ℂ)*I)) '' Icc (0 : ℝ) 1
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCD : C ⊆ D := by
    rintro _ ⟨a, ha, rfl⟩
    apply horizontal_segment_mem_signed (v := z.re) (t := z.im)
      (by simpa only [re_add_im] using hz)
    by_cases hv : 0 ≤ z.re
    · rw [uIcc_of_le hv]
      constructor <;> nlinarith [ha.1, ha.2]
    · rw [uIcc_of_ge (le_of_not_ge hv)]
      constructor <;> nlinarith [ha.1, ha.2]
  obtain ⟨f, hf, he⟩ := SmoothExtension.exists_global_near_closed isOpen_D hCc.isClosed hCD
    (contDiffOn_density k)
  have hglob : ContDiff ℝ ∞ (fun w : ℂ =>
      (k : ℝ)^2*w.re*SmoothPaths.integralPath (SmoothPaths.superpose hf.continuous (horizontalPath w))) :=
    (contDiff_const.mul Complex.reCLM.contDiff).mul
      (SmoothPaths.contDiff_integralPath hf horizontalPath)
  have heq : ∀ᶠ w in 𝓝 z, ∀ a ∈ Icc (0 : ℝ) 1,
      f ((((a*w.re : ℝ) : ℂ)+(w.im : ℂ)*I)) = density k ((((a*w.re : ℝ) : ℂ)+(w.im : ℂ)*I)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro a ha
    have hs : ∀ᶠ y in 𝓝 ((((a*z.re : ℝ) : ℂ)+(z.im : ℂ)*I)), f y = density k y :=
      he.filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ ha))
    exact (show ContinuousAt (fun p : ℂ×ℝ => (((p.2*p.1.re : ℝ) : ℂ)+(p.1.im : ℂ)*I)) (z,a)
      from by fun_prop) hs
  apply ContDiffAt.contDiffWithinAt
  apply hglob.contDiffAt.congr_of_eventuallyEq
  filter_upwards [heq] with w hw
  rw [J_affine, SmoothPaths.integralPath_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
  have hp : projIcc (0 : ℝ) 1 zero_le_one a = ⟨a, ha⟩ := by exact projIcc_of_mem zero_le_one ha
  simp only [SmoothODE.extend, hp, SmoothPaths.superpose_apply, horizontalPath_apply]
  exact (hw a ha).symm

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def rho (t h : ℝ) : ℝ := ‖g ((h : ℂ)+(t : ℂ)*I)‖
def rhoD (t h : ℝ) : ℝ := A (g ((h : ℂ)+(t : ℂ)*I)) /
  (rho t h * ‖deriv F (g ((h : ℂ)+(t : ℂ)*I))‖^2)

theorem rho_pos {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) : 0 < rho t h := by
  apply norm_pos_iff.mpr
  intro he
  have hre := re_g_pos hz (by simpa using hh)
  rw [he] at hre
  simp at hre

theorem hasDerivAt_rho {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) :
    HasDerivAt (rho t) (rhoD t h) h := by
  have hn := rho_pos hz hh
  have hd := (horizontal_normSq_deriv hz).sqrt (ne_of_gt (sq_pos_of_pos hn))
  have he : (fun x : ℝ => Real.sqrt (‖g ((x : ℂ)+(t : ℂ)*I)‖^2)) = rho t := by
    funext x; exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hd
  convert hd using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  dsimp [rhoD, rho]
  ring

theorem rhoD_pos {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) : 0 < rhoD t h := by
  apply div_pos (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hh)))
  exact mul_pos (rho_pos hz hh) (sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz))))

theorem continuousOn_rho {t v : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (hv : 0 ≤ v) :
    ContinuousOn (rho t) (Icc 0 v) := by
  apply (continuousOn_g.norm).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem hz hv hh

theorem density_radial {k : ℕ} (hk : 1 ≤ k) {t h : ℝ}
    (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) :
    density k ((h : ℂ)+(t : ℂ)*I) =
      (rho t h)^(2*k-1) * (1/A (g ((h : ℂ)+(t : ℂ)*I))) * rhoD t h := by
  have hA := ne_of_gt (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hh)))
  have hr := ne_of_gt (rho_pos hz hh)
  have hF := norm_ne_zero_iff.mpr (deriv_F_ne_zero (norm_g_lt hz))
  have he : deriv g ((h : ℂ)+(t : ℂ)*I) = (deriv F (g ((h : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [density, he, norm_inv]
  rw [show 2*k-1 = (2*k-2)+1 by omega, pow_succ]
  dsimp [rhoD, rho] at *
  field_simp
  rw [pow_succ]

theorem deriv_F_neg {w : ℂ} (hw : ‖w‖ < 1) : deriv F (-w) = deriv F w := by
  rw [(hasDerivAt_F (by simpa using hw)).deriv, (hasDerivAt_F hw).deriv]
  congr 1
  apply tsum_congr
  intro n
  simp only [termDeriv]
  rw [(show Even (2*n) from ⟨n, by omega⟩).neg_pow]

theorem deriv_F_conj {w : ℂ} (hw : ‖w‖ < 1) :
    deriv F ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv F w) := by
  have he : (fun n : ℕ => termDeriv n ((starRingEnd ℂ) w)) =
      fun n : ℕ => conjCLE (termDeriv n w) := by
    funext n
    simp [termDeriv, map_ofNat]
  rw [(hasDerivAt_F (by simpa using hw)).deriv, (hasDerivAt_F hw).deriv]
  simp only [he, ← conjCLE.map_tsum]
  simp [map_ofNat]

theorem density_neg_conj {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    density k (-(starRingEnd ℂ) z) = density k z := by
  have hd (w : ℂ) (hw : w ∈ D) : deriv g w = (deriv F (g w))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hw), F_g hw]
  rw [density, density, hd _ (neg_conj_mem_D hz), hd _ hz, g_neg_conj hz,
    deriv_F_neg (by simpa using norm_g_lt hz), deriv_F_conj (norm_g_lt hz)]
  simp

theorem J_neg {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    J k (-v) t = -J k v t := by
  have he (h : ℝ) : -(starRingEnd ℂ) ((h : ℂ)+(t : ℂ)*I) = ((-h : ℝ) : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  have hsub := intervalIntegral.integral_comp_neg
    (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) (a := 0) (b := v)
  simp only [neg_zero] at hsub
  have hi : (∫ h in (0 : ℝ)..v, density k (((-h : ℝ) : ℂ)+(t : ℂ)*I)) =
      ∫ h in (0 : ℝ)..v, density k ((h : ℂ)+(t : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro h hh
    dsimp only
    rw [← he, density_neg_conj (horizontal_segment_mem_signed hz hh)]
  rw [hi, intervalIntegral.integral_symm (a := 0) (b := -v)] at hsub
  rw [J, J, ← mul_neg]
  congr 1
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.TipEstimates


namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

open MeasureTheory intervalIntegral Set
open scoped Real

namespace SymmetricPolar
noncomputable section

def endpointKernel (H y : ℝ) : ℝ := Real.sqrt (y / (H - y))

lemma endpointKernel_eq_rpow {H y : ℝ} (hy : 0 ≤ y) (hyH : y ≤ H) :
    endpointKernel H y = y ^ (1 / 2 : ℝ) * (H - y) ^ (-(1 / 2 : ℝ)) := by
  rw [endpointKernel, Real.sqrt_div hy, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.rpow_neg (sub_nonneg.mpr hyH), div_eq_mul_inv]

lemma intervalIntegrable_endpointKernel {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable (endpointKernel H) volume 0 H := by
  have hi : IntervalIntegrable (fun y : ℝ => (H - y) ^ (-(1 / 2 : ℝ))) volume 0 H := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := H)
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left H).symm
  have hm := hi.continuousOn_mul Real.continuous_sqrt.continuousOn
  apply IntervalIntegrable.congr (f := fun y => Real.sqrt y * (H - y) ^ (-(1 / 2 : ℝ))) _ hm
  intro y hy
  rw [uIoc_of_le hH] at hy
  dsimp only
  rw [endpointKernel_eq_rpow hy.1.le hy.2, Real.sqrt_eq_rpow]

private lemma beta_three_halves_one_half :
    Complex.betaIntegral (3 / 2) (1 / 2) = (Real.pi : ℂ) / 2 := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
  have hG : Complex.Gamma (2 : ℂ) = 1 := by
    norm_num [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one]
  have hreflect := Complex.Gamma_mul_Gamma_one_sub (1 / 2)
  norm_num at hreflect
  rw [show (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 by ring,
    Complex.sin_pi_div_two, div_one] at hreflect
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, hG, div_one,
    show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
    Complex.Gamma_add_one _ (by norm_num)]
  rw [mul_assoc, hreflect]
  ring

lemma integral_endpointKernel {H : ℝ} (hH : 0 < H) :
    (∫ y in 0..H, endpointKernel H y) = Real.pi * H / 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h := Complex.betaIntegral_scaled (3 / 2) (1 / 2) hH
  norm_num only at h
  rw [beta_three_halves_one_half] at h
  have hc : (∫ y in 0..H, (endpointKernel H y : ℂ)) =
      ∫ y in 0..H, (y : ℂ) ^ ((3 / 2 : ℂ) - 1) *
        ((H : ℂ) - y) ^ ((1 / 2 : ℂ) - 1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hH.le] at hy
    dsimp only
    rw [endpointKernel_eq_rpow hy.1 hy.2, Complex.ofReal_mul,
      Complex.ofReal_cpow hy.1, Complex.ofReal_cpow (sub_nonneg.mpr hy.2),
      Complex.ofReal_sub]
    norm_num
  rw [hc]
  norm_num only
  rw [h]
  norm_num
  ring

lemma endpointKernel_le_one {H y : ℝ} (hH : 0 < H) (_hy : 0 ≤ y)
    (hyH : y ≤ H / 2) : endpointKernel H y ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact (div_le_one (by linarith : 0 < H - y)).mpr (by linarith)

lemma intervalIntegrable_dampedEndpointKernel {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable (fun y => Real.exp (-y) * endpointKernel H y) volume 0 H :=
  (intervalIntegrable_endpointKernel hH).continuousOn_mul (by fun_prop)

lemma integral_dampedEndpointKernel_le {H : ℝ} (hH : 0 < H) :
    (∫ y in 0..H, Real.exp (-y) * endpointKernel H y) ≤
      1 + Real.pi / Real.exp 1 := by
  have hhalf : 0 ≤ H / 2 := by positivity
  have hhalfH : H / 2 ≤ H := by linarith
  have hsfirst : uIcc 0 (H / 2) ⊆ uIcc 0 H := by
    simpa only [uIcc_of_le hhalf, uIcc_of_le hH.le] using
      Icc_subset_Icc le_rfl hhalfH
  have hslast : uIcc (H / 2) H ⊆ uIcc 0 H := by
    simpa only [uIcc_of_le hhalfH, uIcc_of_le hH.le] using
      Icc_subset_Icc hhalf le_rfl
  have hk := intervalIntegrable_endpointKernel hH.le
  have hf := intervalIntegrable_dampedEndpointKernel hH.le
  have hfirst : (∫ y in 0..H / 2, Real.exp (-y) * endpointKernel H y) ≤ 1 := by
    calc
      _ ≤ ∫ y in 0..H / 2, Real.exp (-y) := by
        apply intervalIntegral.integral_mono_on hhalf (hf.mono_set hsfirst)
          ((by fun_prop : Continuous (fun y : ℝ => Real.exp (-y))).intervalIntegrable _ _)
        intro y hy
        exact mul_le_of_le_one_right (Real.exp_pos _).le
          (endpointKernel_le_one hH hy.1 hy.2)
      _ ≤ 1 := by
        rw [intervalIntegral.integral_comp_neg, integral_exp]
        simp only [neg_zero, Real.exp_zero]
        linarith [Real.exp_pos (-(H / 2))]
  have hlast : (∫ y in H / 2..H, Real.exp (-y) * endpointKernel H y) ≤
      Real.exp (-(H / 2)) * (Real.pi * H / 2) := by
    calc
      _ ≤ ∫ y in H / 2..H, Real.exp (-(H / 2)) * endpointKernel H y := by
        apply intervalIntegral.integral_mono_on hhalfH (hf.mono_set hslast)
          ((hk.mono_set hslast).const_mul _)
        intro y hy
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hy.1))
          (Real.sqrt_nonneg _)
      _ = Real.exp (-(H / 2)) * ∫ y in H / 2..H, endpointKernel H y :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ Real.exp (-(H / 2)) * ∫ y in 0..H, endpointKernel H y := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply intervalIntegral.integral_mono_interval hhalf hhalfH le_rfl _ hk
        exact Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _)
      _ = _ := by rw [integral_endpointKernel hH]
  have hexp : (H / 2) * Real.exp (-(H / 2)) ≤ 1 / Real.exp 1 := by
    calc
      _ ≤ Real.exp (H / 2 - 1) * Real.exp (-(H / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (H / 2 - 1)]
      _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
      _ = _ := by rw [Real.exp_neg, one_div]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.mono_set hsfirst) (hf.mono_set hslast)]
  have hp := mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
  have hp' : Real.exp (-(H / 2)) * (Real.pi * H / 2) ≤ Real.pi / Real.exp 1 := by
    calc
      _ = Real.pi * (H / 2 * Real.exp (-(H / 2))) := by ring
      _ ≤ Real.pi * (1 / Real.exp 1) := hp
      _ = _ := by ring
  exact add_le_add hfirst (hlast.trans hp')

def movingEndpointIntegral (k : ℕ) (a : ℝ) : ℝ :=
  (k : ℝ) * ∫ r in a..1,
    r ^ (2 * k - 1) * Real.sqrt ((1 - r) / (r - a))

lemma movingEndpointIntegral_eq {k : ℕ} (hk : 0 < k) (a : ℝ) :
    movingEndpointIntegral k a = ∫ y in 0..(k : ℝ) * (1 - a),
      (1 - y / k) ^ (2 * k - 1) * endpointKernel ((k : ℝ) * (1 - a)) y := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  let f : ℝ → ℝ := fun y =>
    (1 - y / k) ^ (2 * k - 1) * endpointKernel ((k : ℝ) * (1 - a)) y
  have hsub (r : ℝ) : f ((k : ℝ) - k * r) =
      r ^ (2 * k - 1) * Real.sqrt ((1 - r) / (r - a)) := by
    dsimp [f, endpointKernel]
    have hbase : 1 - ((k : ℝ) - k * r) / k = r := by field_simp; ring
    rw [hbase]
    congr 2
    rw [show (k : ℝ) - k * r = k * (1 - r) by ring,
      show (k : ℝ) * (1 - a) - k * (1 - r) = k * (r - a) by ring,
      mul_div_mul_left _ _ hk0]
  calc
    _ = (k : ℝ) • ∫ r in a..1, f ((k : ℝ) - k * r) := by
      simp only [movingEndpointIntegral, smul_eq_mul, hsub]
    _ = ∫ y in (k : ℝ) - k * 1..(k : ℝ) - k * a, f y :=
      intervalIntegral.smul_integral_comp_sub_mul f _ _
    _ = _ := by
      rw [show (k : ℝ) - k * 1 = 0 by ring,
        show (k : ℝ) - k * a = k * (1 - a) by ring]

lemma movingEndpointIntegral_le {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) :
    movingEndpointIntegral k a ≤ 1 + Real.pi / Real.exp 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hH : 0 < (k : ℝ) * (1 - a) := mul_pos hkR (sub_pos.mpr ha1)
  rw [movingEndpointIntegral_eq (by omega : 0 < k) a]
  apply le_trans _ (integral_dampedEndpointKernel_le hH)
  apply intervalIntegral.integral_mono_on hH.le
    ((intervalIntegrable_endpointKernel hH.le).continuousOn_mul (by fun_prop))
    (intervalIntegrable_dampedEndpointKernel hH.le)
  intro y hy
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hyk : y ≤ (k : ℝ) := by nlinarith [mul_nonneg hkR.le ha, hy.2]
  have hb0 : 0 ≤ 1 - y / (k : ℝ) := sub_nonneg.mpr ((div_le_one hkR).mpr hyk)
  have hb1 : 1 - y / (k : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hy.1 hkR.le)
  exact (pow_le_pow_of_le_one hb0 hb1 (by omega : k ≤ 2 * k - 1)).trans
    (Real.one_sub_div_pow_le_exp_neg hyk)

lemma movingEndpointIntegral_le_linear {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) :
    movingEndpointIntegral k a ≤ Real.pi * ((k : ℝ) * (1 - a)) / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hH : 0 < (k : ℝ) * (1 - a) := mul_pos hkR (sub_pos.mpr ha1)
  rw [movingEndpointIntegral_eq (by omega : 0 < k) a,
    ← integral_endpointKernel hH]
  apply intervalIntegral.integral_mono_on hH.le
    ((intervalIntegrable_endpointKernel hH.le).continuousOn_mul (by fun_prop))
    (intervalIntegrable_endpointKernel hH.le)
  intro y hy
  apply mul_le_of_le_one_left (Real.sqrt_nonneg _)
  have hyk : y ≤ (k : ℝ) := by nlinarith [mul_nonneg hkR.le ha, hy.2]
  have hb0 : 0 ≤ 1 - y / (k : ℝ) := sub_nonneg.mpr ((div_le_one hkR).mpr hyk)
  have hb1 : 1 - y / (k : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hy.1 hkR.le)
  exact pow_le_one₀ hb0 hb1

end
end SymmetricPolar

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def tailSlope (a : ℝ) : ℝ := 8/Real.pi^2 * Real.artanh a

theorem tailSlope_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 0 < tailSlope a := by
  apply mul_pos (by positivity)
  exact Real.artanh_pos ⟨ha, ha1⟩

theorem T_rho_ge_abs {t v u : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 ≤ v) (hu : u ∈ Icc 0 v) : |t| ≤ T (rho t u) := by
  have hmono := (horizontal_radius_strictMono hz hv).monotoneOn
  have h0 := horizontal_segment_mem hz hv (left_mem_Icc.mpr hv)
  have hU := horizontal_segment_mem hz hv hu
  have hle := hmono (left_mem_Icc.mpr hv) hu hu.1
  have hT := strictMonoOn_T.monotoneOn
    (show rho t 0 ∈ Icc (-1) 1 from ⟨(le_trans (by norm_num) (norm_nonneg _)), (norm_g_lt h0).le⟩)
    (show rho t u ∈ Icc (-1) 1 from ⟨le_trans (by norm_num) (norm_nonneg _), (norm_g_lt hU).le⟩) hle
  have he : T (rho t 0) = |t| := by simpa [rho] using T_norm_g_axis (axis_mem_D hz)
  rwa [he] at hT

theorem reciprocal_A_tail {w : ℂ} (hw : ‖w‖ < 1) (hwr : 0 < w.re)
    {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (hbw : b < ‖w‖)
    (ht : |(F w).im| ≤ T b) :
    1/A w ≤ Real.pi/2 + Real.pi^3 / Real.sqrt (tailSlope a) *
      Real.sqrt ((1-‖w‖)/(‖w‖-b)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := hab.trans_lt (hbw.trans hw)
  have hL := tailSlope_pos ha0 ha1
  have hgap := T_tail_gap ha0 hab hbw.le hw
  have hnum : 0 ≤ 1-‖w‖ := by linarith
  have hden : 0 < tailSlope a * (‖w‖-b) := mul_pos hL (sub_pos.mpr hbw)
  have hgap' : tailSlope a * (‖w‖-b) ≤ T ‖w‖ - |(F w).im| := by
    dsimp [tailSlope] at *
    linarith
  apply (reciprocal_A_slice hw hwr (ha.trans (hab.trans hbw.le))).trans
  apply add_le_add_right
  calc
    Real.pi^3 * Real.sqrt ((1-‖w‖)/(T ‖w‖ - |(F w).im|))
        ≤ Real.pi^3 * Real.sqrt ((1-‖w‖)/(tailSlope a*(‖w‖-b))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left hnum hden hgap'
    _ = Real.pi^3 / Real.sqrt (tailSlope a) * Real.sqrt ((1-‖w‖)/(‖w‖-b)) := by
      rw [show (1-‖w‖)/(tailSlope a*(‖w‖-b)) = ((1-‖w‖)/(‖w‖-b))/(tailSlope a) by rw [div_div, mul_comm (‖w‖-b)],
        Real.sqrt_div (div_nonneg hnum (sub_nonneg.mpr hbw.le))]
      ring

theorem integrable_radialError {b : ℝ} (hb : b ≤ 1) (k : ℕ) :
    IntervalIntegrable (fun r : ℝ => r^(2*k-1)*Real.sqrt ((1-r)/(r-b))) volume b 1 := by
  have h := (SymmetricPolar.intervalIntegrable_endpointKernel (sub_nonneg.mpr hb)).comp_sub_left 1
  have he : (fun r : ℝ => SymmetricPolar.endpointKernel (1-b) (1-r)) =
      fun r : ℝ => Real.sqrt ((1-r)/(r-b)) := by
    funext r
    dsimp [SymmetricPolar.endpointKernel]
    congr 2
    ring
  rw [he] at h
  have hh : IntervalIntegrable (fun r : ℝ => Real.sqrt ((1-r)/(r-b))) volume b 1 := by
    convert h.symm using 1 <;> ring
  exact hh.continuousOn_mul (by fun_prop)

theorem integral_radialLeading {k : ℕ} (hk : 1 ≤ k) (b R : ℝ) :
    (k : ℝ) * ∫ r in b..R, r^(2*k-1)*(Real.pi/2) =
      Real.pi/4 * (R^(2*k)-b^(2*k)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => r^(2*k)/(2*k)) (r^(2*k-1)) r := by
    convert ((hasDerivAt_id r).pow (2*k)).div_const ((2:ℝ)*k) using 1 <;>
      first | rfl | (simp only [Nat.cast_mul, Nat.cast_ofNat, id_eq, mul_one]; field_simp [hk0])
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r ∈ uIcc b R) => hd r)
    (show IntervalIntegrable (fun r : ℝ => r^(2*k-1)) volume b R from (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, hi]
  field_simp
  ring

theorem outer_integral_bound {k : ℕ} (hk : 1 ≤ k) {t v u a : ℝ}
    (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 1/2 ≤ a) (hau : a ≤ rho t u) :
    (k : ℝ)*∫ h in u..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
      Real.pi/4*((rho t v)^(2*k)-(rho t u)^(2*k)) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  have hv : 0 ≤ v := hu.trans huv
  have huI : u ∈ Icc 0 v := ⟨hu, huv⟩
  have huD := horizontal_segment_mem hz hv huI
  have hb0 : 0 ≤ rho t u := norm_nonneg _
  have hb1 : rho t u < 1 := norm_g_lt huD
  have hR1 : rho t v < 1 := norm_g_lt hz
  have hrho := horizontal_radius_strictMono hz hv
  have hbR : rho t u ≤ rho t v := hrho.monotoneOn huI (right_mem_Icc.mpr hv) huv
  have ha1 : a < 1 := hau.trans_lt hb1
  have hL : 0 < tailSlope a := tailSlope_pos (by linarith) ha1
  have hc : 0 ≤ Real.pi^3/Real.sqrt (tailSlope a) := by positivity
  let P : ℝ → ℝ := fun r => r^(2*k-1)*(Real.pi/2) +
    (Real.pi^3/Real.sqrt (tailSlope a))*(r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u)))
  have hradE := integrable_radialError hb1.le k
  have hradE' : IntervalIntegrable
      (fun r : ℝ => r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))) volume (rho t u) (rho t v) :=
    hradE.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by
      rw [uIcc_of_le hb1.le]; exact ⟨hbR, hR1.le⟩))
  have hP : IntervalIntegrable P volume (rho t u) (rho t v) :=
    ((by fun_prop : Continuous (fun r : ℝ => r^(2*k-1)*(Real.pi/2))).intervalIntegrable _ _).add
      (hradE'.const_mul _)
  have hcont : ContinuousOn (rho t) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact (continuousOn_rho hz hv).mono (fun _ hx => ⟨hu.trans hx.1, hx.2⟩)
  have hder : ∀ h ∈ Ioo (min u v) (max u v), HasDerivAt (rho t) (rhoD t h) h := by
    rw [min_eq_left huv, max_eq_right huv]
    intro h hh
    exact hasDerivAt_rho (horizontal_segment_mem hz hv ⟨hu.trans hh.1.le, hh.2.le⟩)
      (hu.trans_lt hh.1)
  have hpos : ∀ h ∈ Ioo (min u v) (max u v), 0 ≤ rhoD t h := by
    rw [min_eq_left huv, max_eq_right huv]
    intro h hh
    exact (rhoD_pos (horizontal_segment_mem hz hv ⟨hu.trans hh.1.le, hh.2.le⟩)
      (hu.trans_lt hh.1)).le
  have hPc : IntervalIntegrable (fun h => P (rho t h)*rhoD t h) volume u v :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hcont hder hpos).mpr hP
  have hdens : IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_density k).comp (by fun_prop)
    intro h hh
    rw [uIcc_of_le huv] at hh
    exact horizontal_segment_mem hz hv ⟨hu.trans hh.1, hh.2⟩
  have hcmp : ∫ h in u..v, density k ((h : ℂ)+(t : ℂ)*I) ≤ ∫ r in rho t u..rho t v, P r := by
    rw [← intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hcont hder hpos (g := P)]
    apply intervalIntegral.integral_mono_ae_restrict huv hdens hPc
    change ∀ᵐ (h : ℝ) ∂volume.restrict (Icc u v), density k ((h : ℂ)+(t : ℂ)*I) ≤ P (rho t h)*rhoD t h
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [volume.ae_ne u] with h hne hh
    have hhu : u < h := lt_of_le_of_ne hh.1 (Ne.symm hne)
    have hh0 : 0 < h := hu.trans_lt hhu
    have hhz := horizontal_segment_mem hz hv ⟨hh0.le, hh.2⟩
    have hbr : rho t u < rho t h := hrho huI ⟨hh0.le, hh.2⟩ hhu
    have hA := reciprocal_A_tail (norm_g_lt hhz) (re_g_pos hhz (by simpa using hh0))
      ha hau hbr (by simpa only [F_g hhz, add_im, ofReal_im, mul_im, ofReal_re, I_im,
        I_re, mul_one, mul_zero, add_zero, zero_add] using T_rho_ge_abs hz hv huI)
    rw [density_radial hk hhz hh0]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA (pow_nonneg (norm_nonneg (g ((h : ℂ)+(t : ℂ)*I))) (2*k-1))) (rhoD_pos hhz hh0).le
    convert hmul using 1 <;>
      first | rfl | (dsimp only [P, rho]; ring)
  have hlead := integral_radialLeading hk (rho t u) (rho t v)
  have herr : (k : ℝ)*∫ r in rho t u..rho t v,
      r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u)) ≤ 1+Real.pi/Real.exp 1 := by
    apply le_trans _ (SymmetricPolar.movingEndpointIntegral_le hk hb0 hb1)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    apply intervalIntegral.integral_mono_interval le_rfl hbR hR1.le _ hradE
    change ∀ᵐ (r : ℝ) ∂volume.restrict (Ioc (rho t u) 1), 0 ≤ r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun r hr => mul_nonneg
      (pow_nonneg (hb0.trans hr.1.le) _) (Real.sqrt_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg k)
  dsimp [P] at hh
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun r : ℝ => r^(2*k-1)*(Real.pi/2))).intervalIntegrable _ _)
    (hradE'.const_mul _), intervalIntegral.integral_const_mul, mul_add, hlead] at hh
  apply hh.trans
  apply add_le_add_right
  calc
    _ = (Real.pi^3/Real.sqrt (tailSlope a))*((k : ℝ)*∫ r in rho t u..rho t v,
        r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left herr hc

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.LensBounds


namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem exists_inner_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (t v : ℝ),
      (v : ℂ)+(t : ℂ)*I ∈ D → 0 ≤ v → rho t v ≤ a →
      (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
        C*(k : ℝ)*a^(2*k-2) := by
  let Cset := F '' Metric.closedBall (0 : ℂ) a
  have hCD : Cset ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ a := by simpa using hw
    simpa using hw'.trans_lt ha1
  have hCc : IsCompact Cset := (isCompact_closedBall (0 : ℂ) a).image_of_continuousOn
    (continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall ha1.le))
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (analyticOnNhd_g.deriv.continuousOn.mono hCD)
  obtain ⟨B, hB0, hB⟩ := isBounded_D.exists_pos_norm_le
  let M := max N 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨B*M^2, mul_nonneg hB0.le (sq_nonneg _), ?_⟩
  intro k t v hz hv hra
  have hvB : v ≤ B := by
    have hh := (abs_re_le_norm ((v : ℂ)+(t : ℂ)*I)).trans (hB _ hz)
    simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_self, add_zero, abs_of_nonneg hv] using hh
  have hpi : IntervalIntegrable (fun h : ℝ => a^(2*k-2)*M^2) volume 0 v := intervalIntegrable_const
  have hii := integrable_density hz k
  have hcmp : ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤ v*(a^(2*k-2)*M^2) := by
    have hh : ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
        ∫ h in 0..v, a^(2*k-2)*M^2 := by
      apply intervalIntegral.integral_mono_on hv hii hpi
      intro h hh
      have hhz := horizontal_segment_mem hz hv hh
      have hr : rho t h ≤ a := ((horizontal_radius_strictMono hz hv).monotoneOn hh
        (right_mem_Icc.mpr hv) hh.2).trans hra
      have hc : (h : ℂ)+(t : ℂ)*I ∈ Cset :=
        ⟨g _, by simpa [rho] using hr, F_g hhz⟩
      have hn : ‖deriv g ((h : ℂ)+(t : ℂ)*I)‖ ≤ M := (hN _ hc).trans (le_max_left _ _)
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hr _) (pow_le_pow_left₀ (norm_nonneg _) hn _)
        (sq_nonneg _) (pow_nonneg ha0 _)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  calc
    _ ≤ (k : ℝ)*(v*(a^(2*k-2)*M^2)) := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg k)
    _ ≤ (k : ℝ)*(B*(a^(2*k-2)*M^2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hvB (mul_nonneg (pow_nonneg ha0 _) (sq_nonneg _))) (Nat.cast_nonneg k)
    _ = _ := by ring

theorem exists_uniform_error_bound {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (t v : ℝ),
      (v : ℂ)+(t : ℂ)*I ∈ D → 0 ≤ v →
      (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
      Real.pi/4*(rho t v)^(2*k) + C*(k : ℝ)*a^(2*k-2) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨C, hC, hinner⟩ := exists_inner_bound ha0 ha1
  refine ⟨C, hC, ?_⟩
  intro k hk t v hz hv
  have hE : 0 ≤ Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by positivity
  have hCterm : 0 ≤ C*(k : ℝ)*a^(2*k-2) := by positivity
  have hR : 0 ≤ Real.pi/4*(rho t v)^(2*k) := by
    exact mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
  by_cases hr : rho t v ≤ a
  · exact (hinner k t v hz hv hr).trans (by linarith)
  by_cases hl : a ≤ rho t 0
  · have hh := outer_integral_bound hk hz (le_refl 0) hv ha hl
    have hn : 0 ≤ Real.pi/4*(rho t 0)^(2*k) :=
      mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
    nlinarith
  have haI : a ∈ Icc (rho t 0) (rho t v) := ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩
  obtain ⟨u, hu, heu⟩ := intermediate_value_Icc hv (continuousOn_rho hz hv) haI
  have huD := horizontal_segment_mem hz hv hu
  have hleft := hinner k t u huD hu.1 heu.le
  have hright := outer_integral_bound hk hz hu.1 hu.2 ha heu.ge
  have hIuv : IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume u v := by
    exact (integrable_density hz k).mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le hv]) right_mem_uIcc)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (integrable_density huD k) hIuv
  have hn : 0 ≤ Real.pi/4*(rho t u)^(2*k) :=
    mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)
  rw [← hadd]
  nlinarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem J_div_order {k : ℕ} (hk : 1 ≤ k) {v t : ℝ} (hv : 0 ≤ v) :
    |J k v t|/(k : ℝ) = (k : ℝ)*∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [abs_of_nonneg (J_nonneg hv k), J]
  field_simp

theorem rho_neg {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) : rho t (-v) = rho t v := by
  have he : -(starRingEnd ℂ) ((v : ℂ)+(t : ℂ)*I) = ((-v : ℝ) : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  rw [rho, rho, ← he, g_neg_conj hz]
  simp

def excess (k : ℕ) (z : ℂ) : ℝ := |J k z.re z.im|/(k : ℝ) - Real.pi/4*‖g z‖^(2*k)

def epsilon (k : ℕ) : ℝ := max 0 (sSup (excess k '' D))

theorem epsilon_nonneg (k : ℕ) : 0 ≤ epsilon k := le_max_left _ _

theorem exists_excess_bound {a : ℝ} (ha : 1/2 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ D,
      excess k z ≤ C*(k : ℝ)*a^(2*k-2) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_error_bound ha ha1
  refine ⟨C, hC, ?_⟩
  intro k hk z hz
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa only [re_add_im] using hz
  have hpos (v t : ℝ) (hv : 0 ≤ v) (hh : (v : ℂ)+(t : ℂ)*I ∈ D) :
      |J k v t|/(k : ℝ) - Real.pi/4*(rho t v)^(2*k) ≤
        C*(k : ℝ)*a^(2*k-2) + Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
    rw [J_div_order hk hv]
    linarith [hb k hk t v hh hv]
  by_cases hv : 0 ≤ z.re
  · simpa only [excess, rho, re_add_im] using hpos z.re z.im hv hz'
  · have hnz : ((-z.re : ℝ) : ℂ)+(z.im : ℂ)*I ∈ D := by
      convert neg_conj_mem_D hz using 1
      apply Complex.ext <;> simp
    have hh := hpos (-z.re) z.im (by linarith) hnz
    rw [J_neg hz', abs_neg, rho_neg hz'] at hh
    simpa only [excess, rho, re_add_im] using hh

theorem bddAbove_excess {k : ℕ} (hk : 1 ≤ k) : BddAbove (excess k '' D) := by
  obtain ⟨C, _, hC⟩ := exists_excess_bound (a := 3/4) (by norm_num) (by norm_num)
  refine ⟨C*(k : ℝ)*(3/4)^(2*k-2) + Real.pi^3/Real.sqrt (tailSlope (3/4))*(1+Real.pi/Real.exp 1), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hC k hk z hz

theorem excess_le_epsilon {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ D) : excess k z ≤ epsilon k :=
  (le_csSup (bddAbove_excess hk) (mem_image_of_mem _ hz)).trans (le_max_right _ _)

theorem epsilon_le_of_excess_le {k : ℕ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ z ∈ D, excess k z ≤ B) :
    epsilon k ≤ B := by
  apply max_le hB
  apply csSup_le ⟨excess k 0, mem_image_of_mem _ zero_mem_D⟩
  rintro _ ⟨z, hz, rfl⟩
  exact h z hz

theorem tendsto_inner_error {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (C : ℝ) :
    Tendsto (fun k : ℕ => C*(k : ℝ)*a^(2*k-2)) atTop (𝓝 0) := by
  have hq : |a^2| < 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq).const_mul (C/a^2)
  simp only [pow_one, mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hp : a^(2*k-2)*a^2 = (a^2)^k := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ 2*k), pow_mul]
  have ha2 : a^2 ≠ 0 := pow_ne_zero _ ha.ne'
  apply mul_right_cancel₀ ha2
  calc
    ((C/a^2)*((k : ℝ)*(a^2)^k))*a^2 = C*(k : ℝ)*(a^2)^k := by field_simp
    _ = C*(k : ℝ)*(a^(2*k-2)*a^2) := by rw [hp]
    _ = C*(k : ℝ)*a^(2*k-2)*a^2 := by ring

theorem exists_small_tail (e : ℝ) (he : 0 < e) :
    ∃ a ∈ Ioo (1/2 : ℝ) 1,
      Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) < e := by
  let H := Real.pi^3*(1+Real.pi/Real.exp 1)
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨a, ha, hL⟩ := exists_tail_cutoff ((H/e)^2)
  have ha0 : 0 < a := by linarith [ha.1]
  have hs : 0 < Real.sqrt (tailSlope a) := Real.sqrt_pos.2 (tailSlope_pos ha0 ha.2)
  have hq : H/e < Real.sqrt (tailSlope a) := by
    rw [← Real.sqrt_sq (div_nonneg hH.le he.le)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hL
  refine ⟨a, ha, ?_⟩
  have hh : H < e * Real.sqrt (tailSlope a) := by
    have := (div_lt_iff₀ he).mp hq
    nlinarith
  have hh' := (div_lt_iff₀ hs).mpr hh
  calc
    _ = H / Real.sqrt (tailSlope a) := by dsimp [H]; ring
    _ < e := hh'

theorem tendsto_epsilon : Tendsto epsilon atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun k => hc.trans_le (epsilon_nonneg k))
  · intro e he
    obtain ⟨a, ha, htail⟩ := exists_small_tail (e/2) (by linarith)
    obtain ⟨C, hC, hbound⟩ := exists_excess_bound ha.1.le ha.2
    have ha0 : 0 < a := by linarith [ha.1]
    have ht := (tendsto_inner_error ha0 ha.2 C).eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < e/2))
    filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with k hinner hk
    have hE := epsilon_le_of_excess_le (k := k)
      (B := C*(k : ℝ)*a^(2*k-2)+Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1))
      (by positivity) (hbound k hk)
    linarith

theorem uniform_slice {k : ℕ} (hk : 1 ≤ k) {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    |J k v t|/(k : ℝ) ≤ Real.pi/4*‖g ((v : ℂ)+(t : ℂ)*I)‖^(2*k)+epsilon k := by
  have hh := excess_le_epsilon hk hz
  have hre : ((v : ℂ)+(t : ℂ)*I).re = v := by simp
  have him : ((v : ℂ)+(t : ℂ)*I).im = t := by simp
  simp only [excess, hre, him] at hh
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.StripMaps


namespace OAI

universe u55 u56 u57 u58 u59 u60

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u55} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι : Type u56} [Fintype ι]

def domain (ℓ : ι → E →L[ℂ] ℂ) : Set E := {z | ∀ j, ℓ j z ∈ PlanarLens.D}

def tuple (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) : EuclideanSpace ℂ ι :=
  (EuclideanSpace.equiv ι ℂ).symm (fun j => PlanarLens.g (ℓ j z)^k)

omit [Fintype ι] in
@[simp] theorem tuple_apply (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) (j : ι) :
    tuple ℓ k z j = PlanarLens.g (ℓ j z)^k := rfl

theorem norm_tuple_sq (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) (z : E) :
    ‖tuple ℓ k z‖^2 = ∑ j, ‖PlanarLens.g (ℓ j z)‖^(2*k) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  change ‖PlanarLens.g (ℓ j z)^k‖^2 = _
  rw [norm_pow, ← pow_mul, Nat.mul_comm k 2]

theorem isOpen_domain (ℓ : ι → E →L[ℂ] ℂ) : IsOpen (domain ℓ) := by
  have he : domain ℓ = ⋂ j, (ℓ j) ⁻¹' PlanarLens.D := by ext z; simp [domain]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => PlanarLens.isOpen_D.preimage (ℓ j).continuous)

omit [Fintype ι] in
theorem zero_mem_domain (ℓ : ι → E →L[ℂ] ℂ) : (0 : E) ∈ domain ℓ := by
  intro j
  simpa using PlanarLens.zero_mem_D

theorem analyticOnNhd_tuple (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (tuple ℓ k) (domain ℓ) := by
  intro z hz
  apply ((EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.analyticAt _).comp
  exact AnalyticAt.pi (fun j => ((PlanarLens.analyticOnNhd_g _ (hz j)).comp ((ℓ j).analyticAt z)).pow k)

omit [Fintype ι] in
theorem tuple_zero_iff (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {k : ℕ} (hk : 1 ≤ k)
    {z : E} (hz : z ∈ domain ℓ) : tuple ℓ k z = 0 ↔ z = 0 := by
  constructor
  · intro hf
    apply hℓ
    funext j
    have hj := congrArg (fun w : EuclideanSpace ℂ ι => w j) hf
    have hg : PlanarLens.g (ℓ j z) = 0 := (pow_eq_zero_iff (by omega : k ≠ 0)).mp (by simpa using hj)
    simpa using (PlanarLens.g_eq_zero_iff (hz j)).mp hg
  · rintro rfl
    ext j
    simp only [tuple_apply, map_zero, PlanarLens.g_zero, zero_pow (by omega : k ≠ 0)]
    rfl

theorem tuple_order (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) :
    tuple ℓ k =O[𝓝 (0 : E)] (fun z : E => ‖z‖^k) := by
  have hc (j : ι) : (fun z => PlanarLens.g (ℓ j z)) =O[𝓝 (0 : E)] (fun z : E => ‖z‖) := by
    have ha : AnalyticAt ℂ (fun z => PlanarLens.g (ℓ j z)) (0 : E) :=
      (PlanarLens.analyticOnNhd_g _ (by simpa using PlanarLens.zero_mem_D)).comp ((ℓ j).analyticAt 0)
    have hh := ha.differentiableAt.isBigO_sub.norm_right
    simpa only [map_zero, PlanarLens.g_zero, sub_zero] using hh
  have hp : (fun z j => PlanarLens.g (ℓ j z)^k) =O[𝓝 (0 : E)] (fun z : E => ‖z‖^k) :=
    isBigO_pi.mpr (fun j => (hc j).pow k)
  exact ((EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.isBigO_comp
    (fun z j => PlanarLens.g (ℓ j z)^k) _).trans hp

variable [FiniteDimensional ℂ E]

omit [Fintype ι] in

theorem isBounded_domain (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) : Bornology.IsBounded (domain ℓ) := by
  let L : E →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi ℓ
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hℓ)
  let C := PlanarLens.F '' Metric.closedBall (0 : ℂ) 1
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
    PlanarLens.continuousOn_F_closedBall
  have hc : IsCompact (L ⁻¹' {f : ι → ℂ | ∀ j, f j ∈ C}) :=
    hL.isCompact_preimage (isCompact_pi_infinite (fun _ => hC))
  apply hc.isBounded.subset
  intro z hz j
  exact image_mono Metric.ball_subset_closedBall (hz j)

omit [Fintype ι] in

theorem compact_inner_preimage (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {r : ℝ} (hr : r < 1) :
    IsCompact {z : E | ∀ j, ℓ j z ∈ PlanarLens.F '' Metric.closedBall (0 : ℂ) r} := by
  let L : E →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi ℓ
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hℓ)
  have hC : IsCompact (PlanarLens.F '' Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
      (PlanarLens.continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hr.le))
  have hc := hL.isCompact_preimage (isCompact_pi_infinite (fun _ : ι => hC))
  exact hc

theorem compact_sublevel (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {k : ℕ} (hk : 1 ≤ k)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IsCompact {z : E | z ∈ domain ℓ ∧ ‖tuple ℓ k z‖^2 ≤ s} := by
  have hk0 : 2*k ≠ 0 := by omega
  have hval : (s+1)/2 ∈ Icc ((0 : ℝ)^(2*k)) ((1 : ℝ)^(2*k)) := by
    simp only [zero_pow hk0, one_pow]
    constructor <;> linarith
  obtain ⟨r, hr, hre⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun r : ℝ => r^(2*k)) (by fun_prop) hval
  dsimp only at hre
  have hr0 : 0 ≤ r := hr.1
  have hr1 : r < 1 := by
    by_contra hn
    have her : r = 1 := le_antisymm hr.2 (le_of_not_gt hn)
    rw [her, one_pow] at hre
    linarith
  let C := {z : E | ∀ j, ℓ j z ∈ PlanarLens.F '' Metric.closedBall (0 : ℂ) r}
  have hC : IsCompact C := compact_inner_preimage ℓ hℓ hr1
  have hCD : C ⊆ domain ℓ := by
    intro z hz j
    rcases hz j with ⟨w, hw, he⟩
    refine ⟨w, ?_, he⟩
    have hw' : ‖w‖ ≤ r := by simpa using hw
    simpa using hw'.trans_lt hr1
  have hsub : ∀ z ∈ domain ℓ, ‖tuple ℓ k z‖^2 ≤ s → z ∈ C := by
    intro z hz hzs j
    have hcoord : ‖PlanarLens.g (ℓ j z)‖^(2*k) ≤ ‖tuple ℓ k z‖^2 := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (tuple ℓ k z) j) 2
      simpa only [tuple_apply, norm_pow, ← pow_mul, Nat.mul_comm k 2] using hh
    have hp : ‖PlanarLens.g (ℓ j z)‖^(2*k) ≤ r^(2*k) := by linarith
    have hn : ‖PlanarLens.g (ℓ j z)‖ ≤ r := (pow_le_pow_iff_left₀ (norm_nonneg _) hr0 hk0).mp hp
    exact ⟨PlanarLens.g (ℓ j z), by simpa using hn, PlanarLens.F_g (hz j)⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hcont : Continuous (fun z : C => ‖tuple ℓ k z‖^2) :=
    ((analyticOnNhd_tuple ℓ k).continuousOn.mono hCD).domRestrict.norm.pow 2
  have hclosed : IsClosed {z : C | ‖tuple ℓ k z‖^2 ≤ s} := isClosed_le hcont continuous_const
  have hc := hclosed.isCompact.image continuous_subtype_val
  convert hc using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hsub z hz.1 hz.2⟩, hz.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hCD z.2, hz⟩

end
end PolarStrips

namespace ComplexCoordinates
open scoped ComplexConjugate ContDiff
noncomputable section
variable {ι : Type u57} [Fintype ι]
abbrev R (ι : Type u58) := EuclideanSpace ℝ ι
abbrev C (ι : Type u59) := EuclideanSpace ℂ ι

def re : C ι →L[ℝ] R ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (EuclideanSpace.equiv ι ℝ).symm (fun i => (z i).re)
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro a x; ext i; simp }

def im : C ι →L[ℝ] R ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => (EuclideanSpace.equiv ι ℝ).symm (fun i => (z i).im)
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro a x; ext i; simp }

@[simp] theorem re_apply (z : C ι) (i : ι) : re z i = (z i).re := rfl
@[simp] theorem im_apply (z : C ι) (i : ι) : im z i = (z i).im := rfl

def parts : C ι ≃L[ℝ] R ι × R ι :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => (re z, im z)
    invFun := fun p => (EuclideanSpace.equiv ι ℂ).symm (fun i => (p.1 i : ℂ)+(p.2 i : ℂ)*Complex.I)
    left_inv := by intro z; ext i; simp [Complex.re_add_im]
    right_inv := by intro p; ext i <;> simp
    map_add' := by intros; simp
    map_smul' := by intros; simp }

@[simp] theorem parts_apply (z : C ι) : parts z = (re z, im z) := rfl
@[simp] theorem parts_symm_apply (x y : R ι) (i : ι) :
    parts.symm (x,y) i = (x i : ℂ)+(y i : ℂ)*Complex.I := rfl

def functional (b : R ι) : C ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => ∑ i, (b i : ℂ)*z i
    map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro a x; simp [mul_left_comm, Finset.mul_sum] }

@[simp] theorem functional_apply (b : R ι) (z : C ι) : functional b z = ∑ i, (b i : ℂ)*z i := rfl

theorem re_functional (b : R ι) (z : C ι) :
    (functional b z).re = inner (𝕜 := ℝ) b (re z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem im_functional (b : R ι) (z : C ι) :
    (functional b z).im = inner (𝕜 := ℝ) b (im z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem norm_sq_parts (z : C ι) : ‖z‖^2 = ‖re z‖^2+‖im z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, re_apply, im_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply, ← pow_two, Finset.sum_add_distrib]

theorem real_inner_parts (z w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    inner (𝕜 := ℝ) z w = inner (𝕜 := ℝ) (re z) (re w)+inner (𝕜 := ℝ) (im z) (im w) := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  simp [real_inner_eq_re_inner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Finset.sum_add_distrib]

@[simp] theorem re_I_smul (z : C ι) : re (Complex.I • z) = -im z := by
  ext i; simp [Complex.mul_re]
@[simp] theorem im_I_smul (z : C ι) : im (Complex.I • z) = re z := by
  ext i; simp [Complex.mul_im]

theorem functional_injective {κ : Type u60} (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    Function.Injective (fun z : C ι => fun j => functional (b j) z) := by
  intro z w h
  apply parts.injective
  apply Prod.ext
  · apply hb
    funext j
    have hh := congrArg Complex.re (congrFun h j)
    simpa only [re_functional, parts_apply] using hh
  · apply hb
    funext j
    have hh := congrArg Complex.im (congrFun h j)
    simpa only [im_functional, parts_apply] using hh

end
end ComplexCoordinates

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def primitive (k : ℕ) (z : ℂ) : ℝ := J k z.re z.im

theorem contDiffAt_primitive {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    ContDiffAt ℝ ∞ (primitive k) z :=
  (contDiffOn_J k).contDiffAt (isOpen_D.mem_nhds hz)

theorem J_mono {v w t : ℝ} (hv : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hw : (w : ℂ)+(t : ℂ)*I ∈ D) (hvw : v ≤ w) (k : ℕ) : J k v t ≤ J k w t := by
  have hi := (integrable_density hv k).symm.trans (integrable_density hw k)
  have he := intervalIntegral.integral_add_adjacent_intervals (integrable_density hv k) hi
  have hp : 0 ≤ ∫ h in v..w, density k ((h : ℂ)+(t : ℂ)*I) :=
    intervalIntegral.integral_nonneg hvw (fun _ _ => density_nonneg _ _)
  unfold J
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith

theorem J_product_nonneg {v w t : ℝ} (hv : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hw : (w : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    0 ≤ (J k w t-J k v t)*(w-v) := by
  rcases le_total v w with h | h
  · exact mul_nonneg (sub_nonneg.mpr (J_mono hv hw h k)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (J_mono hw hv h k)) (sub_nonpos.mpr h)

theorem fderiv_primitive_one {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    fderiv ℝ (primitive k) z 1 = (k : ℝ)^2*density k z := by
  have hp := (contDiffAt_primitive hz k).differentiableAt (by simp)
  have hd : HasDerivAt (fun v : ℝ => (v : ℂ)+(z.im : ℂ)*I) 1 z.re :=
    by simpa using ((hasDerivAt_id (z.re : ℂ)).comp_ofReal.add_const ((z.im : ℂ)*I))
  have hp' : HasFDerivAt (primitive k) (fderiv ℝ (primitive k) z) ((z.re : ℂ)+(z.im : ℂ)*I) := by
    simpa only [Complex.re_add_im] using hp.hasFDerivAt
  have hh := hp'.comp_hasDerivAt z.re hd
  have hj := hasDerivAt_J (v := z.re) (t := z.im) (by simpa only [Complex.re_add_im] using hz) k
  have hh' : HasDerivAt (fun v => J k v z.im) (fderiv ℝ (primitive k) z 1) z.re := by
    simpa [primitive, Function.comp_def] using hh
  simpa only [Complex.re_add_im] using hh'.unique hj

theorem fderiv_primitive_apply {z : ℂ} (hz : z ∈ D) (k : ℕ) (h : ℂ) :
    fderiv ℝ (primitive k) z h =
      (k : ℝ)^2*density k z * h.re + fderiv ℝ (primitive k) z I * h.im := by
  have he : h = h.re • (1 : ℂ)+h.im • I := by apply Complex.ext <;> simp
  calc
    fderiv ℝ (primitive k) z h = fderiv ℝ (primitive k) z (h.re • (1 : ℂ)+h.im • I) := congrArg _ he
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul, fderiv_primitive_one hz k]; ring

end
end PlanarLens

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.StripEmbedding


namespace OAI

universe u61 u62 u63 u64 u65 u66 u67 u68 u69

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set ComplexCoordinates
open scoped ContDiff
noncomputable section
variable {ι : Type u61} {κ : Type u62} [Fintype ι] [Fintype κ]

def phase (b : κ → R ι) (k : ℕ) (z : C ι) : R ι × R ι :=
  (im z, -re z - ∑ j, PlanarLens.primitive k (functional (b j) z) • b j)

theorem contDiffAt_phase (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) : ContDiffAt ℝ ∞ (phase b k) z := by
  change ContDiffAt ℝ ∞ (fun z : C ι => (ComplexCoordinates.im z, -ComplexCoordinates.re z - ∑ j, PlanarLens.primitive k (functional (b j) z) • b j)) z
  refine (ComplexCoordinates.im : C ι →L[ℝ] R ι).contDiff.contDiffAt.prodMk
    ((ComplexCoordinates.re : C ι →L[ℝ] R ι).contDiff.contDiffAt.neg.sub ?_)
  apply ContDiffAt.sum
  intro j _
  exact ((PlanarLens.contDiffAt_primitive (hz j) k).comp z
    ((functional (b j)).restrictScalars ℝ).contDiff.contDiffAt).smul contDiffAt_const

theorem momentum_monotonic (b : κ → R ι) (k : ℕ) {z w : C ι}
    (hz : z ∈ domain (fun j => functional (b j)))
    (hw : w ∈ domain (fun j => functional (b j))) (hx : im z = im w) :
    inner (𝕜 := ℝ) ((phase b k w).2-(phase b k z).2) (re w-re z) ≤ -‖re w-re z‖^2 := by
  have hj (j : κ) : 0 ≤
      (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) *
      inner (𝕜 := ℝ) (b j) (re w-re z) := by
    have ht : (functional (b j) z).im = (functional (b j) w).im := by rw [im_functional, im_functional, hx]
    have hv : (((functional (b j) z).re : ℂ)+((functional (b j) w).im : ℂ)*Complex.I) ∈ PlanarLens.D := by
      rw [← ht, Complex.re_add_im]; exact hz j
    have hh := PlanarLens.J_product_nonneg (w := (functional (b j) w).re) hv (by simpa only [Complex.re_add_im] using hw j) k
    simpa only [PlanarLens.primitive, ht, inner_sub_right, ← re_functional] using hh
  have he : (phase b k w).2-(phase b k z).2 = -(re w-re z) -
      ∑ j, (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) • b j := by
    simp only [phase, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [he, inner_sub_left, inner_neg_left, real_inner_self_eq_norm_sq]
  have hsum : 0 ≤ inner (𝕜 := ℝ)
      (∑ j, (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) • b j)
      (re w-re z) := by
    simp only [sum_inner, real_inner_smul_left]
    exact Finset.sum_nonneg (fun j _ => hj j)
  linarith

theorem injOn_phase (b : κ → R ι) (k : ℕ) :
    InjOn (phase b k) (domain (fun j => functional (b j))) := by
  intro z hz w hw he
  have hx : im z = im w := congrArg Prod.fst he
  have hp : (phase b k w).2-(phase b k z).2 = 0 := sub_eq_zero.mpr (congrArg Prod.snd he).symm
  have hh := momentum_monotonic b k hz hw hx
  rw [hp, inner_zero_left] at hh
  have hr : re w = re z := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (re w-re z)]))
  apply parts.injective
  exact Prod.ext hr.symm hx

end
end PolarStrips

namespace ComplexPotential
open ComplexCoordinates Set Filter
open scoped Topology ContDiff
noncomputable section

variable {E : Type u63} {F : Type u64} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem ddc_holomorphic_norm_sq {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : AnalyticOnNhd ℂ f U) {z : E} (hz : z ∈ U) (v w : E) :
    let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    ddc (complexStructure E) (fun x => ‖f x‖^2) z v w =
      standardTensor (complexStructure F) (fderiv ℝ f z v) (fderiv ℝ f z w) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have he := ddc_comp (complexStructure E) (complexStructure F)
    ((hf z hz).contDiffAt.restrict_scalars ℝ) (contDiff_norm_sq ℝ).contDiffAt
    (show ∀ᶠ x in 𝓝 z, ∀ a, fderiv ℝ f x (complexStructure E a) = complexStructure F (fderiv ℝ f x a) by
      filter_upwards [hU.mem_nhds hz] with x hx
      exact fderiv_commutes_complexStructure (hf x hx).differentiableAt) v w
  rw [ddc_norm_sq (complexStructure F) complexStructure_skew] at he
  exact he

variable {ι : Type u65} [Fintype ι]

def phaseForm (v w : R ι × R ι) : ℝ :=
  inner (𝕜 := ℝ) v.1 w.2-inner (𝕜 := ℝ) w.1 v.2

theorem standardTensor_parts (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    standardTensor (complexStructure (C ι)) v w = phaseForm (parts v) (parts w) := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  dsimp only
  rw [standardTensor_apply, complexStructure_apply, real_inner_parts]
  simp only [re_I_smul, im_I_smul, inner_neg_left, phaseForm, parts_apply]
  rw [real_inner_comm (im v) (re w)]
  ring

theorem standardTensor_coordinates (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    standardTensor (complexStructure (C ι)) v w =
      ∑ i, ((v i).re*(w i).im-(w i).re*(v i).im) := by
  dsimp only
  rw [standardTensor_parts]
  simp [phaseForm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_sub_distrib, mul_comm]

theorem scalar_wedge_mul (c v w : ℂ) :
    (c*v).re*(c*w).im-(c*w).re*(c*v).im =
      ‖c‖^2*(v.re*w.im-w.re*v.im) := by
  rw [Complex.sq_norm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

end
end ComplexPotential

namespace PolarStrips
open Set Filter ComplexCoordinates ComplexPotential
open scoped Topology ContDiff
noncomputable section
variable {ι : Type u66} {κ : Type u67} [Fintype ι] [Fintype κ]

theorem fderiv_tuple_apply (ℓ : κ → C ι →L[ℂ] ℂ) (k : ℕ) {z : C ι}
    (hz : z ∈ domain ℓ) (v : C ι) (j : κ) :
    fderiv ℝ (tuple ℓ k) z v j =
      (k : ℂ)*PlanarLens.g (ℓ j z)^(k-1)*deriv PlanarLens.g (ℓ j z)*ℓ j v := by
  have ht := ((analyticOnNhd_tuple ℓ k z hz).differentiableAt.restrictScalars ℝ).hasFDerivAt
  have hp := (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : κ => ℂ) j).restrictScalars ℝ).hasFDerivAt.comp z ht)
  have hg := ((PlanarLens.analyticOnNhd_g _ (hz j)).differentiableAt.hasDerivAt.pow k).hasFDerivAt
  have hc := (hg.comp z (ℓ j).hasFDerivAt).restrictScalars ℝ
  have he := hc.unique hp
  have hh := congrArg (fun L : C ι →L[ℝ] ℂ => L v) he
  change (ℓ j v)*((k : ℂ)*PlanarLens.g (ℓ j z)^(k-1)*deriv PlanarLens.g (ℓ j z)) =
    fderiv ℝ (tuple ℓ k) z v j at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh.symm

theorem norm_coefficient (k : ℕ) (w : ℂ) :
    ‖(k : ℂ)*PlanarLens.g w^(k-1)*deriv PlanarLens.g w‖^2 =
      (k : ℝ)^2*PlanarLens.density k w := by
  simp only [norm_mul, norm_pow, Complex.norm_natCast, mul_pow, ← pow_mul, PlanarLens.density]
  have he : (k-1)*2 = 2*k-2 := by omega
  rw [he]
  ring

theorem fderiv_phase_apply (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v : C ι) :
    fderiv ℝ (phase b k) z v = (im v, -re v - ∑ j,
      fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) • b j) := by
  let L : κ → C ι →L[ℝ] R ι := fun j =>
    ((fderiv ℝ (PlanarLens.primitive k) (functional (b j) z)).comp
      ((functional (b j)).restrictScalars ℝ)).smulRight (b j)
  have hj (j : κ) : HasFDerivAt (fun x : C ι => PlanarLens.primitive k (functional (b j) x) • b j) (L j) z :=
    (((PlanarLens.contDiffAt_primitive (hz j) k).differentiableAt (by simp)).hasFDerivAt.comp z
      ((functional (b j)).restrictScalars ℝ).hasFDerivAt).smul_const (b j)
  have hs : HasFDerivAt (fun x : C ι => ∑ j, PlanarLens.primitive k (functional (b j) x) • b j)
      (∑ j, L j) z := by
    simpa only [Finset.sum_fn] using (HasFDerivAt.sum (u := Finset.univ) (fun j _ => hj j))
  have hd : HasFDerivAt (phase b k)
      ((im : C ι →L[ℝ] R ι).prod (-(re : C ι →L[ℝ] R ι)-∑ j, L j)) z :=
    im.hasFDerivAt.prodMk (re.hasFDerivAt.neg.sub hs)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, sub_apply,
    neg_apply, sum_apply, L,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem phase_form_formula (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v w : C ι) :
    phaseForm (fderiv ℝ (phase b k) z v) (fderiv ℝ (phase b k) z w) =
      phaseForm (parts v) (parts w) + ∑ j,
        (k : ℝ)^2*PlanarLens.density k (functional (b j) z) *
          ((functional (b j) v).re*(functional (b j) w).im -
            (functional (b j) w).re*(functional (b j) v).im) := by
  rw [fderiv_phase_apply b k hz, fderiv_phase_apply b k hz]
  have he (a : C ι) (j : κ) : inner (𝕜 := ℝ) (im a) (b j) = (functional (b j) a).im := by
    rw [real_inner_comm, im_functional]
  have hf : phaseForm (im v, -re v - ∑ j,
        fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) • b j)
      (im w, -re w - ∑ j,
        fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) w) • b j) =
      phaseForm (parts v) (parts w) + ∑ j,
        (fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) * (functional (b j) w).im -
         fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) w) * (functional (b j) v).im) := by
    simp only [phaseForm, parts_apply, inner_sub_right, inner_neg_right, inner_sum,
      real_inner_smul_right, he, Finset.sum_sub_distrib]
    rw [real_inner_comm (im v) (re w), real_inner_comm (im w) (re v)]
    ring
  rw [hf]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [PlanarLens.fderiv_primitive_apply (hz j) k (functional (b j) v),
    PlanarLens.fderiv_primitive_apply (hz j) k (functional (b j) w)]
  ring

theorem phase_pullback (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    phaseForm (fderiv ℝ (phase b k) z v) (fderiv ℝ (phase b k) z w) =
      ddc (complexStructure (C ι)) (fun x => ‖x‖^2 + ‖tuple (fun j => functional (b j)) k x‖^2) z v w := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ (C κ) := InnerProductSpace.complexToReal
  let ℓ := fun j => functional (b j)
  have hτ : ContDiffAt ℝ ∞ (fun x => ‖tuple ℓ k x‖^2) z :=
    ((analyticOnNhd_tuple ℓ k z hz).contDiffAt.restrict_scalars ℝ).norm_sq ℂ
  dsimp only
  rw [ddc_add _ (contDiff_norm_sq ℝ).contDiffAt hτ,
    add_apply, add_apply,
    ddc_norm_sq _ complexStructure_skew,
    ddc_holomorphic_norm_sq (isOpen_domain ℓ) (analyticOnNhd_tuple ℓ k) hz,
    standardTensor_parts v w,
    standardTensor_coordinates (fderiv ℝ (tuple ℓ k) z v) (fderiv ℝ (tuple ℓ k) z w),
    phase_form_formula b k hz]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_tuple_apply ℓ k hz v j, fderiv_tuple_apply ℓ k hz w j, scalar_wedge_mul, norm_coefficient]

end
end PolarStrips

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u68} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def polar (K : Set E) : Set E := {p | ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ 1}

theorem polar_antitone {K L : Set E} (h : K ⊆ L) : polar L ⊆ polar K :=
  fun _ hp q hq => hp q (h hq)

theorem mem_interior_polar_of_bound {K : Set E} {p : E} {B r : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ q ∈ K, ‖q‖ ≤ B) (hr : r < 1)
    (hp : ∀ q ∈ K, inner (𝕜 := ℝ) q p ≤ r) : p ∈ interior (polar K) := by
  let δ := (1-r)/(B+1)
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (Metric.ball_mem_nhds p hδ)
  intro w hw q hq
  have hw' : ‖w-p‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hinner := real_inner_le_norm q (w-p)
  have hbq := hbound q hq
  have hmul : ‖q‖*‖w-p‖ ≤ (B+1)*δ := by
    calc
      ‖q‖*‖w-p‖ ≤ B*δ := mul_le_mul hbq hw'.le (norm_nonneg _) hB
      _ ≤ (B+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have hδeq : (B+1)*δ = 1-r := by dsimp [δ]; field_simp
  rw [inner_sub_right] at hinner
  linarith [hp q hq]

variable {κ : Type u69}

def stripBody (b : κ → E) : Set E := {x | ∀ j, |inner (𝕜 := ℝ) (b j) x| ≤ 1}

variable [Fintype κ]

theorem mem_interior_stripBody (b : κ → E) {x : E}
    (hx : ∀ j, |inner (𝕜 := ℝ) (b j) x| < 1) : x ∈ interior (stripBody b) := by
  let U : Set E := {y | ∀ j, |inner (𝕜 := ℝ) (b j) y| < 1}
  have hopen : IsOpen U := by
    have he : U = ⋂ j, {y | |inner (𝕜 := ℝ) (b j) y| < 1} := by ext y; simp [U]
    rw [he]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (by fun_prop) continuous_const
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hopen.mem_nhds hx) (fun y hy j => (hy j).le))

theorem zero_mem_interior_stripBody (b : κ → E) : (0 : E) ∈ interior (stripBody b) :=
  mem_interior_stripBody b (by intro j; simp)

variable [FiniteDimensional ℝ E]

omit [Fintype κ] in
theorem isCompact_stripBody (b : κ → E)
    (hb : Function.Injective (fun x : E => fun j => inner (𝕜 := ℝ) (b j) x)) :
    IsCompact (stripBody b) := by
  let L : E →L[ℝ] (κ → ℝ) := ContinuousLinearMap.pi (fun j => innerSL ℝ (b j))
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hb)
  have hc := hL.isCompact_preimage (isCompact_pi_infinite (fun _ : κ => isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
  convert hc using 1
  ext x
  simp only [stripBody, mem_ofPred_eq, mem_preimage, ContinuousLinearMap.pi_apply, innerSL_apply_apply,
    mem_Icc, ← abs_le, L]

end
end ConvexPolar

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.MomentumBounds


namespace OAI

universe u70 u71 u72 u73

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter ComplexCoordinates
open scoped Topology ContDiff
noncomputable section
variable {ι : Type u70} {κ : Type u71} [Fintype ι] [Fintype κ]

theorem position_mem_interior (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) :
    (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) := by
  apply ConvexPolar.mem_interior_stripBody
  intro j
  change |inner (𝕜 := ℝ) (b j) (im z)| < 1
  rw [← im_functional]
  exact abs_lt.mpr (PlanarLens.im_mem_Ioo (hz j))

theorem norm_re_le (z : C ι) : ‖re z‖ ≤ ‖z‖ := by
  have hh := norm_sq_parts z
  nlinarith [sq_nonneg ‖im z‖, norm_nonneg (re z), norm_nonneg z]

theorem momentum_bound (b : κ → R ι) {k : ℕ} (hk : 1 ≤ k) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) {y : R ι}
    (hy : y ∈ ConvexPolar.stripBody b) {A B : ℝ}
    (hzA : ‖z‖ ≤ A) (hyB : ‖y‖ ≤ B) :
    inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
      A*B/(k : ℝ) + Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
        (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hu : inner (𝕜 := ℝ) y (-re z) ≤ A*B := by
    have hh := real_inner_le_norm y (-re z)
    rw [norm_neg] at hh
    have hm := mul_le_mul hyB ((norm_re_le z).trans hzA) (norm_nonneg _) (le_trans (norm_nonneg _) hyB)
    nlinarith
  have hj (j : κ) : -(PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)) ≤
      |PlanarLens.primitive k (functional (b j) z)| := by
    have hh : |inner (𝕜 := ℝ) y (b j)| ≤ 1 := by rw [real_inner_comm]; exact hy j
    calc
      _ ≤ |PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)| := neg_le_abs _
      _ = |PlanarLens.primitive k (functional (b j) z)| * |inner (𝕜 := ℝ) y (b j)| := abs_mul _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hh (abs_nonneg (PlanarLens.primitive k (functional (b j) z)))
  have hsum : inner (𝕜 := ℝ) y (phase b k z).2 ≤ A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)| := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [phase, inner_sub_right, inner_sum, real_inner_smul_right, Finset.sum_neg_distrib] at ⊢ hh
    linarith
  have hslice (j : κ) : |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) ≤
      Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k := by
    simpa only [PlanarLens.primitive, Complex.re_add_im] using
      PlanarLens.uniform_slice hk (v := (functional (b j) z).re) (t := (functional (b j) z).im)
        (by simpa only [Complex.re_add_im] using hz j)
  calc
    _ ≤ (A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)|)/(k : ℝ) :=
      div_le_div_of_nonneg_right hsum hkpos.le
    _ = A*B/(k : ℝ) + ∑ j, |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) := by
      rw [add_div, Finset.sum_div]
    _ ≤ A*B/(k : ℝ) + ∑ j, (Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hslice j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← norm_tuple_sq]; simp [add_assoc]

theorem exists_uniform_momentum_bound (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ ConvexPolar.stripBody b, ‖y‖ ≤ B) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ z ∈ domain (fun j => functional (b j)),
        ∀ y ∈ ConvexPolar.stripBody b,
          inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
            C/(k : ℝ)+Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
              (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  obtain ⟨A, hA⟩ := (isBounded_domain _ (functional_injective b hb)).exists_norm_le
  obtain ⟨B, hB⟩ := (ConvexPolar.isCompact_stripBody b hb).isBounded.exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg (0 : C ι)).trans (hA 0 (zero_mem_domain _))
  have hB0 : 0 ≤ B := (norm_nonneg (0 : R ι)).trans (hB 0 (interior_subset (ConvexPolar.zero_mem_interior_stripBody b)))
  refine ⟨A*B, B, mul_nonneg hA0 hB0, hB0, hB, ?_⟩
  intro k hk z hz y hy
  exact momentum_bound b hk hz hy (hA z hz) (hB y hy)

theorem exists_scaled_image (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x))
    {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ z : C ι,
      z ∈ domain (fun j => functional (b j)) → ‖tuple (fun j => functional (b j)) k z‖^2 < 1 →
      (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) ∧
        (((1+η)*Real.pi*(k : ℝ)/4)⁻¹ • (phase b k z).2) ∈ interior (ConvexPolar.polar (ConvexPolar.stripBody b)) := by
  obtain ⟨C, B, _hC, hB, hbound, hmoment⟩ := exists_uniform_momentum_bound b hb
  have ht : Tendsto (fun k : ℕ => C/(k : ℝ)+(Fintype.card κ : ℝ)*PlanarLens.epsilon k) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (PlanarLens.tendsto_epsilon.const_mul (Fintype.card κ : ℝ))
  have hsmall := ht.eventually (eventually_lt_nhds (show (0 : ℝ) < η*Real.pi/4 by positivity))
  obtain ⟨k, hk, hksmall⟩ := (eventually_ge_atTop (1 : ℕ)).and hsmall |>.exists
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let T := (1+η)*Real.pi/4
  have hT : 0 < T := by dsimp [T]; positivity
  have hTsmall : C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k < T := by dsimp [T]; nlinarith
  refine ⟨k, hk, fun z hz hτ => ⟨position_mem_interior b k hz, ?_⟩⟩
  apply ConvexPolar.mem_interior_polar_of_bound hB hbound
    (r := (C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k)/T)
  · exact (div_lt_one hT).mpr hTsmall
  · intro y hy
    have hh := hmoment k hk z hz y hy
    have hp : inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ) ≤
        C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
      have hm := mul_le_mul_of_nonneg_left hτ.le (by positivity : (0 : ℝ) ≤ Real.pi/4)
      linarith
    have hd := div_le_div_of_nonneg_right hp hT.le
    calc
      _ = inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ)/T := by
        rw [real_inner_smul_right]
        dsimp only [T]
        field_simp
      _ ≤ _ := hd

end
end PolarStrips

open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar

end SymmetricPolar

namespace LocalEmbedding
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {E : Type u72} {F : Type u73} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem open_image {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hs := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨e, heq⟩ := hD x hx
  have he : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [heq]
    exact (hs.differentiableAt (by simp)).hasFDerivAt
  rw [← (hs.hasStrictFDerivAt' he (by simp)).map_nhds_eq_of_equiv]
  change f ⁻¹' (f '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun y hy => mem_image_of_mem f hy)

theorem isOpenEmbedding {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    Topology.IsOpenEmbedding (fun x : U => f x) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuousOn.domRestrict
  · intro x y h; exact Subtype.ext (hi x.2 y.2 h)
  · intro V hV
    have hUV : Subtype.val '' V ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have huV : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val _ hV
    have ho := open_image huV (hf.mono hUV) (fun x hx => hD x (hUV hx))
    change IsOpen ((fun x : U => f x) '' V)
    rw [image_image] at ho
    exact ho

end
end LocalEmbedding

namespace SymmetricPolar
open Set Filter
open scoped ContDiff Topology
noncomputable section
variable {n : ℕ}

theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

def diagScale (a b : ℝ) : Phase n →L[ℝ] Phase n :=
  (a • ContinuousLinearMap.fst ℝ (Position n) (Position n)).prod
    (b • ContinuousLinearMap.snd ℝ (Position n) (Position n))

@[simp] theorem diagScale_apply (a b : ℝ) (z : Phase n) : diagScale a b z = (a • z.1, b • z.2) := rfl

theorem diagScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (diagScale a b : Phase n → Phase n) := by
  intro x y h
  exact Prod.ext ((smul_right_injective _ ha) (congrArg Prod.fst h))
    ((smul_right_injective _ hb) (congrArg Prod.snd h))

theorem omega0_diagScale (a b : ℝ) (v w : Phase n) :
    omega0 (diagScale a b v) (diagScale a b w) = (a*b)*omega0 v w := by
  simp only [omega0, diagScale_apply, real_inner_smul_left, real_inner_smul_right]
  ring

theorem omega0_nondegenerate (v : Phase n) (h : ∀ w : Phase n, omega0 v w = 0) : v = 0 := by
  have hh := h (-v.2, v.1)
  simp only [omega0, inner_neg_left, real_inner_self_eq_norm_sq, sub_neg_eq_add] at hh
  have h1 : v.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.1, sq_nonneg ‖v.2‖])
  have h2 : v.2 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.2, sq_nonneg ‖v.1‖])
  exact Prod.ext h1 h2

theorem isInvertible_of_preserves_omega0 (L : Phase n →L[ℝ] Phase n)
    (hL : ∀ v w, omega0 (L v) (L w) = omega0 v w) : L.IsInvertible := by
  have hi : Function.Injective L := by
    intro v w hvw
    have hz : L (v-w) = 0 := by rw [map_sub, hvw, sub_self]
    apply sub_eq_zero.mp
    apply omega0_nondegenerate
    intro a
    rw [← hL, hz]
    simp [omega0]
  have hs : Function.Surjective L := LinearMap.surjective_of_injective hi
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem hasSymplecticEmbedding_of_injOn {U V : Set (Phase n)} (hU : IsOpen U)
    {e : Phase n → Phase n} (he : ContDiffOn ℝ ∞ e U) (hi : InjOn e U)
    (hm : MapsTo e U V) (hω : ∀ z ∈ U, ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding U V := by
  refine ⟨e, he, ?_, hm, hω⟩
  exact (LocalEmbedding.isOpenEmbedding hU he hi (fun z hz => isInvertible_of_preserves_omega0 _ (hω z hz))).isEmbedding

theorem HasSymplecticEmbedding.mono_target {U V W : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) (hVW : V ⊆ W) : HasSymplecticEmbedding U W := by
  rcases h with ⟨e, he, hi, hm, hω⟩
  exact ⟨e, he, hi, hm.mono_right hVW, hω⟩

theorem HasSymplecticEmbedding.injOn {U : Set (Phase n)} {e : Phase n → Phase n}
    (he : Topology.IsEmbedding (fun z : U => e z)) : InjOn e U := by
  intro x hx y hy h
  exact congrArg Subtype.val (he.injective (show e (⟨x,hx⟩ : U) = e (⟨y,hy⟩ : U) from h))

theorem mapsTo_scaled_ball {lam c : ℝ} (hlam : 0 < lam) :
    MapsTo (diagScale (Real.sqrt lam) (Real.sqrt lam) : Phase n → Phase n)
      (capacityBall n c) (capacityBall n (lam*c)) := by
  intro z hz
  change Real.pi*(‖Real.sqrt lam • z.1‖^2+‖Real.sqrt lam • z.2‖^2) < lam*c
  have hsq : |Real.sqrt lam|^2 = lam := by rw [sq_abs, Real.sq_sqrt hlam.le]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, hsq]
  have hh := mul_lt_mul_of_pos_left hz hlam
  nlinarith

theorem embedding_of_scaled_ball_map {lam c a b : ℝ} (hlam : 0 < lam) (hab : a*b = lam⁻¹)
    {V : Set (Phase n)} {e : Phase n → Phase n}
    (he : ContDiffOn ℝ ∞ e (capacityBall n (lam*c)))
    (hi : InjOn e (capacityBall n (lam*c)))
    (hm : MapsTo (fun z => diagScale a b (e z)) (capacityBall n (lam*c)) V)
    (hω : ∀ z ∈ capacityBall n (lam*c), ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding (capacityBall n c) V := by
  let D : Phase n →L[ℝ] Phase n := diagScale (Real.sqrt lam) (Real.sqrt lam)
  let L : Phase n →L[ℝ] Phase n := diagScale a b
  let F : Phase n → Phase n := fun z => L (e (D z))
  have hD : MapsTo D (capacityBall n c) (capacityBall n (lam*c)) := mapsTo_scaled_ball hlam
  have hLinj : Function.Injective L := diagScale_injective (left_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
    (right_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
  have hDinj : Function.Injective D := diagScale_injective (Real.sqrt_pos.mpr hlam).ne' (Real.sqrt_pos.mpr hlam).ne'
  have hs (z : Phase n) (hz : z ∈ capacityBall n c) : ContDiffAt ℝ ∞ e (D z) :=
    he.contDiffAt ((isOpen_capacityBall _ _).mem_nhds (hD hz))
  apply hasSymplecticEmbedding_of_injOn (isOpen_capacityBall n c) (e := F)
  · intro z hz
    exact (L.contDiff.contDiffAt.comp z ((hs z hz).comp z D.contDiff.contDiffAt)).contDiffWithinAt
  · intro z hz w hw h
    exact hDinj (hi (hD hz) (hD hw) (hLinj h))
  · intro z hz
    exact hm (hD hz)
  · intro z hz v w
    have hd : HasFDerivAt F (L.comp ((fderiv ℝ e (D z)).comp D)) z :=
      L.hasFDerivAt.comp z (((hs z hz).differentiableAt (by simp)).hasFDerivAt.comp z D.hasFDerivAt)
    rw [hd.fderiv]
    change omega0 (diagScale a b (fderiv ℝ e (D z) (D v)))
      (diagScale a b (fderiv ℝ e (D z) (D w))) = _
    rw [omega0_diagScale, hω _ (hD hz), hab, omega0_diagScale]
    rw [← pow_two, Real.sq_sqrt hlam.le, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

end
end SymmetricPolar

end LowerBoundInline

end OAI

end

section
-- OAI.Geometry.PolarProducts.PolarApproximation


namespace OAI

universe u74 u75 u76 u77

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set Filter ComplexCoordinates ComplexPotential PolarStrips
open scoped Topology ContDiff
noncomputable section
variable {n : ℕ} {κ : Type u74} [Fintype κ]

theorem exists_positive_slack {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∃ η : ℝ, 0 < η ∧ (1+η)*c < d := by
  let η := (d-c)/(2*c)
  have hη : 0 < η := div_pos (sub_pos.mpr hcd) (mul_pos (by norm_num) hc)
  have he : η*c = (d-c)/2 := by dsimp [η]; field_simp
  exact ⟨η, hη, by nlinarith⟩

theorem finite_strips_embedding (b : κ → Position n)
    (hb : Function.Injective (fun x : Position n => fun j => inner (𝕜 := ℝ) (b j) x))
    {c : ℝ} (hc : 0 < c) (hc4 : c < 4) :
    HasSymplecticEmbedding (capacityBall n c)
      (interior (ConvexPolar.stripBody b) ×ˢ interior (ConvexPolar.polar (ConvexPolar.stripBody b))) := by
  let : InnerProductSpace ℝ (C (Fin n)) := InnerProductSpace.complexToReal
  obtain ⟨η, hη, hηc⟩ := exists_positive_slack hc hc4
  obtain ⟨k, hk, hscaled⟩ := exists_scaled_image b hb hη
  let ℓ := fun j => functional (b j)
  have hℓ : Function.Injective (fun z : C (Fin n) => fun j => ℓ j z) := functional_injective b hb
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let S := (1+η)*Real.pi*(k : ℝ)/4
  have hS : 0 < S := by dsimp [S]; positivity
  let a := S*c/Real.pi
  have ha : 0 < a := div_pos (mul_pos hS hc) Real.pi_pos
  have hak : a < (k : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    have hh := mul_lt_mul_of_pos_right hηc (mul_pos Real.pi_pos hkpos)
    dsimp [S]
    nlinarith
  obtain ⟨Q, hQ, _hQi, hQm, hQω⟩ :=
    exists_ball_from_holomorphic_zero (isOpen_domain ℓ) (zero_mem_domain ℓ)
      (analyticOnNhd_tuple ℓ k) (fun x hx => tuple_zero_iff ℓ hℓ hk hx) hk (tuple_order ℓ k)
      (fun s hs hs1 => compact_sublevel ℓ hℓ hk hs hs1) ha hak
  let i : Phase n →L[ℝ] C (Fin n) := parts.symm.toContinuousLinearMap
  have hi (z : Phase n) (hz : z ∈ capacityBall n (S*c)) : ‖i z‖^2 < a := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    have he : ‖i z‖^2 = ‖z.1‖^2+‖z.2‖^2 := by
      have hh := norm_sq_parts (parts.symm z)
      have hre : re (parts.symm z) = z.1 := congrArg Prod.fst (parts.apply_symm_apply z)
      have him : im (parts.symm z) = z.2 := congrArg Prod.snd (parts.apply_symm_apply z)
      simpa only [i, ContinuousLinearEquiv.coe_coe, hre, him] using hh
    rw [he, mul_comm]
    exact hz
  let e : Phase n → Phase n := fun z => phase b k (Q (i z))
  have hs (z : Phase n) (hz : z ∈ capacityBall n (S*c)) : ContDiffAt ℝ ∞ e z := by
    have hphase : ContDiffAt ℝ ∞ (phase b k) (Q (i z)) :=
      contDiffAt_phase b k (hQm _ (hi z hz)).1
    have hh := hphase.comp z (hQ.contDiffAt.comp z i.contDiff.contDiffAt)
    simpa only [Function.comp_def, e] using hh
  apply embedding_of_scaled_ball_map hS (a := 1) (b := S⁻¹) (by simp) (e := e)
  · exact fun z hz => (hs z hz).contDiffWithinAt
  · intro z hz w hw he
    have hq : Q (i z) = Q (i w) := injOn_phase b k (hQm _ (hi z hz)).1 (hQm _ (hi w hw)).1 he
    exact parts.symm.injective (Q.injective hq)
  · intro z hz
    have hm := hscaled (Q (i z)) (hQm _ (hi z hz)).1 (hQm _ (hi z hz)).2
    simpa only [diagScale_apply, one_smul, e, S, Set.mem_prod] using hm
  · intro z hz v w
    have hphase : HasFDerivAt (phase b k) (fderiv ℝ (phase b k) (Q (i z))) (Q (i z)) :=
      ((contDiffAt_phase b k (hQm _ (hi z hz)).1).differentiableAt (by simp)).hasFDerivAt
    have hd : HasFDerivAt e ((fderiv ℝ (phase b k) (Q (i z))).comp
        ((fderiv ℝ (Q : C (Fin n) → C (Fin n)) (i z)).comp i)) z := by
      have hh := hphase.comp z ((hQ.differentiable (by simp) (i z)).hasFDerivAt.comp z i.hasFDerivAt)
      simpa only [Function.comp_def, e] using hh
    rw [hd.fderiv]
    change phaseForm (fderiv ℝ (phase b k) (Q (i z)) (fderiv ℝ (Q : C (Fin n) → C (Fin n)) (i z) (i v)))
      (fderiv ℝ (phase b k) (Q (i z)) (fderiv ℝ (Q : C (Fin n) → C (Fin n)) (i z) (i w))) = _
    rw [phase_pullback b k (hQm _ (hi z hz)).1, hQω _ (hi z hz), standardTensor_parts]
    change phaseForm (parts (parts.symm v)) (parts (parts.symm w)) = _
    rw [parts.apply_symm_apply, parts.apply_symm_apply]
    rfl

end
end SymmetricPolar

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u75} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem zero_mem_interior_of_symmetric {K : Set E} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) (hs : ∀ x, x ∈ K ↔ -x ∈ K) : (0 : E) ∈ interior K := by
  obtain ⟨x, hx⟩ := hi
  have hn : -x ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    have hh : K ∈ 𝓝 (-(-x)) := by simpa using mem_interior_iff_mem_nhds.mp hx
    have hh' := continuous_neg.continuousAt.preimage_mem_nhds hh
    have he : (fun y : E => -y) ⁻¹' K = K := by ext y; exact (hs y).symm
    rwa [he] at hh'
  have hm := hK.interior hx hn (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simpa using hm

theorem isClosed_polar (K : Set E) : IsClosed (polar K) := by
  have he : polar K = ⋂ q ∈ K, {p : E | inner (𝕜 := ℝ) q p ≤ 1} := by ext p; simp [polar]
  rw [he]
  exact isClosed_biInter (fun q _ => isClosed_le (by fun_prop) continuous_const)

theorem polar_abs_pairing {K : Set E} (hs : ∀ x, x ∈ K ↔ -x ∈ K)
    {p : E} (hp : p ∈ polar K) {x : E} (hx : x ∈ K) : |inner (𝕜 := ℝ) p x| ≤ 1 := by
  apply abs_le.mpr
  have hn := hp (-x) ((hs x).mp hx)
  rw [inner_neg_left, real_inner_comm] at hn
  exact ⟨by linarith, by rw [real_inner_comm]; exact hp x hx⟩

theorem norm_smul_normalized {x : E} (hx : x ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r/‖x‖) • x‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (norm_nonneg _)), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem normalized_inner {x : E} (hx : x ≠ 0) (r : ℝ) :
    inner (𝕜 := ℝ) ((r/‖x‖) • x) x = r*‖x‖ := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

theorem norm_le_of_mem_polar {K : Set E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : E) r ⊆ K) {p : E} (hp : p ∈ polar K) : ‖p‖ ≤ r⁻¹ := by
  by_cases hp0 : p = 0
  · simp [hp0, hr.le]
  have hq : (r/‖p‖) • p ∈ K := hball (by simpa using (norm_smul_normalized hp0 hr.le).le)
  have hh := hp _ hq
  rw [normalized_inner hp0] at hh
  have hh' : ‖p‖ ≤ r⁻¹ * (1 : ℝ) := (le_inv_mul_iff₀ hr).mpr hh
  simpa only [mul_one] using hh'

theorem isCompact_polar [FiniteDimensional ℝ E] {K : Set E} (h0 : (0 : E) ∈ interior K) : IsCompact (polar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hr2 : 0 < r/2 := half_pos hr
  have hclosed : Metric.closedBall (0 : E) (r/2) ⊆ K := by
    intro x hx
    apply hball
    exact (Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hr)
  apply (isCompact_closedBall (0 : E) ((r/2)⁻¹)).of_isClosed_subset (isClosed_polar K)
  intro p hp
  simpa using norm_le_of_mem_polar hr2 hclosed hp

theorem mem_polar_polar_iff [FiniteDimensional ℝ E] {K : Set E} (hK : Convex ℝ K) (hc : IsClosed K)
    (h0 : (0 : E) ∈ K) (x : E) : x ∈ polar (polar K) ↔ x ∈ K := by
  constructor
  · intro hx
    by_contra hn
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hK hc hn
    have hu : 0 < u := by simpa using hfu 0 h0
    let v : E := (InnerProductSpace.toDual ℝ E).symm f
    have hv (y : E) : inner (𝕜 := ℝ) y v = f y := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hp : u⁻¹ • v ∈ polar K := by
      intro y hy
      rw [real_inner_smul_right, hv, ← div_eq_inv_mul]
      exact (div_le_one hu).mpr (hfu y hy).le
    have hh := hx _ hp
    rw [real_inner_smul_left, real_inner_comm, hv, ← div_eq_inv_mul] at hh
    exact (not_le_of_gt hux) ((div_le_one hu).mp hh)
  · intro hx p hp
    rw [real_inner_comm]
    exact hp x hx

theorem closedBall_subset_polar_of_norm_bound {K : Set E} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ B) : Metric.closedBall (0 : E) ((B+1)⁻¹) ⊆ polar K := by
  intro p hp x hx
  have hp' : ‖p‖ ≤ (B+1)⁻¹ := by simpa using hp
  have hi := real_inner_le_norm x p
  have hm := mul_le_mul (hbound x hx) hp' (norm_nonneg _) hB
  have hr : 0 < B+1 := by linarith
  have hb : B*(B+1)⁻¹ ≤ 1 := (div_le_one hr).mpr (by linarith)
  exact hi.trans (hm.trans hb)

end
end ConvexPolar

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u76} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type u77}

theorem pairing_le_of_net {P : Set E} {b : κ → E} {δ M : ℝ}
    (hnet : ∀ p ∈ P, ∃ j, ‖p-b j‖ ≤ δ) {x : E}
    (hx : ∀ j, inner (𝕜 := ℝ) (b j) x ≤ M) {p : E} (hp : p ∈ P) :
    inner (𝕜 := ℝ) p x ≤ M+δ*‖x‖ := by
  obtain ⟨j, hj⟩ := hnet p hp
  have hh := real_inner_le_norm (p-b j) x
  rw [inner_sub_left] at hh
  have hm := mul_le_mul_of_nonneg_right hj (norm_nonneg x)
  linarith [hx j]

theorem net_norm_bound {P : Set E} {b : κ → E} {δ M r : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hball : Metric.closedBall (0 : E) r ⊆ P)
    (hnet : ∀ p ∈ P, ∃ j, ‖p-b j‖ ≤ δ) {x : E}
    (hx : ∀ j, inner (𝕜 := ℝ) (b j) x ≤ M) : (r-δ)*‖x‖ ≤ M := by
  by_cases hx0 : x = 0
  · simpa [hx0] using hM
  have hp : (r/‖x‖) • x ∈ P := hball (by simpa using (norm_smul_normalized hx0 hr).le)
  have hh := pairing_le_of_net hnet hx hp
  rw [normalized_inner hx0] at hh
  nlinarith

theorem finite_polar_approximation [FiniteDimensional ℝ E] {K : Set E}
    (hc : IsCompact K) (hK : Convex ℝ K) (hi : (interior K).Nonempty)
    (hs : ∀ x, x ∈ K ↔ -x ∈ K) {α : ℝ} (hα : 0 < α) :
    ∃ t : Finset E,
      Function.Injective (fun x : E => fun j : t => inner (𝕜 := ℝ) (j : E) x) ∧
      K ⊆ stripBody (fun j : t => (j : E)) ∧
      (∀ x ∈ stripBody (fun j : t => (j : E)), (1+α)⁻¹ • x ∈ K) ∧
      polar (stripBody (fun j : t => (j : E))) ⊆ polar K := by
  classical
  have h0 := zero_mem_interior_of_symmetric hK hi hs
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let r := (B+1)⁻¹
  have hr : 0 < r := inv_pos.mpr (by linarith)
  let δ := α*r/(1+α)
  have hlam : 0 < 1+α := by linarith
  have hδ : 0 < δ := div_pos (mul_pos hα hr) hlam
  have hrδ : 0 < r-δ := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hlam).mpr
    nlinarith
  have hδeq : δ = α*(r-δ) := by dsimp [δ]; field_simp; ring
  have hball : Metric.closedBall (0 : E) r ⊆ polar K :=
    closedBall_subset_polar_of_norm_bound hB.le hbound
  obtain ⟨t, htK, ht, hcover⟩ := (isCompact_polar h0).finite_cover_balls hδ
  let b : ht.toFinset → E := fun j => j
  have hb (j : ht.toFinset) : b j ∈ polar K := htK (by simpa only [b, Set.Finite.mem_toFinset] using j.2)
  have hnet (p : E) (hp : p ∈ polar K) : ∃ j : ht.toFinset, ‖p-b j‖ ≤ δ := by
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hp)
    obtain ⟨hqmem, hdist⟩ := mem_iUnion.mp hq
    refine ⟨⟨q, by simpa using hqmem⟩, ?_⟩
    simpa only [dist_eq_norm, b] using (Metric.mem_ball.mp hdist).le
  have hKK' : K ⊆ stripBody b := by
    intro x hx j
    exact polar_abs_pairing hs (hb j) hx
  have hspans : Function.Injective (fun x : E => fun j => inner (𝕜 := ℝ) (b j) x) := by
    intro x y hxy
    have hz (j) : inner (𝕜 := ℝ) (b j) (x-y) ≤ 0 := by
      rw [inner_sub_right]
      have hh : inner (𝕜 := ℝ) (b j) x = inner (𝕜 := ℝ) (b j) y := congrFun hxy j
      rw [hh, sub_self]
    have hh := net_norm_bound hr.le le_rfl hball hnet hz
    have he : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp he)
  refine ⟨ht.toFinset, hspans, hKK', ?_, polar_antitone hKK'⟩
  intro x hx
  apply (mem_polar_polar_iff hK hc.isClosed (interior_subset h0) _).mp
  have hx' (j) : inner (𝕜 := ℝ) (b j) x ≤ 1 := (le_abs_self _).trans (hx j)
  have hh := net_norm_bound hr.le (by norm_num : (0 : ℝ) ≤ 1) hball hnet hx'
  have hd : δ*‖x‖ ≤ α := by nlinarith
  intro p hp
  rw [real_inner_smul_right, ← div_eq_inv_mul]
  apply (div_le_one hlam).mpr
  have hh' := pairing_le_of_net hnet hx' hp
  linarith

end
end ConvexPolar

namespace SymmetricPolar
open Set Filter
open scoped Topology ContDiff Pointwise
noncomputable section
variable {n : ℕ}

theorem symmetric_polar_embedding {K : Set (Position n)} (hK : IsSymmetricConvexBody K)
    {c : ℝ} (hc : 0 < c) (hc4 : c < 4) :
    HasSymplecticEmbedding (capacityBall n c) (polarProduct K) := by
  obtain ⟨α, hα, hαc⟩ := exists_positive_slack hc hc4
  let lam := 1+α
  have hlam : 0 < lam := by dsimp [lam]; linarith
  rcases hK with ⟨hcompact, hconvex, hinterior, hsymm⟩
  obtain ⟨t, htinj, hKK', hK'K, hpolar⟩ :=
    ConvexPolar.finite_polar_approximation hcompact hconvex hinterior hsymm hα
  let b : t → Position n := fun j => j
  have hsubset : ConvexPolar.stripBody b ⊆ lam • K := by
    intro x hx
    refine ⟨lam⁻¹ • x, hK'K x hx, ?_⟩
    change lam • (lam⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  have hposition {q : Position n} (hq : q ∈ interior (ConvexPolar.stripBody b)) :
      lam⁻¹ • q ∈ interior K := by
    have hh := interior_mono hsubset hq
    rw [interior_smul₀ hlam.ne'] at hh
    obtain ⟨w, hw, rfl⟩ := hh
    simpa only [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul] using hw
  obtain ⟨e, he, hi, hm, hω⟩ := finite_strips_embedding b htinj (mul_pos hlam hc) hαc
  apply embedding_of_scaled_ball_map hlam (a := lam⁻¹) (b := 1) (by simp) he
    (HasSymplecticEmbedding.injOn hi) ?_ hω
  intro z hz
  obtain ⟨hq, hp⟩ := hm hz
  change lam⁻¹ • (e z).1 ∈ interior K ∧ (1 : ℝ) • (e z).2 ∈ interior (polar K)
  refine ⟨hposition hq, ?_⟩
  change (1 : ℝ) • (e z).2 ∈ interior (ConvexPolar.polar K)
  simpa only [one_smul] using interior_mono hpolar hp

end
end SymmetricPolar

end LowerBoundInline

end OAI

end

namespace OAI.SymmetricPolar
open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
noncomputable section
private def omegaB (n : ℕ) : LinearMap.BilinForm ℝ (Phase n) :=
  LinearMap.mk₂ ℝ omega0 (by intros; simp [omega0, inner_add_left, inner_add_right]; ring)
    (by intros; simp [omega0, real_inner_smul_left, real_inner_smul_right]; ring)
    (by intros; simp [omega0, inner_add_left, inner_add_right]; ring)
    (by intros; simp [omega0, real_inner_smul_left, real_inner_smul_right]; ring)

private theorem omega_det {n} (A : Phase n →L[ℝ] Phase n)
    (h : ∀ v w, omega0 (A v) (A w) = omega0 v w) : |A.det| = 1 := by
  classical
  let B := omegaB n
  have nd : B.Nondegenerate := by
    constructor <;> intro x hx <;> apply Prod.ext
    · simpa [B, omegaB, omega0] using hx (0, x.1)
    · simpa [B, omegaB, omega0] using hx (x.2, 0)
    · simpa [B, omegaB, omega0] using hx (0, x.1)
    · simpa [B, omegaB, omega0] using hx (x.2, 0)
  let b := Module.Free.chooseBasis ℝ (Phase n)
  have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp nd
  have eq : B.comp A.toLinearMap A.toLinearMap = B := by
    apply LinearMap.ext₂
    exact h
  have hm := LinearMap.BilinForm.toMatrix_comp b b B A.toLinearMap A.toLinearMap
  rw [eq] at hm
  have hh := congrArg Matrix.det hm
  simp only [Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hh
  change |LinearMap.det A.toLinearMap| = 1
  rcases mul_eq_zero.mp (show ((LinearMap.BilinForm.toMatrix b B).det) *
      ((LinearMap.det A.toLinearMap)^2 - 1) = 0 by linarith only [hh]) with h0 | hs
  · exact (hd h0).elim
  · nlinarith [sq_abs (LinearMap.det A.toLinearMap), abs_nonneg (LinearMap.det A.toLinearMap)]
private theorem embedding_volume {n : ℕ} {U V : Set (Phase n)} (hU : IsOpen U)
    (h : HasSymplecticEmbedding U V) : volume U ≤ volume V := by
  obtain ⟨e, he, hi, hm, hw⟩ := h
  have df (x) (hx : x ∈ U) := ((he.differentiableOn (by simp) x hx).differentiableAt
    (hU.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt (s := U)
  have inj : InjOn e U := fun x hx y hy hxy => congrArg Subtype.val
    (hi.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  let : (volume : Measure (Phase n)).IsAddHaarMeasure := by
    change ((volume : Measure (Position n)).prod volume).IsAddHaarMeasure
    infer_instance
  have hj := lintegral_abs_det_fderiv_eq_addHaar_image volume hU.measurableSet df inj
  have hj' := setLIntegral_congr_fun (μ := (volume : Measure (Phase n))) hU.measurableSet
    (f := fun x => ENNReal.ofReal |(fderiv ℝ e x).det|) (g := fun _ => 1)
    (fun x hx => by simp [omega_det _ (hw x hx)])
  rw [hj', setLIntegral_one] at hj
  exact hj.le.trans (measure_mono hm.image_subset)
private theorem capacity_volume {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 < c) :
    volume (capacityBall n c) = ENNReal.ofReal (c^n / (n.factorial : ℝ)) := by
  let E := WithLp 2 (Phase n)
  have hdim : Module.finrank ℝ E = 2*n := by
    rw [(WithLp.linearEquiv 2 ℝ (Phase n)).finrank_eq, Module.finrank_prod]
    simp [Position, two_mul]
  have hset : capacityBall n c = WithLp.toLp 2 ⁻¹' Metric.ball (0 : E) (Real.sqrt (c/Real.pi)) := by
    ext x
    simp only [capacityBall, mem_ofPred_eq, mem_preimage, Metric.mem_ball, dist_zero_right,
      Real.lt_sqrt (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2, lt_div_iff₀ Real.pi_pos]
    rw [mul_comm]
    rfl
  rw [hset, (WithLp.volume_preserving_toLp (Position n) (Position n)).measure_preimage
    Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    InnerProductSpace.volume_ball_of_dim_even hdim, hdim, pow_mul,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  field_simp [Real.pi_ne_zero]
theorem mahler_of_capacity_embeddings {n : ℕ} (K : Set (Position n))
    (h : ∀ c : ℝ, 0 < c → c < 4 → HasSymplecticEmbedding (capacityBall n c) (polarProduct K)) :
    (4 : ℝ≥0∞)^n / (n.factorial : ℝ≥0∞) ≤ volume K * volume (polar K) := by
  have hp : volume (polarProduct K) ≤ volume K * volume (polar K) := by
    rw [polarProduct, Measure.volume_eq_prod, Measure.prod_prod]
    exact mul_le_mul' (measure_mono interior_subset) (measure_mono interior_subset)
  have bound (c : ℝ) (hc : 0 < c) (hc' : c < 4) :=
    (embedding_volume (U := capacityBall n c) (isOpen_lt (by fun_prop) continuous_const) (h c hc hc')).trans hp
  cases n with
  | zero =>
    have hu : capacityBall 0 1 = univ := by
      ext x
      simp [capacityBall, Subsingleton.elim x 0]
    have hh := bound 1 (by norm_num) (by norm_num)
    have hvol : volume (capacityBall 0 1) = 1 := by
      rw [hu, Measure.volume_eq_prod, ← univ_prod_univ, Measure.prod_prod,
        volume_euclideanSpace_eq_dirac (Fin 0)]
      simp
    simpa only [hvol, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hh
  | succ k =>
    let n := k+1
    have hb (c : ℝ) (hc : 0 < c) (hc' : c < 4) := bound c hc hc'
    have ht : Tendsto (fun c : ℝ => ENNReal.ofReal (c^n / (n.factorial : ℝ))) (𝓝[<] 4)
        (𝓝 (ENNReal.ofReal ((4:ℝ)^n / (n.factorial : ℝ)))) :=
      (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous (fun c : ℝ => c^n / (n.factorial : ℝ)))).continuousAt.continuousWithinAt
    have hh := le_of_tendsto ht (b := volume K * volume (polar K)) (by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 4))] with c h4 h0
      rw [← capacity_volume (n := k+1) h0]
      exact hb c h0 h4)
    simpa [n, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.factorial_pos), ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4)] using hh



end
end OAI.SymmetricPolar

open Set MeasureTheory
open scoped ENNReal
namespace SelfPolarPort
open OMA.S_arxiv_2211_14630
private theorem appR {n : ℕ} (a b : Fin n → ℝ) (j : Fin n) : Fin.append a b (j.addNat n) = b j := by simpa only [Fin.natAdd_eq_addNat] using Fin.append_right a b j
noncomputable def rot (n : ℕ) : Phase n →ₗ[ℝ] Phase n where
  toFun y := Fin.append (fun i => y (Fin.natAdd n i)) (fun i => -y (Fin.castAdd n i))
  map_add' x y := by ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [appR, neg_add_rev, add_comm]
  map_smul' a y := by ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [appR]

theorem rot4 (n : ℕ) : (((rot n).comp (rot n)).comp ((rot n).comp (rot n))) = LinearMap.id := by
  ext x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [rot, appR]

theorem rot_mp (n : ℕ) : MeasurePreserving (rot n) volume volume := by
  have h := congrArg LinearMap.det (rot4 n)
  simp only [LinearMap.det_comp, LinearMap.det_id] at h
  have hn : LinearMap.det (rot n) ≠ 0 := by intro hz; simp [hz] at h
  have hab : |LinearMap.det (rot n)| = 1 := by
    have hsq : LinearMap.det (rot n) * LinearMap.det (rot n) = 1 := by rcases mul_self_eq_one_iff.mp h with h1|h1 <;> nlinarith [sq_nonneg (LinearMap.det (rot n))]
    rcases le_or_gt 0 (LinearMap.det (rot n)) with hp | hp
    · rw [abs_of_nonneg hp]; nlinarith [sq_nonneg (LinearMap.det (rot n) - 1)]
    · rw [abs_of_neg hp]; nlinarith [sq_nonneg (LinearMap.det (rot n) + 1)]
  exact ⟨(rot n).continuous_of_finiteDimensional.measurable, by rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hn, abs_inv, hab]; simp⟩

def polar {n : ℕ} (X : Set (Phase n)) := {y : Phase n | ∀ x ∈ X, (∑ i, x i * y i) ≤ 1}

theorem polClosed {n : ℕ} (X : Set (Phase n)) : IsClosed (polar X) := by
  simp only [polar, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_le (by fun_prop) continuous_const

theorem rot_pre {n : ℕ} (X : Set (Phase n)) : rot n ⁻¹' polar X = symplecticPolar X := by
  ext y; simp only [polar, symplecticPolar, mem_preimage, mem_ofPred_eq]; congr! 3
  simp [Fin.sum_univ_add, rot, appR, Finset.sum_add_distrib, sub_eq_add_neg]

theorem symmetric {n : ℕ} {X : Set (Phase n)} (hX : X = symplecticPolar X) : ∀ x ∈ X, -x ∈ X := by
  intro x hx; rw [hX]; intro y hy
  have h := (hX ▸ hy : y ∈ symplecticPolar X) x hx
  simpa [Pi.neg_apply, mul_comm, sub_eq_add_neg, add_comm] using h
theorem finish (n : ℕ) (X : Set (Phase n)) (hc : IsCompact X) (hv : Convex ℝ X)
    (hi : 0 ∈ interior X) (hX : X = symplecticPolar X)
    (mahler : ∀ K : Set (EuclideanSpace ℝ (Fin (n+n))), IsCompact K → Convex ℝ K →
      (interior K).Nonempty → (∀ x ∈ K, -x ∈ K) → (4 : ℝ≥0∞)^(n+n) / ((n+n).factorial : ℝ≥0∞) ≤
      volume K * volume {y | ∀ x ∈ K, inner ℝ x y ≤ (1 : ℝ)}) :
    (2 : ℝ≥0∞)^n / (n.factorial : ℝ≥0∞) ≤ volume X := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+n) => ℝ)
  let K := e ⁻¹' X
  have vol (T : Set (Phase n)) : volume (e ⁻¹' T) = volume T :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n+n))).measure_preimage_equiv T
  have h := mahler K (e.toHomeomorph.isCompact_preimage.mpr hc) (hv.linear_preimage e.toLinearMap)
    ⟨0, preimage_interior_subset_interior_preimage e.continuous (by simpa using hi : e 0 ∈ interior X)⟩
    (fun x hx => by simpa [K] using symmetric hX (e x) hx)
  have he : {y | ∀ x ∈ K, inner ℝ x y ≤ (1 : ℝ)} = e ⁻¹' polar X := by
    ext y; constructor
    · intro H x hx; simpa [e, PiLp.inner_apply, Real.inner_apply, mul_comm] using H (e.symm x) (by simpa [K] using hx)
    · intro H x hx; simpa [e, PiLp.inner_apply, Real.inner_apply, mul_comm] using H (e x) hx
  have hp : volume X = volume (polar X) := by
    calc
      volume X = volume (rot n ⁻¹' polar X) := congrArg volume (hX.trans (rot_pre X).symm)
      _ = _ := (rot_mp n).measure_preimage (polClosed X).measurableSet.nullMeasurableSet
  rw [he, vol (polar X), ← hp, show volume K = volume X from vol X] at h
  have H := ENNReal.toReal_mono (ENNReal.mul_ne_top hc.measure_lt_top.ne hc.measure_lt_top.ne) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_mul] at H
  have hfac : ((n+n).factorial : ℝ) ≤ (2:ℝ)^(n+n) * (n.factorial : ℝ) * n.factorial := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n n ▸ Nat.mul_le_mul_right n.factorial (Nat.mul_le_mul_right n.factorial (Nat.choose_le_two_pow (n+n) n)) : (n+n).factorial ≤ _)
  have hx := (div_le_iff₀ (by positivity)).mp H
  have hx2 := hx.trans (mul_le_mul_of_nonneg_left hfac (by positivity))
  have hp2 : (0:ℝ) < 2^(n+n) := by positivity
  have hb : (2:ℝ)^n ≤ (volume X).toReal * n.factorial := by
    have hh : ((2:ℝ)^n)^2 * (2:ℝ)^(n+n) ≤ ((volume X).toReal * n.factorial)^2 * (2:ℝ)^(n+n) := by
      calc
        _ = (4:ℝ)^(n+n) := by rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
        _ ≤ _ := hx2
        _ = _ := by ring
    have hh' := (mul_le_mul_iff_left₀ hp2).mp hh
    nlinarith [show 0 ≤ (volume X).toReal * n.factorial by positivity]
  have H2 := ENNReal.ofReal_le_ofReal ((div_le_iff₀ (by positivity)).mpr hb)
  simpa [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr n.factorial_pos), ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_toReal hc.measure_lt_top.ne] using H2
end SelfPolarPort

open OAI.SymmetricPolar in
theorem OMA.solution : type_of% @OMA.S_arxiv_2211_14630.main := by
  intro n X hc hv hi hX
  apply SelfPolarPort.finish n X hc hv hi hX
  intro K hK hV hI hs
  apply mahler_of_capacity_embeddings
  intro c hc hc4
  apply symmetric_polar_embedding (c := c) (K := K) ?_ hc hc4
  exact ⟨hK, hV, hI, fun x => ⟨hs x, fun h => by simpa using hs (-x) h⟩⟩
