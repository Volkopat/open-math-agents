import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R3
import Mathlib
/-!
# Loop obstructions for the surface-classification polygons

On an orientable handle, a real-valued boundary height increases along the
first edge and decreases along its paired edge. Its reduction modulo one
descends to the quotient. A simply connected quotient would lift the descended
map, forcing the original heights at identified vertices to agree. The same
argument uses two free boundary arcs in the genus-zero case.

For a crosscap the boundary lifts to a path from a quaternion to its negative.
The quotient by the sign subgroup identifies the two lifts, and the equatorial
loop fills through a third quaternion coordinate. This detects the projective
plane as well as higher nonorientable genera.

Credit: @deepqntm. The polygon definitions below are from Lean Eval, via the
Apache-2.0 ClassificationOfSurfaces project at e3c7230fe78d7b056a415d9ecae6f77887046b32.
-/
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/


/-
DO NOT EDIT OR MODIFY

This is the problem definition vendored from
https://github.com/leanprover/lean-eval
with the sparse checkout
generated/topological_classification_of_surfaces


The final submitted solution will live at
https://github.com/leanprover/lean-eval
which is a pristine verbatim clone of
leanprover/lean-eval/generated/topological_classification_of_surfaces

-/

/-
Benchmark statements for topological classification of compact connected surfaces with boundary.

The representative surface in each homeomorphism class is obtained by
gluing certain arcs in the boundary of the unit disc.

Reference: Jean Gallier & Dianna Xu, *A Guide to the Classification Theorem for Compact Surfaces*,
Definition 6.5, Lemma 6.1, Theorem 6.1.
https://www.cis.upenn.edu/~jean/surfclassif-root.pdf
-/

namespace Complex

/-- The closed unit disc in the complex plane. -/
abbrev ClosedUnitDisc : Type := Metric.closedBall (0 : ℂ) 1

/-- The boundary point exp(2πir) on the boundary of the closed unit disc in the complex plane. -/
noncomputable def ClosedUnitDisc.bdyPtOfReal (r : ℝ) : ClosedUnitDisc :=
  ⟨r.fourierChar, r.fourierChar.2.le⟩

end Complex

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex Set

/-- The representative orientable surface homeomorphic to a closed orientable genus `p`
surface with `n` discs removed, obtained by identifying the boundary of a disc in the pattern
`a₁b₁a₁⁻¹b₁⁻¹⋯aₚbₚaₚ⁻¹bₚ⁻¹c₁h₁c₁⁻¹⋯cₙhₙcₙ⁻¹`. -/
inductive OrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 3 - x) / (4 * p + 3 * n))
  | b (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + 1 + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 4 - x) / (4 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : OrientableRel p n
      (.bdyPtOfReal <| - (3 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| - (3 * i + 3 - x) / (4 * p + 3 * n))

/-- The representative non-orientable surface homeomorphic to a direct sum of `p` projective
planes with `n` discs removed, obtained by identifying the boundary of a disc in the pattern
`a₁a₁⋯aₚaₚc₁h₁c₁⁻¹⋯cₙhₙcₙ⁻¹`. -/
inductive NonOrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : NonOrientableRel p n
      (.bdyPtOfReal <| (2 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| (2 * i + 1 + x) / (2 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : NonOrientableRel p n
      (.bdyPtOfReal <| -(3 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| -(3 * i + 3 - x) / (2 * p + 3 * n))



end LeanEval.Topology.ClassificationOfSurfaces

noncomputable section
open Topology Set
open Complex LeanEval.Topology.ClassificationOfSurfaces

namespace OMA.SurfacePolygons

/-- Uniqueness of lifts on the disc forces a lift to respect every edge pairing
if the polygon quotient is simply connected. -/
theorem respecting_edges_of_simplyConnected {D E B : Type*}
    [TopologicalSpace D] [PreconnectedSpace D] [TopologicalSpace E] [TopologicalSpace B]
    (r : D → D → Prop) [SimplyConnectedSpace (Quot r)] [LocallyPathConnectedSpace (Quot r)]
    {p : E → B} (hp : IsCoveringMap p) (f : C(D, E))
    (compatible : ∀ x y, r x y → p (f x) = p (f y)) {x y : D} (hxy : r x y) :
    f x = f y := by
  let g : C(Quot r, B) := ⟨Quot.lift (p ∘ f) compatible,
    continuous_quot_lift _ (hp.continuous.comp f.continuous)⟩
  obtain ⟨F, ⟨hbase, hcomp⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts g (Quot.mk r x) (f x) rfl
  have heq : F ∘ Quot.mk r = ⇑f :=
    hp.eq_of_comp_eq (F.continuous.comp continuous_quot_mk) f.continuous
      (funext fun a ↦ congrFun hcomp (Quot.mk r a)) x hbase
  calc
    f x = F (Quot.mk r x) := (congrFun heq x).symm
    _ = F (Quot.mk r y) := congrArg F (Quot.sound hxy)
    _ = f y := congrFun heq y

private def circleInDisc (z : Circle) : ClosedUnitDisc := ⟨z, z.2.le⟩

private lemma circleInDisc_closed : IsClosedEmbedding circleInDisc :=
  Continuous.isClosedEmbedding (continuous_subtype_val.subtype_mk _) (fun _ _ h ↦
    Circle.coe_injective (congrArg (fun z : ClosedUnitDisc ↦ (z : ℂ)) h))

private lemma circleCoord (r : ℝ) :
    (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm (Real.fourierChar r) =
      (r : AddCircle (1 : ℝ)) := by
  apply (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).injective
  rw [Homeomorph.apply_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  simp [Real.fourierChar_apply']

/-- Extend a real-valued boundary profile, given in turns, to the closed disc. -/
private theorem exists_disc_profile {T : Type} [TopologicalSpace T] [TietzeExtension.{0} T]
    (w : ℝ → T) (hw : Continuous w) (h01 : w 0 = w 1) :
    ∃ f : C(ClosedUnitDisc, T), ∀ r ∈ Icc (0 : ℝ) 1,
      f (.bdyPtOfReal r) = w r := by
  let g : C(Circle, T) :=
    ⟨AddCircle.liftIco 1 0 w ∘ (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm,
      (AddCircle.liftIco_zero_continuous h01 hw.continuousOn).comp (Homeomorph.continuous _)⟩
  obtain ⟨f, hf⟩ := g.exists_extension' circleInDisc_closed
  refine ⟨f, fun r hr ↦ ?_⟩
  change (f ∘ circleInDisc) (Real.fourierChar r) = w r
  rw [hf]
  change AddCircle.liftIco 1 0 w _ = _
  rw [circleCoord]
  rcases hr.2.lt_or_eq with h | rfl
  · exact AddCircle.liftIco_zero_coe_apply ⟨hr.1, h⟩
  · rw [AddCircle.coe_period]
    simpa using (AddCircle.liftIco_zero_coe_apply (f := w)
      (show (0 : ℝ) ∈ Ico 0 1 by norm_num)).trans h01

private lemma bdy_add_one (r : ℝ) : ClosedUnitDisc.bdyPtOfReal (r + 1) = .bdyPtOfReal r := by
  apply congrArg circleInDisc
  apply (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.injective
  rw [circleCoord, circleCoord, AddCircle.coe_add_period]

end OMA.SurfacePolygons
namespace OMA.SurfacePolygons

private theorem polygon_profile {T : Type} [TopologicalSpace T] [TietzeExtension.{0} T]
    (d : ℝ) (hd : 0 < d) (w : ℝ → T) (hw : Continuous w) (hend : w 0 = w d) :
    ∃ f : C(ClosedUnitDisc, T),
      (∀ s, 0 ≤ s → s ≤ d → f (.bdyPtOfReal (s / d)) = w s) ∧
      (∀ s, 0 ≤ s → s ≤ d → f (.bdyPtOfReal (-s / d)) = w (d - s)) := by
  obtain ⟨f, hf⟩ := exists_disc_profile (fun r ↦ w (r * d))
    (hw.comp (continuous_id.mul_const d)) (by simpa using hend)
  have pos (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ d) :
      f (.bdyPtOfReal (s / d)) = w s := by
    simpa [div_mul_cancel₀ _ hd.ne'] using hf (s / d)
      ⟨div_nonneg hs hd.le, (div_le_one hd).mpr hs'⟩
  refine ⟨f, pos, fun s hs hs' ↦ ?_⟩
  rw [← bdy_add_one, show -s / d + 1 = (d - s) / d by field_simp; ring]
  exact pos _ (sub_nonneg.mpr hs') (sub_le_self _ hs)

private def handleHeight (s : ℝ) : ℝ := max 0 (min 1 (min s (3 - s)))

private lemma handleHeight_low {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    handleHeight s = s := by
  simp [handleHeight, min_eq_left (show s ≤ 3 - s by linarith), min_eq_right hs',
    max_eq_right hs]

private lemma handleHeight_top {s : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 2) :
    handleHeight s = 1 := by
  simp [handleHeight, min_eq_left (le_min hs (by linarith : 1 ≤ 3 - s))]

private lemma handleHeight_down {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) :
    handleHeight s = 3 - s := by
  simp [handleHeight, min_eq_right (show 3 - s ≤ s by linarith),
    min_eq_right (show 3 - s ≤ 1 by linarith), max_eq_right (sub_nonneg.mpr hs')]

private lemma handleHeight_zero {s : ℝ} (hs : 3 ≤ s) : handleHeight s = 0 := by
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (sub_nonpos.mpr hs)))

/-- Every positive-genus orientable normal form, with any number of boundary
components, has a nontrivial loop. Coordinates match the Lean Eval polygon. -/
theorem not_simplyConnected_orientable (p n : ℕ) (hp : 1 ≤ p) :
    ¬ SimplyConnectedSpace (Quot (OrientableRel p n)) := by
  intro hsc
  let : ContractibleSpace ClosedUnitDisc := Metric.contractibleSpace_closedBall (by norm_num)
  let : LocallyPathConnectedSpace ClosedUnitDisc := (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn' : 0 ≤ (n : ℝ) := by positivity
  let d : ℝ := 4 * p + 3 * n
  have hd : 4 ≤ d := by dsimp [d]; linarith
  obtain ⟨f, fpos, fneg⟩ := polygon_profile d (by linarith) handleHeight
    (by unfold handleHeight; fun_prop) (by rw [handleHeight_low (by norm_num) (by norm_num),
      handleHeight_zero (by linarith)])
  have compat (u v : ClosedUnitDisc) (huv : OrientableRel p n u v) :
      (f u : AddCircle (1 : ℝ)) = (f v : AddCircle (1 : ℝ)) := by
    cases huv with
    | a x i =>
      have hi : (i.val : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
      have hi' : (0 : ℝ) ≤ i.val := by positivity
      obtain ⟨hx, hx'⟩ := x.property
      rw [fpos _ (by positivity) (by dsimp [d]; linarith),
          fpos _ (by linarith) (by dsimp [d]; linarith)]
      by_cases h : i.val = 0
      · simp only [h, Nat.cast_zero, mul_zero, zero_add]
        rw [handleHeight_low hx hx', handleHeight_down (by linarith) (by linarith)]
        congr 1
        ring
      · have hi1 : (1 : ℝ) ≤ i.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
        rw [handleHeight_zero (by linarith), handleHeight_zero (by linarith)]
    | b x i =>
      have hi : (i.val : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
      have hi' : (0 : ℝ) ≤ i.val := by positivity
      obtain ⟨hx, hx'⟩ := x.property
      rw [fpos _ (by positivity) (by dsimp [d]; linarith),
          fpos _ (by linarith) (by dsimp [d]; linarith)]
      by_cases h : i.val = 0
      · simp only [h, Nat.cast_zero, mul_zero, zero_add]
        rw [handleHeight_top (by linarith) (by linarith), handleHeight_zero (by linarith)]
        simp
      · have hi1 : (1 : ℝ) ≤ i.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
        rw [handleHeight_zero (by linarith), handleHeight_zero (by linarith)]
    | c x i =>
      have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      have hi' : (0 : ℝ) ≤ i.val := by positivity
      obtain ⟨hx, hx'⟩ := x.property
      rw [fneg _ (by positivity) (by dsimp [d]; linarith),
          fneg _ (by linarith) (by dsimp [d]; linarith),
          handleHeight_zero (by dsimp [d]; linarith), handleHeight_zero (by dsimp [d]; linarith)]
  let i : Fin p := ⟨0, by omega⟩
  have he := respecting_edges_of_simplyConnected _ (AddCircle.isCoveringMap_coe (1 : ℝ))
    f compat (OrientableRel.b (p := p) (n := n) 0 i)
  simp [i] at he
  change f (.bdyPtOfReal d⁻¹) = f (.bdyPtOfReal (4 / d)) at he
  rw [← one_div d, fpos _ (by norm_num) (by linarith), fpos _ (by norm_num) hd,
    handleHeight_top (by norm_num) (by norm_num), handleHeight_zero (by norm_num)] at he
  norm_num at he

end OMA.SurfacePolygons
namespace OMA.SurfacePolygons

open scoped Quaternion

/-- The double covering used to detect a crosscap. Its total space is the
group of nonzero quaternions, and its two sheets differ by sign. -/
private def signs : Subgroup ℍˣ where
  carrier := {u | u = 1 ∨ u = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by rintro x (rfl | rfl) <;> simp

private lemma signs_discrete : IsDiscrete (signs : Set ℍˣ) := by
  have h : (signs : Set ℍˣ) = {1, -1} := by ext u; rfl
  rw [h]
  exact (Set.toFinite _).isDiscrete

private lemma same_coset_neg (u : ℍˣ) :
    QuotientGroup.mk (s := signs) u = QuotientGroup.mk (s := signs) (-u) := by
  apply QuotientGroup.eq.mpr
  exact Or.inr (by simp)

private def fillQuat (v : ℝ × ℝ) : ℍ := ⟨v.1, v.2, 1 - v.1 ^ 2 - v.2 ^ 2, 0⟩

private lemma fillQuat_ne (v : ℝ × ℝ) : fillQuat v ≠ 0 := by
  intro h
  have hx : v.1 = 0 := congrArg QuaternionAlgebra.re h
  have hy : v.2 = 0 := congrArg QuaternionAlgebra.imI h
  have hz : 1 - v.1 ^ 2 - v.2 ^ 2 = 0 := congrArg QuaternionAlgebra.imJ h
  simp [hx, hy] at hz

private lemma fillQuat_continuous : Continuous fillQuat := by
  change Continuous (fun v : ℝ × ℝ ↦ Quaternion.linearIsometryEquivTuple.symm
    (WithLp.toLp 2 ![v.1, v.2, 1 - v.1 ^ 2 - v.2 ^ 2, 0]))
  apply Quaternion.linearIsometryEquivTuple.symm.continuous.comp
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

private def fillUnit : C(ℝ × ℝ, ℍˣ) :=
  ⟨fun v ↦ Units.mk0 (fillQuat v) (fillQuat_ne v), Units.continuous_iff.mpr
    ⟨fillQuat_continuous, fillQuat_continuous.inv₀ fillQuat_ne⟩⟩

private def equator (t : ℝ) : ℝ × ℝ := (Real.cos (t * Real.pi), Real.sin (t * Real.pi))

private lemma fillUnit_equator (t : ℝ) :
    (fillUnit (equator t) : ℍ) =
      ⟨Real.cos (t * Real.pi), Real.sin (t * Real.pi), 0, 0⟩ := by
  change (⟨_, _, 1 - Real.cos (t * Real.pi) ^ 2 - Real.sin (t * Real.pi) ^ 2, 0⟩ : ℍ) = _
  rw [show 1 - Real.cos (t * Real.pi) ^ 2 - Real.sin (t * Real.pi) ^ 2 = 0 by
    linarith [Real.sin_sq_add_cos_sq (t * Real.pi)]]
  rfl

private lemma fillUnit_step (t : ℝ) :
    fillUnit (equator (1 + t)) = -fillUnit (equator t) := by
  apply Units.ext
  rw [Units.val_neg, fillUnit_equator, fillUnit_equator,
    show (1 + t) * Real.pi = t * Real.pi + Real.pi by ring,
    Real.cos_add_pi, Real.sin_add_pi]
  change (⟨_, _, 0, 0⟩ : ℍ) = ⟨_, _, -(0 : ℝ), -(0 : ℝ)⟩
  rw [neg_zero]

end OMA.SurfacePolygons
namespace OMA.SurfacePolygons
open scoped Quaternion

/-- Every nonorientable normal form of positive genus fails simple connectedness,
including the projective plane, whose fundamental group has no integral character. -/
theorem not_simplyConnected_nonorientable (p n : ℕ) (hp : 1 ≤ p) :
    ¬ SimplyConnectedSpace (Quot (NonOrientableRel p n)) := by
  intro hsc
  let : ContractibleSpace ClosedUnitDisc := Metric.contractibleSpace_closedBall (by norm_num)
  let : LocallyPathConnectedSpace ClosedUnitDisc := (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn' : 0 ≤ (n : ℝ) := by positivity
  let d : ℝ := 2 * p + 3 * n
  have hd : 2 ≤ d := by dsimp [d]; linarith
  let w (s : ℝ) := equator (min s 2)
  have h02 : w 0 = w d := by
    simp [w, equator, min_eq_right hd]
  obtain ⟨f, fpos, fneg⟩ := polygon_profile d (by linarith) w (by dsimp [w, equator]; fun_prop) h02
  let proj : ℍˣ → ℍˣ ⧸ signs := QuotientGroup.mk
  have hproj : IsCoveringMap proj := (signs.isQuotientCoveringMap signs_discrete).isCoveringMap
  have compat (u v : ClosedUnitDisc) (huv : NonOrientableRel p n u v) :
      proj ((fillUnit.comp f) u) = proj ((fillUnit.comp f) v) := by
    simp only [ContinuousMap.comp_apply]
    cases huv with
    | a x i =>
      have hi : (i.val : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
      have hi' : (0 : ℝ) ≤ i.val := by positivity
      obtain ⟨hx, hx'⟩ := x.property
      rw [fpos _ (by positivity) (by dsimp [d]; linarith),
          fpos _ (by positivity) (by dsimp [d]; linarith)]
      by_cases h : i.val = 0
      · simp only [h, Nat.cast_zero, mul_zero, zero_add, w, min_eq_left (by linarith : (x : ℝ) ≤ 2),
          min_eq_left (by linarith : 1 + (x : ℝ) ≤ 2)]
        rw [fillUnit_step]
        exact same_coset_neg _
      · have hi1 : (1 : ℝ) ≤ i.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
        simp only [w, min_eq_right (by linarith : 2 ≤ 2 * (i.val : ℝ) + x),
          min_eq_right (by linarith : 2 ≤ 2 * (i.val : ℝ) + 1 + x)]
    | c x i =>
      have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      have hi' : (0 : ℝ) ≤ i.val := by positivity
      obtain ⟨hx, hx'⟩ := x.property
      rw [fneg _ (by positivity) (by dsimp [d]; linarith),
          fneg _ (by linarith) (by dsimp [d]; linarith)]
      simp only [w, min_eq_right (by dsimp [d]; linarith : 2 ≤ d - (3 * (i.val : ℝ) + x)),
        min_eq_right (by dsimp [d]; linarith : 2 ≤ d - (3 * (i.val : ℝ) + 3 - x))]
  let i : Fin p := ⟨0, by omega⟩
  have he := respecting_edges_of_simplyConnected _ hproj (fillUnit.comp f) compat
    (NonOrientableRel.a (p := p) (n := n) 0 i)
  simp [i] at he
  have h0 := fpos 0 (by norm_num) (by linarith)
  have h1 := fpos 1 (by norm_num) (by linarith)
  simp only [zero_div, one_div] at h0 h1
  rw [h0, h1] at he
  have hre := congrArg (fun u : ℍˣ ↦ (u : ℍ).re) he
  simp [w, fillUnit, fillQuat, equator] at hre
  change (1 : ℝ) = -1 at hre
  norm_num at hre

end OMA.SurfacePolygons
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R3.H2 := by
  let D := Metric.closedBall (0 : ℂ) 1
  let b (t : ℝ) : D := ⟨t.fourierChar, t.fourierChar.2.le⟩
  let R (o : Bool) (p : ℕ) (a c : D) :=
    ∃ (i : Fin p) (t : Set.Icc (0 : ℝ) 1), if o then
      (a = b ((4 * i.val + t.val) / (4 * p)) ∧ c = b ((4 * i.val + 3 - t.val) / (4 * p))) ∨
      (a = b ((4 * i.val + 1 + t.val) / (4 * p)) ∧ c = b ((4 * i.val + 4 - t.val) / (4 * p)))
    else a = b ((2 * i.val + t.val) / (2 * p)) ∧ c = b ((2 * i.val + 1 + t.val) / (2 * p))
  change ∀ o p, 0 < p → ¬ SimplyConnectedSpace (Quot (R o p))
  intro o p hp hsc
  cases o with
  | true =>
    apply OMA.SurfacePolygons.not_simplyConnected_orientable p 0 hp
    have e : Quot (R true p) ≃ₜ Quot (OrientableRel p 0) := by
      apply Homeomorph.Quot.congrRight
      intro u v
      constructor
      · rintro ⟨i, t, h⟩
        rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · simpa only [b, Complex.ClosedUnitDisc.bdyPtOfReal, Nat.cast_zero, mul_zero, add_zero] using (OrientableRel.a (n := 0) t i)
        · simpa only [b, Complex.ClosedUnitDisc.bdyPtOfReal, Nat.cast_zero, mul_zero, add_zero] using (OrientableRel.b (n := 0) t i)
      · intro h
        cases h with
        | a t i => exact ⟨i, t, Or.inl (by simp [b, Complex.ClosedUnitDisc.bdyPtOfReal])⟩
        | b t i => exact ⟨i, t, Or.inr (by simp [b, Complex.ClosedUnitDisc.bdyPtOfReal])⟩
        | c t i => exact Fin.elim0 i
    exact e.symm.toHomotopyEquiv.simplyConnectedSpace
  | false =>
    apply OMA.SurfacePolygons.not_simplyConnected_nonorientable p 0 hp
    have e : Quot (R false p) ≃ₜ Quot (NonOrientableRel p 0) := by
      apply Homeomorph.Quot.congrRight
      intro u v
      constructor
      · rintro ⟨i, t, hu, hv⟩
        subst u v
        simpa only [b, Complex.ClosedUnitDisc.bdyPtOfReal, Nat.cast_zero, mul_zero, add_zero] using (NonOrientableRel.a (n := 0) t i)
      · intro h
        cases h with
        | a t i =>
          refine ⟨i, t, ?_⟩
          simp [b, Complex.ClosedUnitDisc.bdyPtOfReal]
        | c t i => exact Fin.elim0 i
    exact e.symm.toHomotopyEquiv.simplyConnectedSpace
