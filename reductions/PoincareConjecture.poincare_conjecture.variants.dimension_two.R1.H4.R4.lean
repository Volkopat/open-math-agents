import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
import Mathlib

/-!
# Recognizing the sphere among the normal forms for compact surfaces

The first input is the classification theorem for compact surfaces with boundary,
with the canonical polygonal identifications of the Lean Eval benchmark.
The second detects loops on handles, crosscaps, and spheres with at least two
boundary components. The third rules out a plane atlas on the single-disc model.

Polygon normal forms follow
https://github.com/mccorvie/classification-of-surfaces/blob/master/ClassificationOfSurfaces/LeanEval/ChallengeDeps.lean
and Gallier and Xu, A Guide to the Classification Theorem for Compact Surfaces.
-/

open Set Topology
namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R4

/-- Embed the plane into the open interior of the half-plane to use the classification atlas.
This chart construction follows the scout note by @ryansolves. -/
private theorem halfPlaneAtlas (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] :
    Nonempty (ChartedSpace (EuclideanHalfSpace 2) M) := by
  let c : (EuclideanSpace ℝ (Fin 2)) := WithLp.toLp 2 (fun _ : Fin 2 ↦ (1 : ℝ))
  have hc : c ∈ {x : (EuclideanSpace ℝ (Fin 2)) | 0 < x 0} := by change (0 : ℝ) < 1; norm_num
  have ho : IsOpen {x : (EuclideanSpace ℝ (Fin 2)) | 0 < x 0} := isOpen_lt continuous_const (by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho c hc
  let e := OpenPartialHomeomorph.univBall c r
  have he := e.isOpenEmbedding (OpenPartialHomeomorph.univBall_source c r)
  have hpos (x : (EuclideanSpace ℝ (Fin 2))) : 0 < e x 0 := by
    apply hball
    rw [← OpenPartialHomeomorph.univBall_target c hr]
    exact e.map_source (by simp [e, OpenPartialHomeomorph.univBall_source])
  let f (x : (EuclideanSpace ℝ (Fin 2))) : EuclideanHalfSpace 2 := ⟨e x, (hpos x).le⟩
  have hRange : range f = (Subtype.val : EuclideanHalfSpace 2 → (EuclideanSpace ℝ (Fin 2))) ⁻¹' range (e : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hf : IsOpenEmbedding f := by
    refine ⟨IsEmbedding.of_comp (he.continuous.subtype_mk _) continuous_subtype_val he.toIsEmbedding, ?_⟩
    exact hRange ▸ he.isOpen_range.preimage continuous_subtype_val
  let : ChartedSpace (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)) := hf.singletonChartedSpace
  exact ⟨ChartedSpace.comp (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)) M⟩

/-- Classification into the sphere and the orientable or nonorientable polygons. -/
def H1 : Prop :=
  let D := Metric.closedBall (0 : ℂ) 1
  let z (t : ℝ) : D := ⟨Real.fourierChar t, (Real.fourierChar t).2.le⟩
  let R (o : Bool) (p n : ℕ) (u v : D) :=
    let d : ℝ := (if o then 4 else 2) * p + 3 * n
    let edge (s t : ℝ) := u = z (s / d) ∧ v = z (t / d)
    (∃ (i : Fin p) (x : Icc (0 : ℝ) 1), if o then
        edge (4 * i + x) (4 * i + 3 - x) ∨ edge (4 * i + 1 + x) (4 * i + 4 - x)
      else edge (2 * i + x) (2 * i + 1 + x)) ∨
      ∃ (i : Fin n) (x : Icc (0 : ℝ) 1), edge (-(3 * i + x)) (-(3 * i + 3 - x))
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M],
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
    ∃ (o : Bool) (p n : ℕ), (1 ≤ p ∨ o = true ∧ 1 ≤ n) ∧ Nonempty (M ≃ₜ Quot (R o p n))

/-- Positive genus and two or more holes in a genus-zero orientable surface detect a loop. -/
def H2 : Prop :=
  let D := Metric.closedBall (0 : ℂ) 1
  let z (t : ℝ) : D := ⟨Real.fourierChar t, (Real.fourierChar t).2.le⟩
  let R (o : Bool) (p n : ℕ) (u v : D) :=
    let d : ℝ := (if o then 4 else 2) * p + 3 * n
    let edge (s t : ℝ) := u = z (s / d) ∧ v = z (t / d)
    (∃ (i : Fin p) (x : Icc (0 : ℝ) 1), if o then
        edge (4 * i + x) (4 * i + 3 - x) ∨ edge (4 * i + 1 + x) (4 * i + 4 - x)
      else edge (2 * i + x) (2 * i + 1 + x)) ∨
      ∃ (i : Fin n) (x : Icc (0 : ℝ) 1), edge (-(3 * i + x)) (-(3 * i + 3 - x))
  ∀ (o : Bool) (p n : ℕ), (1 ≤ p ∨ o = true ∧ 2 ≤ n) → ¬ SimplyConnectedSpace (Quot (R o p n))

/-- The remaining polygon, a single disk, admits no atlas modeled on the whole plane. -/
def H3 : Prop :=
  let D := Metric.closedBall (0 : ℂ) 1
  let z (t : ℝ) : D := ⟨Real.fourierChar t, (Real.fourierChar t).2.le⟩
  let R (o : Bool) (p n : ℕ) (u v : D) :=
    let d : ℝ := (if o then 4 else 2) * p + 3 * n
    let edge (s t : ℝ) := u = z (s / d) ∧ v = z (t / d)
    (∃ (i : Fin p) (x : Icc (0 : ℝ) 1), if o then
        edge (4 * i + x) (4 * i + 3 - x) ∨ edge (4 * i + 1 + x) (4 * i + 4 - x)
      else edge (2 * i + x) (2 * i + 1 + x)) ∨
      ∃ (i : Fin n) (x : Icc (0 : ℝ) 1), edge (-(3 * i + x)) (-(3 * i + 3 - x))
  ¬ Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) (Quot (R true 0 1)))

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1.H4 := by
  intro classify loops disk M _ _ _ _ _
  obtain ⟨atlas⟩ := halfPlaneAtlas M
  let : ChartedSpace (EuclideanHalfSpace 2) M := atlas
  rcases classify M with sphere | ⟨o, p, n, hpar, ⟨e⟩⟩
  · exact sphere
  · have sc := e.symm.toHomotopyEquiv.simplyConnectedSpace
    have hp : p = 0 := by
      by_contra h
      exact loops o p n (Or.inl (by omega)) sc
    subst p
    obtain ⟨rfl, hn⟩ := hpar.resolve_left (by decide)
    have hn' : n = 1 := by
      by_contra h
      exact loops true 0 n (Or.inr ⟨rfl, by omega⟩) sc
    subst n
    exact (disk ⟨e.chartedSpace (H := EuclideanSpace ℝ (Fin 2))⟩).elim

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R4
