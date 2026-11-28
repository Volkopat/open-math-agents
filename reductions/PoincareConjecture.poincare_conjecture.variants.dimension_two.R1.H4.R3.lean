import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Complex.Circle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! # Closed polygon normal forms for the two-dimensional Poincaré theorem

The surface classification uses half-space charts, whereas the target uses
plane charts. The chart construction below gives the former with empty
boundary in all positive dimensions. The polygon relations use the usual
four-side handle and two-side crosscap blocks, with each side parameter in
the closed unit interval.
-/
namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R3
open Set
open scoped Manifold

/-- The closed case of polygon classification, with no boundary holes. -/
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [ChartedSpace (EuclideanHalfSpace 2) M] [IsManifold (𝓡∂ 2) 0 M]
    [BoundarylessManifold (𝓡∂ 2) M],
    let disc := Metric.closedBall (0 : ℂ) 1
    let b := fun t : ℝ => (⟨t.fourierChar, t.fourierChar.2.le⟩ : disc)
    let r := fun (orient : Bool) (p : ℕ) (a c : disc) =>
      ∃ (i : Fin p) (t : Set.Icc (0:ℝ) 1),
        if orient then
          (a = b ((4*i.val+t.val)/(4*p)) ∧ c = b ((4*i.val+3-t.val)/(4*p))) ∨
          (a = b ((4*i.val+1+t.val)/(4*p)) ∧ c = b ((4*i.val+4-t.val)/(4*p)))
        else a = b ((2*i.val+t.val)/(2*p)) ∧ c = b ((2*i.val+1+t.val)/(2*p))
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
      ∃ (orient : Bool) (p : ℕ), 0 < p ∧ Nonempty (M ≃ₜ Quot (r orient p))

/-- Each positive-genus closed polygon has nontrivial fundamental group. -/
def H2 : Prop :=
    let disc := Metric.closedBall (0 : ℂ) 1
    let b := fun t : ℝ => (⟨t.fourierChar, t.fourierChar.2.le⟩ : disc)
    let r := fun (orient : Bool) (p : ℕ) (a c : disc) =>
      ∃ (i : Fin p) (t : Set.Icc (0:ℝ) 1),
        if orient then
          (a = b ((4*i.val+t.val)/(4*p)) ∧ c = b ((4*i.val+3-t.val)/(4*p))) ∨
          (a = b ((4*i.val+1+t.val)/(4*p)) ∧ c = b ((4*i.val+4-t.val)/(4*p)))
        else a = b ((2*i.val+t.val)/(2*p)) ∧ c = b ((2*i.val+1+t.val)/(2*p))
    ∀ (orient : Bool) (p : ℕ), 0 < p → ¬ SimplyConnectedSpace (Quot (r orient p))

/-- A Euclidean manifold can be regarded as a manifold with half-space charts
all of whose centers are interior. Translation moves each chart center to a
fixed interior point, so the construction needs no differentiable structure. -/
theorem exists_interior_halfspace_atlas (n : ℕ) [NeZero n] (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∃ c : ChartedSpace (EuclideanHalfSpace n) M, letI := c
      IsManifold (𝓡∂ n) 0 M ∧ BoundarylessManifold (𝓡∂ n) M := by
  let E := EuclideanSpace ℝ (Fin n)
  let H := EuclideanHalfSpace n
  let I := modelWithCornersEuclideanHalfSpace n
  let v : E := WithLp.toLp 2 (fun _ => (1 : ℝ))
  let move (c z : E) := z - c + v
  have hmove (c : E) : Continuous (move c) := (continuous_id.sub continuous_const).add continuous_const
  have inv (z : E) (hz : 0 < z 0) : I (I.symm z) = z := by
    apply I.right_inv
    exact ⟨⟨z, hz.le⟩, rfl⟩
  let e (c : E) : OpenPartialHomeomorph E H := {
    toFun := fun z => I.symm (move c z)
    invFun := fun y => I y - v + c
    source := {z | 0 < (move c z) 0}
    target := {y | 0 < (I y) 0}
    map_source' := by
      intro z hz
      change 0 < (I (I.symm (move c z))) 0
      rw [inv _ hz]
      exact hz
    map_target' := by
      intro y hy
      change 0 < (I y) 0 at hy
      change 0 < (I y - v + c - c + v) 0
      simpa only [add_sub_cancel_right, sub_add_cancel] using hy
    left_inv' := by
      intro z hz
      rw [inv _ hz]
      simp [move]
    right_inv' := by
      intro y _
      change I.symm (I y - v + c - c + v) = y
      simp only [add_sub_cancel_right, sub_add_cancel, I.left_inv]
    open_source := isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp (hmove c))
    open_target := isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp I.continuous)
    continuousOn_toFun := (I.continuous_symm.comp (hmove c)).continuousOn
    continuousOn_invFun := ((I.continuous.sub continuous_const).add continuous_const).continuousOn }
  let planeCharts : ChartedSpace H E := {
    atlas := range e
    chartAt := e
    mem_chart_source := by intro c; change 0 < (c-c+v) 0; simp [v]
    chart_mem_atlas := fun c => ⟨c,rfl⟩ }
  letI : ChartedSpace H E := planeCharts
  letI : ChartedSpace H M := ChartedSpace.comp H E M
  refine ⟨‹ChartedSpace H M›, inferInstance, ⟨fun x => ?_⟩⟩
  let z := chartAt E x x
  change I (I.symm (move z z)) ∈ interior (range I)
  have eqmove : move z z = v := by simp [move]
  rw [eqmove, inv _ (by change 0 < (1:ℝ); norm_num)]
  exact (interior_range_modelWithCornersEuclideanHalfSpace n) ▸ (by change 0 < (1:ℝ); norm_num)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1.H4 := by
  intro classify polygons M _ _ _ _ _
  obtain ⟨atlas,smooth,interior⟩ := exists_interior_halfspace_atlas 2 M
  let : ChartedSpace (EuclideanHalfSpace 2) M := atlas
  let : IsManifold (𝓡∂ 2) 0 M := smooth
  let : BoundarylessManifold (𝓡∂ 2) M := interior
  rcases classify M with sphere | ⟨orient,p,hp,⟨e⟩⟩
  · exact sphere
  · exact False.elim (polygons orient p hp e.symm.toHomotopyEquiv.simplyConnectedSpace)

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R3
