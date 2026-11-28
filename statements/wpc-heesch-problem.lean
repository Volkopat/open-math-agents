import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Sets.Closeds

namespace OMA.S_wpc_heesch_problem

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A planar figure in the sense of the Heesch problem is an embedded closed disk. -/
def IsFigure (S : Set Plane) : Prop :=
  Nonempty (↥(Metric.closedBall (0 : Plane) 1) ≃ₜ ↥S)

/-- A collection of congruent copies with pairwise disjoint interiors. -/
def IsPacking (S : Set Plane) (tiles : Set (Set Plane)) : Prop :=
  (∀ U ∈ tiles, ∃ e : Plane ≃ᵢ Plane, e '' S = U) ∧
    tiles.Pairwise (fun U V => Disjoint (interior U) (interior V))

/-- A tiling is a packing that covers the plane. -/
def TilesPlane (S : Set Plane) : Prop :=
  ∃ tiles : Set (Set Plane), IsPacking S tiles ∧ ⋃₀ tiles = Set.univ

/-- The collection of tiles in the first n layers, including layer zero. -/
def tilesThrough (layers : ℕ → Set (Set Plane)) (n : ℕ) : Set (Set Plane) :=
  ⋃ i ≤ n, layers i

/-- Each added layer meets the previous layer along boundaries and places the
previous patch entirely inside the interior of the enlarged patch. -/
def CanSurround (S : Set Plane) (n : ℕ) : Prop :=
  ∃ layers : ℕ → Set (Set Plane),
    layers 0 = {S} ∧
    (∀ i ≤ n, (layers i).Finite) ∧
    IsPacking S (tilesThrough layers n) ∧
    ∀ i < n,
      (∀ U ∈ layers (i + 1), ∃ V ∈ layers i, (frontier U ∩ frontier V).Nonempty) ∧
      ⋃₀ (tilesThrough layers i) ⊆ interior (⋃₀ (tilesThrough layers (i + 1)))

/-- The finite upper bound question for Heesch numbers of plane figures. -/
theorem main :
    ∃ bound : ℕ, ∀ S : Set Plane, IsFigure S → ¬ TilesPlane S →
      ∀ n : ℕ, CanSurround S n → n ≤ bound := by
  sorry

end OMA.S_wpc_heesch_problem
