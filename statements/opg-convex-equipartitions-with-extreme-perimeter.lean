import Mathlib

namespace OMA.S_opg_convex_equipartitions_with_extreme_perimeter

open Set MeasureTheory
open scoped BigOperators

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Three closed convex pieces with disjoint interiors and equal planar area. -/
def Equipartition (C : Set Plane) (pieces : Fin 3 → Set Plane) : Prop :=
  (⋃ i, pieces i) = C ∧
    (∀ i, IsCompact (pieces i) ∧ Convex ℝ (pieces i) ∧
      volume (pieces i) = volume C / 3) ∧
    Pairwise (fun i j => Disjoint (interior (pieces i)) (interior (pieces j)))

/-- The given segments are precisely the interfaces away from the outer boundary. -/
def Cuts {m : ℕ} (C : Set Plane) (p : Plane) (q : Fin m → Plane)
    (pieces : Fin 3 → Set Plane) : Prop :=
  Function.Injective q ∧
    (∀ i, q i ∈ frontier C ∧ q i ≠ p ∧ openSegment ℝ p (q i) ⊆ interior C) ∧
    interior C ∩ (⋃ i, frontier (pieces i)) =
      interior C ∩ (⋃ i, segment ℝ p (q i))

/-- The sum of the Euclidean lengths of the three piece boundaries. -/
noncomputable def perimeterSum (pieces : Fin 3 → Set Plane) : ENNReal :=
  ∑ i, Measure.hausdorffMeasure 1 (frontier (pieces i))

/-- Conjecture 1a of Nandakumar on convex equipartitions with extreme perimeter. -/
theorem main :
    ∀ (C : Set Plane), IsCompact C → Convex ℝ C →
      ∀ p ∈ interior C, ∀ (q : Fin 3 → Plane) (pieces : Fin 3 → Set Plane),
        Equipartition C pieces → Cuts C p q pieces →
          ∃ (i : Fin 3) (r : Fin 2 → Plane) (newPieces : Fin 3 → Set Plane),
            Equipartition C newPieces ∧ Cuts C (q i) r newPieces ∧
              perimeterSum pieces < perimeterSum newPieces := by
  sorry

end OMA.S_opg_convex_equipartitions_with_extreme_perimeter
