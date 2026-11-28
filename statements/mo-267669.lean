import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homotopy.Equiv

open Topology
open scoped ContinuousMap

namespace OMA.S_mo_267669

universe u

/-- A space has finite-dimensional CW type if it is homotopy equivalent to a
Hausdorff CW complex whose cells have a uniform upper dimension bound. -/
def HasFiniteDimensionalCWType (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (K : Type u) (_ : TopologicalSpace K) (_ : T2Space K)
    (_ : RelCWComplex (Set.univ : Set K) ∅),
      RelCWComplex.FiniteDimensional (Set.univ : Set K) (D := ∅) ∧ Nonempty (X ≃ₕ K)

/-- When a product has finite-dimensional CW type, a factor has that type whenever
the other factor is inhabited. -/
theorem main :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y],
      HasFiniteDimensionalCWType (X × Y) →
        (Nonempty Y → HasFiniteDimensionalCWType X) ∧
          (Nonempty X → HasFiniteDimensionalCWType Y) := by
  sorry

end OMA.S_mo_267669
