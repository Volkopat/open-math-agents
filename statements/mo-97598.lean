import Mathlib

open scoped Manifold ContDiff

namespace OMA.S_mo_97598

/-- There is a closed topological manifold with no smooth manifold of
one higher dimension in its homotopy type. -/
theorem main :
    ∃ (n : ℕ) (M : Type) (topology : TopologicalSpace M),
      letI := topology
      Nonempty M ∧ T2Space M ∧ SecondCountableTopology M ∧ CompactSpace M ∧
        Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) M) ∧
        ∀ (N : Type) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
          [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) N] [IsManifold (𝓡 (n + 1)) ∞ N],
          ¬ Nonempty (ContinuousMap.HomotopyEquiv M N) := by
  sorry

end OMA.S_mo_97598
