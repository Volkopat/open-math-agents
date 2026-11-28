import Mathlib

open ContinuousAlternatingMap
open scoped BigOperators Manifold ContDiff

namespace OMA.S_mo_483874

abbrev PhaseSpace (n : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Fin n)

/-- The standard symplectic form on the position and momentum coordinates. -/
noncomputable def standard {n : ℕ} (v w : PhaseSpace n) : ℝ :=
  ∑ i : Fin n, (v (Sum.inl i) * w (Sum.inr i) - v (Sum.inr i) * w (Sum.inl i))

/-- A symplectic form agreeing with the standard form outside a compact set
is symplectomorphic to the standard form in real dimension at least six. -/
theorem main :
    ∀ (n : ℕ), 3 ≤ n →
      ∀ form : PhaseSpace n → PhaseSpace n [⋀^Fin 2]→L[ℝ] ℝ,
        ContDiff ℝ ∞ form →
        (∀ x, extDeriv form x = 0) →
        (∀ x v, (∀ w, form x ![v, w] = 0) → v = 0) →
        (∃ K : Set (PhaseSpace n), IsCompact K ∧
          ∀ x ∉ K, ∀ v w, form x ![v, w] = standard v w) →
        ∃ e : Diffeomorph (𝓘(ℝ, PhaseSpace n)) (𝓘(ℝ, PhaseSpace n))
            (PhaseSpace n) (PhaseSpace n) ∞,
          ∀ x v w, form x ![v, w] =
            standard (fderiv ℝ (fun z => e z) x v) (fderiv ℝ (fun z => e z) x w) := by
  sorry

end OMA.S_mo_483874
