import Mathlib

/-!
# MO 378413: bounded open sets with the same boundary

Source: https://mathoverflow.net/questions/378413

The question asks whether two bounded open subsets of the Euclidean plane with the
same topological boundary must coincide when that boundary is locally path connected.
The source itself gives a counterexample without a hypothesis on the boundary, and
asks whether local path connectedness suffices.  Only the body of `main` is `sorry`.
-/

namespace OMA.S_mo_378413

theorem main :
    ∀ U₁ U₂ : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U₁ → IsOpen U₂ →
      Bornology.IsBounded U₁ → Bornology.IsBounded U₂ →
      frontier U₁ = frontier U₂ →
      LocallyPathConnectedSpace (frontier U₁) →
      U₁ = U₂ := by
  sorry

end OMA.S_mo_378413
