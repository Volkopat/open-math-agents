import Mathlib

/-!
# Smooth 4-dimensional Poincare conjecture

Source: https://www.openproblemgarden.org/op/smooth_4_dimensional_poincare_conjecture
Credit: @Mapika

Conjecture. If a 4-manifold has the homotopy type of the 4-sphere $S^4$, is it diffeomorphic
to $S^4$?

By Freedman such a manifold is homeomorphic to $S^4$; the smooth question is whether $S^4$
carries an exotic smooth structure. It is the only open case of the generalized Poincaré
conjectures.

We state the affirmative answer to the question.

Conventions:
* "4-manifold" is read in the smooth category, since the question asks for a diffeomorphism:
  a type `M` with a Hausdorff, second countable topology and a `C^∞` manifold structure
  modelled on `ℝ⁴` (`𝓡 4`, the model without boundary). Hausdorff and second countable are the
  standard requirements in the definition of a manifold. No compactness or boundary
  assumption is imposed, as on the source page; a manifold homotopy equivalent to `S^4` is
  automatically compact (a noncompact connected 4-manifold has vanishing `H_4`), and allowing
  a boundary would add nothing (a compact manifold with nonempty boundary is homotopy
  equivalent to its noncompact interior), so this agrees with the usual "homotopy 4-sphere"
  formulation.
* `S^4` is the unit sphere of `EuclideanSpace ℝ (Fin 5)` with Mathlib's standard (stereographic)
  smooth structure.
* "Has the homotopy type of" is a homotopy equivalence `M ≃ₕ S^4`
  (`ContinuousMap.HomotopyEquiv`); "diffeomorphic" is a `C^∞` diffeomorphism
  `Diffeomorph (𝓡 4) (𝓡 4) M S^4 ∞` with respect to the given smooth structure on `M`.

Relation to formal-conjectures: the same question is already stated upstream as
`PoincareConjecture.poincare_conjecture.variants.smooth_dimension_four : SmoothConjectureFor 4`
in `FormalConjectures/Millennium/Poincare.lean` (category research open). That statement
assumes Hausdorff but not second countable. The two agree: a Hausdorff locally Euclidean
space homotopy equivalent to `S^4` is connected with nonzero `H_4`, hence compact, hence
second countable.
-/

namespace OMA.S_opg_smooth_4_dimensional_poincare_conjecture

open Metric
open scoped Manifold ContDiff ContinuousMap

universe u

/-- Conjecture: every smooth 4-manifold homotopy equivalent to `S^4` is diffeomorphic to `S^4`. -/
theorem main :
    ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
      Nonempty (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) →
      Nonempty (Diffeomorph (𝓡 4) (𝓡 4) M (sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) ∞) := by
  sorry

end OMA.S_opg_smooth_4_dimensional_poincare_conjecture
