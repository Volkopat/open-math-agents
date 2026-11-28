import Mathlib

namespace OMA.S_mo_45714

/-- Can a Hausdorff abelian topological group be isomorphic to its Pontryagin
bidual while the canonical evaluation fails to give a topological isomorphism? -/
theorem main :
    ∃ (G : Type) (group : CommGroup G) (topology : TopologicalSpace G),
      letI : CommGroup G := group
      letI : TopologicalSpace G := topology
      IsTopologicalGroup G ∧ T2Space G ∧
        Nonempty (ContinuousMulEquiv G (PontryaginDual (PontryaginDual G))) ∧
        ¬ ∃ e : ContinuousMulEquiv G (PontryaginDual (PontryaginDual G)),
          ∀ (x : G) (χ : PontryaginDual G), e x χ = χ x := by
  sorry

end OMA.S_mo_45714
