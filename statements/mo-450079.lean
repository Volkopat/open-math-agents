import Mathlib

namespace OMA.S_mo_450079

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The real special linear group carries the topology inherited
from its four matrix entries. -/
instance : TopologicalSpace SL2 :=
  TopologicalSpace.induced (fun A : SL2 => (A : Matrix (Fin 2) (Fin 2) ℝ)) inferInstance

/-- There is a free discrete subgroup of the product of two real
special linear groups whose two projection images both fail to be free
and discrete simultaneously. -/
theorem main :
    ∃ G : Subgroup (SL2 × SL2),
      let first := G.map (MonoidHom.fst SL2 SL2)
      let second := G.map (MonoidHom.snd SL2 SL2)
      IsFreeGroup G ∧ DiscreteTopology G ∧
        ¬ (IsFreeGroup first ∧ DiscreteTopology first) ∧
        ¬ (IsFreeGroup second ∧ DiscreteTopology second) := by
  sorry

end OMA.S_mo_450079
