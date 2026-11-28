import Mathlib

namespace OMA.S_mo_85724

/-- The order of DeMeo's seven-element lattice, with vertices numbered
from zero to six and the interior vertices labelled a, b, c, d, x in order. -/
def l7Le (i j : Fin 7) : Prop :=
  i = j ∨ i = 0 ∨ j = 6 ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ (j = 3 ∨ j = 4))

/-- DeMeo's seven-element lattice is realized as the entire interval of
subgroups between some subgroup and its ambient finite group. -/
theorem main :
    ∃ (G : Type) (group : Group G),
      letI := group
      Finite G ∧ ∃ (H : Subgroup G) (e : Fin 7 ≃ Set.Ici H),
        ∀ i j : Fin 7, l7Le i j ↔ e i ≤ e j := by
  sorry

end OMA.S_mo_85724
