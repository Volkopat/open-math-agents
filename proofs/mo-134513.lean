import OMAStatements.S_mo_134513
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_134513.main) := fun h => by
  rcases h _ (SimpleGraph.starGraph (0 : Fin 4)) ⟨2, by decide⟩ with ⟨d, hd⟩ | ⟨⟨e⟩⟩
  · have := (hd 0).trans (hd 1).symm; revert this; decide
  · simpa using Fintype.card_congr e.toEquiv
