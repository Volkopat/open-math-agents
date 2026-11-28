import OMAStatements.S_mo_322734
import Mathlib

-- Problem: mo-322734, can adding an edge to a digraph decrease the least number of colours of
-- a majority colouring?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes. The directed triangle 0 -> 1 -> 2 -> 0 needs 3 colours, since every vertex must differ
-- from its unique in-neighbour. After adding the edge 0 -> 2 the colouring (0, 1, 1) works:
-- vertex 2 now has two in-neighbours and may agree with one of them. One colour never works
-- when there is an edge, so the minimum drops from 3 to 2.

open OMA.S_mo_322734 in
theorem OMA.solution : type_of% @OMA.S_mo_322734.main := by
  refine ⟨3, {(0, 1), (1, 2), (2, 0)}, by decide, 0, 2, by decide, by decide, 3, 2,
    ⟨⟨by norm_num, ![0, 1, 2], ?_⟩, ?_⟩, ⟨⟨by norm_num, ![0, 1, 1], ?_⟩, ?_⟩, by norm_num⟩
  · unfold majorityColouring
    decide
  · rintro k ⟨hk, c, hc⟩
    by_contra hlt
    have hk12 : k = 1 ∨ k = 2 := by omega
    unfold majorityColouring at hc
    rcases hk12 with rfl | rfl
    · revert hc c
      decide
    · revert hc c
      decide
  · unfold majorityColouring
    decide
  · rintro k ⟨hk, c, hc⟩
    by_contra hlt
    have hk1 : k = 1 := by omega
    unfold majorityColouring at hc
    subst hk1
    revert hc c
    decide
