import OMAStatements.S_mo_111771
import Mathlib

-- Problem: mo-111771, is the index in Aut(G) of the stabilizer of a subgroup H bounded in
-- terms of k = |H| and l = |G : H| only?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes, trivially: the index of the stabilizer of H is the size of the orbit of H under Aut(G),
-- a set of subsets of G, so it is at most 2^|G| = 2^(k l).

open scoped Pointwise

theorem OMA.solution : type_of% @OMA.S_mo_111771.main := by
  refine ⟨fun k l => 2 ^ (k * l), ?_⟩
  intro G _ _ H k l _ _ hG
  rw [MulAction.index_stabilizer]
  have h2 : Nat.card (Set G) = 2 ^ Nat.card G := by
    classical
    let _inst : Fintype G := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_set]
  calc (MulAction.orbit (MulAut G) (H : Set G)).ncard ≤ Nat.card (Set G) :=
        Set.ncard_le_card _
    _ = 2 ^ (k * l) := by rw [h2, hG]
