import OMAStatements.S_mo_462989
import Mathlib

-- Problem: mo-462989, if G \ v and G \ w are isomorphic, is there an automorphism of G that
-- switches v and w?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Let G be the graph on the integers in which the nonnegative integers form a clique and
-- the negative integers are isolated. Take v = 0 and w = -1. The map x -> x - 1 is an
-- isomorphism from G \ 0 onto G \ (-1). But 0 has a neighbour (namely 1) and -1 has none, so no
-- automorphism of G maps 0 to -1.

namespace MO462989

def G : SimpleGraph ℤ where
  Adj i j := i ≠ j ∧ 0 ≤ i ∧ 0 ≤ j
  symm := by
    constructor
    intro i j h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

theorem adj_iff (i j : ℤ) : G.Adj i j ↔ i ≠ j ∧ 0 ≤ i ∧ 0 ≤ j := Iff.rfl

theorem iso : Nonempty (G.induce {x : ℤ | x ≠ 0} ≃g G.induce {x : ℤ | x ≠ -1}) := by
  refine ⟨⟨⟨fun x => ⟨x.1 - 1, by
      have h : x.1 ≠ 0 := x.2
      show x.1 - 1 ≠ -1
      omega⟩, fun y => ⟨y.1 + 1, by
      have h : y.1 ≠ -1 := y.2
      show y.1 + 1 ≠ 0
      omega⟩, ?_, ?_⟩, ?_⟩⟩
  · intro x
    apply Subtype.ext
    show x.1 - 1 + 1 = x.1
    omega
  · intro y
    apply Subtype.ext
    show y.1 + 1 - 1 = y.1
    omega
  · intro a b
    show G.Adj (a.1 - 1) (b.1 - 1) ↔ G.Adj a.1 b.1
    have ha : a.1 ≠ 0 := a.2
    have hb : b.1 ≠ 0 := b.2
    rw [adj_iff, adj_iff]
    constructor
    · intro h
      omega
    · intro h
      omega

end MO462989

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_462989.main) := by
  intro h
  obtain ⟨σ, h0, _⟩ := h ℤ MO462989.G 0 (-1) MO462989.iso
  have h01 : MO462989.G.Adj 0 1 := by
    rw [MO462989.adj_iff]
    omega
  have h2 := σ.map_rel_iff.mpr h01
  rw [h0, MO462989.adj_iff] at h2
  omega
