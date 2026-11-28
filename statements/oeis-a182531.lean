import Mathlib

/-!
# OEIS A182531: extremal edge counts for the paw

Source: https://oeis.org/A182531

The paw is the triangle on vertices 0, 1, 2 with an additional edge from 0 to 3.
The sequence counts the largest number of edges in an n-vertex simple graph
without the paw as a subgraph. Other edges between the four vertices of a copy
are permitted, as in Mathlib's `SimpleGraph.extremalNumber`.

Colin Barker conjectured the formula for n > 3, and Falk Hüffner proved it in
the OEIS comments. The exceptional case n = 3 has three edges.
-/

namespace OMA.S_oeis_a182531

/-- The non-induced subgraph forbidden in A182531. -/
def paw : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ ((i.val < 3 ∧ j.val < 3) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0))
  symm := by
    constructor
    intro i j h
    rcases h with ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr (Or.inr h.symm)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl h.symm)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem main : ∀ n : ℕ, 1 ≤ n →
    SimpleGraph.extremalNumber n paw = if n = 3 then 3 else n ^ 2 / 4 := by
  sorry

end OMA.S_oeis_a182531
