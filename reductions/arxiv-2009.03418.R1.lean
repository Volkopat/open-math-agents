import OMAStatements.S_arxiv_2009_03418

/-! Hill crossing formula: split attainment from the universal lower bound.
Interfaces adapted from OpenAI, openai/math, lean/OAI/Combinatorics/CompleteCrossing/Main.lean,
revision 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
namespace OMA.R_arxiv_2009_03418_R1
open OMA.S_arxiv_2009_03418

def H1 : Prop := ∀ n : ℕ, 3 ≤ n → ∃ D : AdmissibleDrawing (completeGraph n), crossingCount D = hill n

def H2 : Prop := ∀ n : ℕ, 3 ≤ n → ∀ D : AdmissibleDrawing (completeGraph n), hill n ≤ crossingCount D

lemma small_graph (n : ℕ) (hn : n < 3) : ordinaryCrossingNumber (completeGraph n) = hill n := by
  have he : Subsingleton (CompleteEdge n) := by
    constructor
    intro a b
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> have ha := a.property <;> have hb := b.property <;> have ha1 := a.val.1.isLt <;> have ha2 := a.val.2.isLt <;> have hb1 := b.val.1.isLt <;> have hb2 := b.val.2.isLt <;> change a.val.1.val < a.val.2.val at ha <;> change b.val.1.val < b.val.2.val at hb <;> omega
  have hc (D : AdmissibleDrawing (completeGraph n)) : crossingCount D = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨e,f,h,_,_⟩ := D.crossings_finite.mem_toFinset.mp hp
    exact h (he.elim e f)
  have hhill : hill n = 0 := by simp [hill, show n - 3 = 0 by omega]
  rw [hhill, ordinaryCrossingNumber]
  by_cases h : Nonempty (AdmissibleDrawing (completeGraph n))
  · exact Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨h.some, hc h.some⟩)
  · have hr : Set.range (@crossingCount _ _ (completeGraph n)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨d, _⟩
      exact h ⟨d⟩
    simp [hr]

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2009_03418.main := by
  intro upper lower n
  by_cases hn : 3 ≤ n
  · obtain ⟨D, hD⟩ := upper n hn
    unfold ordinaryCrossingNumber
    apply Nat.le_antisymm
    · exact Nat.sInf_le ⟨D, hD⟩
    · exact le_csInf ⟨_, ⟨D, rfl⟩⟩ (by rintro _ ⟨d, rfl⟩; exact lower n hn d)
  · exact small_graph n (by omega)

end OMA.R_arxiv_2009_03418_R1
