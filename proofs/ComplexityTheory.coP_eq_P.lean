import FormalConjectures.Millennium.PvsNP
open ComplexityTheory Turing
lemma OMA.compl_mem_P (L : DecisionProblem) (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨M⟩ := h
  refine ⟨{ M with
    outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
    outputsFun := fun a => ?_ }⟩
  convert M.outputsFun a using 1
  simp [Equiv.boolNot, BitstringEncoding.toEncoding]
theorem OMA.solution : type_of% @ComplexityTheory.coP_eq_P := by
  ext L
  exact ⟨fun h => compl_compl L ▸ OMA.compl_mem_P _ h, OMA.compl_mem_P L⟩
