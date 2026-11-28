import OMAStatements.S_oeis_a059163

open OMA.S_oeis_a059163

theorem OMA.solution : type_of% @OMA.S_oeis_a059163.main := by
  intro n
  obtain ⟨h, hh⟩ : ∃ h, ruler (n / 3 + 1) = h + 1 := ⟨ruler (n / 3 + 1) - 1, by unfold ruler; omega⟩
  unfold a A059129 element' element phrase
  rw [hh]
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with e | e | e <;>
    simp [e, pow_succ] <;> ring
