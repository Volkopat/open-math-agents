import OMAStatements.S_oeis_a364906

open OMA.S_oeis_a364906

private lemma count : a 1547 = 1 := by
  have h : primeIndices 1547 = [4, 6, 7] := by decide +kernel
  rw [a, h, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => 1, by decide⟩, ?_⟩
  rintro ⟨c, hc⟩
  apply Subtype.ext
  change (∑ i : Fin 3, c i * ([4, 6, 7] : List ℕ).get i) = 17 at hc
  rw [Fin.sum_univ_three] at hc
  change c 0 * 4 + c 1 * 6 + c 2 * 7 = 17 at hc
  funext i
  fin_cases i <;> dsimp <;> omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a364906.main) := by
  intro h
  have hi := ((h 1547 (by decide)).mp count).2
  exact (by decide : (119 : ℕ) ≠ 221)
    (hi (by decide) (by decide) (by decide +kernel))
