import OMAStatements.S_oeis_a071069

open OMA.S_oeis_a071069 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071069.main) := by
  intro h
  have h23 := (h 23 (by norm_num)).1
  have h1 : a070923 13537 ≤ 63 := by
    unfold a070923
    have hmem : 63 ∈ (((Finset.range (13537 + 1)).filter
        (fun x => 13537 ^ 2 ≤ x ^ 3)).image (fun x => x ^ 3 - 13537 ^ 2)) := by
      refine Finset.mem_image.mpr ⟨568, ?_, by norm_num⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by norm_num), by norm_num⟩
    exact Finset.min'_le _ _ hmem
  have h2 : a 23 ≤ a070923 13537 := by
    unfold a
    rw [dif_pos (by norm_num : 1 ≤ 23)]
    have hmem : a070923 13537 ∈
        ((Finset.Ioo (23 ^ 3) ((23 + 1) ^ 3)).image a070923) := by
      refine Finset.mem_image.mpr ⟨13537, ?_, rfl⟩
      exact Finset.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
    exact Finset.min'_le _ _ hmem
  have hle : a 23 ≤ 63 := le_trans h2 h1
  have hq : (a 23 : ℚ) ≤ 63 := by exact_mod_cast hle
  linarith
