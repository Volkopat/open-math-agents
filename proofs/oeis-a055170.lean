import OMAStatements.S_oeis_a055170

namespace OMA.S_oeis_a055170

private theorem no_duplicate_first_occurrences (l : List ℕ) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp [List.mem_eraseDups], no_duplicate_first_occurrences _⟩
termination_by l.length
decreasing_by simpa using Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem segment_zero_count {l : List ℕ} (h₀ : 0 ∈ l) :
    (nextSegment l).count 0 = 1 := by
  rw [nextSegment, List.count_flatMap]
  have hcount := List.count_flatMap (l := l.eraseDups) (f := fun x => [x]) (x := 0)
  rw [List.flatMap_singleton'] at hcount
  rw [← List.count_eq_one_of_mem (no_duplicate_first_occurrences l) (List.mem_eraseDups.mpr h₀),
    hcount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  have hpositive : 0 < l.count x := List.count_pos_iff.mpr (List.mem_eraseDups.mp hx)
  simp [Function.comp_apply, List.count_cons, hpositive.ne']

private theorem zero_count (n : ℕ) : (stage n).count 0 = n + 1 := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    have h₀ : 0 ∈ stage n := List.count_pos_iff.mp (by omega)
    simp [stage, ih, segment_zero_count h₀, Nat.add_assoc]

private theorem stage_covers (n : ℕ) : ∀ k ≤ n, k ∈ stage n := by
  induction n with
  | zero =>
    intro k hk
    simp [stage, Nat.eq_zero_of_le_zero hk]
  | succ n ih =>
    intro k hk
    rw [stage]
    rcases eq_or_lt_of_le hk with rfl | hlt
    · apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨0, List.mem_eraseDups.mpr (ih 0 (Nat.zero_le _)), ?_⟩
      simp [zero_count]
    · exact List.mem_append_left _ (ih k (Nat.le_of_lt_succ hlt))

private theorem stage_length (n : ℕ) : n < (stage n).eraseDups.length := by
  have hs : List.range (n + 1) ⊆ (stage n).eraseDups := by
    intro k hk
    exact List.mem_eraseDups.mpr
      (stage_covers n k (Nat.le_of_lt_succ (List.mem_range.mp hk)))
  have := List.nodup_range.length_le_of_subset hs
  simpa using this

private theorem first_occurrences_prefix {n m : ℕ} (h : n ≤ m) :
    (stage n).eraseDups <+: (stage m).eraseDups := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step h ih =>
    rw [stage, List.eraseDups_append]
    exact ih.trans (List.prefix_append _ _)

private theorem stable {j m : ℕ} (h : j ≤ m) :
    a j = (stage m).eraseDups[j]'((stage_length j).trans_le (first_occurrences_prefix h).length_le) := by
  rw [a, List.getD_eq_getElem _ _ (stage_length j)]
  exact (first_occurrences_prefix h).getElem (stage_length j)

end OMA.S_oeis_a055170

open OMA.S_oeis_a055170 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055170.main := by
  constructor
  · intro i j h
    exact (no_duplicate_first_occurrences (stage (max i j))).getElem_inj_iff.mp
      ((stable (le_max_left i j)).symm.trans (h.trans (stable (le_max_right i j))))
  · intro x
    have hx : x ∈ (stage x).eraseDups := List.mem_eraseDups.mpr (stage_covers x x le_rfl)
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨j, (stable (le_max_left j x)).trans ?_⟩
    exact ((first_occurrences_prefix (le_max_right j x)).getElem hj).symm.trans he
