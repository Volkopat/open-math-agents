import OMAStatements.S_oeis_a054109

open OMA.S_oeis_a054109 in
theorem OMA.solution : type_of% @OMA.S_oeis_a054109.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have s (j : ℕ) : ((j:ℤ)+2) * (2*j+3).choose (j+2) = 2*(2*j+3) * (2*j+1).choose (j+1) := by
    have h1 := Nat.add_one_mul_choose_eq (2*j+2) (j+1)
    have h2 := Nat.choose_succ_succ' (2*j+1) j
    have h3 := j.choose_symm_half
    zify at h1 h2 h3
    linear_combination (2*j+3)*(h2-h3)-h1
  have d (j : ℕ) : a (j+1) = b (j+1) - a j := by
    rw [a, Finset.sum_range_succ, a, eq_sub_iff_add_eq', ← add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero]
    · simp
    · intro i hi
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.1 hi), pow_succ]
      ring
  have s1 := s (k+1)
  simp [d, b, add_assoc, mul_add] at s1 ⊢
  linear_combination s1
