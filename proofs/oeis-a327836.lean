import OMAStatements.S_oeis_a327836

open OMA.S_oeis_a327836 in
theorem OMA.solution : type_of% @OMA.S_oeis_a327836.main := by
  intro n _
  apply Nat.sInf_le
  refine ⟨by positivity, (Nat.modEq_iff_dvd.mpr ?_).symm⟩
  have h : (n : ℤ) + 1 ∣ (n : ℤ) ^ 2 - 1 := ⟨(n : ℤ) - 1, by ring⟩
  push_cast
  simpa [pow_mul] using dvd_sub_pow_of_dvd_sub h n
