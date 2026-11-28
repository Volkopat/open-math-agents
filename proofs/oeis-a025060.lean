import OMAStatements.S_oeis_a025060

theorem OMA.solution : type_of% @OMA.S_oeis_a025060.main := by
  intro z
  set t : ℤ := |z| + 3 with ht
  have hz1 : -|z| ≤ z := neg_abs_le z
  have hz2 : z ≤ |z| := le_abs_self z
  have h0 : 0 ≤ |z| := abs_nonneg z
  refine ⟨t, 1 - t, z + t ^ 2 - t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · nlinarith
  · omega
  · nlinarith
  · nlinarith
  · ring
