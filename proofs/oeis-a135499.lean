import OMAStatements.S_oeis_a135499
open OMA.S_oeis_a135499

theorem OMA.solution : type_of% @OMA.S_oeis_a135499.main := by
  rintro n ⟨-, h⟩
  have k (L : List ℕ) : ((digitSums L).1 : ℤ) - (digitSums L).2 = (L.map (↑)).alternatingSum := by
    induction L <;> simp [digitSums, List.alternatingSum_cons] <;> linarith
  simp [Nat.eleven_dvd_iff, ← k, h]
