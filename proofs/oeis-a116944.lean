import OMAStatements.S_oeis_a116944

-- The discrepancy is recorded in OEIS A116944 and A068894.
-- Both sequences reach 125. The least eligible fourth-power base is 57.
open OMA.S_oeis_a116944

theorem OMA.solution : type_of% @OMA.S_oeis_a116944.main := by
  refine ⟨4, by decide, ?_⟩
  have hrec : recurrence 4 = 252047376 := by decide
  have hleast : leastPower 4 = 10556001 := by decide
  rw [hrec, hleast]
  decide
