import OMAStatements.S_oeis_a121571

namespace OMA.R_oeis_a121571_R1

open OMA.S_oeis_a121571 (Rep)

def H1 : Prop := ¬ Rep 340250525752

def H2 : Prop := ∀ m : ℕ, 340250525752 < m → Rep m

def H3 : Prop :=
  {m : ℕ | 0 < m ∧ m ≤ 340250525752 ∧ ¬ Rep m}.ncard = 31332338304

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a121571.main := by
  intro boundary beyond count
  refine ⟨boundary, beyond, ?_⟩
  have same :
      {m : ℕ | 0 < m ∧ ¬ Rep m} =
        {m : ℕ | 0 < m ∧ m ≤ 340250525752 ∧ ¬ Rep m} := by
    ext m
    constructor
    · rintro ⟨positive, absent⟩
      exact ⟨positive, le_of_not_gt (fun greater => absent (beyond m greater)), absent⟩
    · rintro ⟨positive, _, absent⟩
      exact ⟨positive, absent⟩
  rw [same]
  exact count

end OMA.R_oeis_a121571_R1