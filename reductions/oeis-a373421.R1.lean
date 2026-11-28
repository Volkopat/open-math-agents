import OMAStatements.S_oeis_a373421

namespace OMA.R_oeis_a373421_R1

open OMA.S_oeis_a373421

/-- The published extreme candidate is itself an exception. -/
def H1 : Prop := ¬ IsRepresentable 2671

/-- Every integer beyond the candidate has a representation. -/
def H2 : Prop := ∀ n : ℕ, 2671 < n → IsRepresentable n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a373421.main := by
  intro hwitness htail
  refine ⟨⟨by decide, hwitness⟩, ?_⟩
  intro n hn
  by_contra! h
  exact hn.2 (htail n h)

end OMA.R_oeis_a373421_R1
