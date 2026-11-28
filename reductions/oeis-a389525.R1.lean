import OMAStatements.S_oeis_a389525

namespace OMA.R_oeis_a389525_R1

open OMA.S_oeis_a389525

/-- Ordered representations through the updated verification bound in A389525. -/
def H1 : Prop :=
  ∀ n : ℕ, 3200 < n → n ≤ 7700000 → ∃ i j k m : ℕ, 1 ≤ m ∧ m ≤ k ∧ k ≤ j ∧ j ≤ i ∧
    2*n+1 = prime (i^2) + prime (j^2) + prime (k^2) + 2*prime (m^2)

/-- Ordered representations above the published verification bound. -/
def H2 : Prop :=
  ∀ n : ℕ, 7700000 < n → ∃ i j k m : ℕ, 1 ≤ m ∧ m ≤ k ∧ k ≤ j ∧ j ≤ i ∧
    2*n+1 = prime (i^2) + prime (j^2) + prime (k^2) + 2*prime (m^2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a389525.main := by
  intro hfinite htail n hlo
  rcases le_or_gt n 7700000 with h | h
  · exact hfinite n hlo h
  · exact htail n h

end OMA.R_oeis_a389525_R1
