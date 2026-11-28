import OMAStatements.S_oeis_a387991

namespace OMA.R_oeis_a387991_R1

open OMA.S_oeis_a387991

/-- Ordered four-term representations throughout the range verified in A387991. -/
def H1 : Prop :=
  ∀ n : ℕ, 3070 ≤ n → n ≤ 200000 → ∃ i j k m : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ m ∧
    n = i * prime i + j * prime j + k * prime k + m * prime m

/-- Ordered four-term representations above the published verification range. -/
def H2 : Prop :=
  ∀ n : ℕ, 200000 < n → ∃ i j k m : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ m ∧
    n = i * prime i + j * prime j + k * prime k + m * prime m

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a387991.main := by
  intro hfinite htail n hn
  rcases le_or_gt n 200000 with h | h
  · exact hfinite n hn h
  · exact htail n h

end OMA.R_oeis_a387991_R1
