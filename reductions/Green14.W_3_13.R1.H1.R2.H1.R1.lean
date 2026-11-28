import OMAReductions.R_Green14_W_3_13_R1_H1_R2

/-!
# Four-way central case split of the two-blue-site 158-site pattern

Splits `Green14.W_3_13.R1.H1.R2.H1` (`S 78`, `¬S 79`, `¬S 80` on sites 0..157)
by the colors of the adjacent central sites 77, 81, and 76. Each resulting
branch reduces the search tree significantly so that the decision-tree
certificates fit comfortably within the Lean kernel time and memory limits.
-/

namespace OMA.R_Green14_W_3_13_R1_H1_R2_H1_R1

/-- Site 77 is red alongside 78 (forcing 76 and 79 blue). -/
def H1 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → S 77 → False

/-- Site 77 is blue and site 81 is red. -/
def H2 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → S 81 → False

/-- Sites 77 and 81 are blue and site 76 is red. -/
def H3 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → ¬S 81 → S 76 → False

/-- Sites 76, 77, 79, 80, and 81 are all blue around red site 78. -/
def H4 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → ¬S 81 → ¬S 76 → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_13_R1_H1_R2.H1 := by
  intro h1 h2 h3 h4 S hbound hno hhit h78 h79 h80
  by_cases h77 : S 77
  · exact h1 S hbound hno hhit h78 h79 h80 h77
  · by_cases h81 : S 81
    · exact h2 S hbound hno hhit h78 h79 h80 h77 h81
    · by_cases h76 : S 76
      · exact h3 S hbound hno hhit h78 h79 h80 h77 h81 h76
      · exact h4 S hbound hno hhit h78 h79 h80 h77 h81 h76

end OMA.R_Green14_W_3_13_R1_H1_R2_H1_R1
