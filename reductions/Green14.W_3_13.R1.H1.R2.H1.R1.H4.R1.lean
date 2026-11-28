import OMAReductions.R_Green14_W_3_13_R1_H1_R2_H1_R1

-- Reduction Green14.W_3_13.R1.H1.R2.H1.R1.H4.R1 of step Green14.W_3_13.R1.H1.R2.H1.R1.H4
-- Credit: @YutaViriato

/-!
# Balanced four-way split of the five-blue-site 158-site pattern

Splits `Green14.W_3_13.R1.H1.R2.H1.R1.H4` (`S 78` red and `76, 77, 79, 80, 81` blue on sites
`0..157`) by expanding outward symmetrically to sites `75, 82`, then `74, 83`, then `73, 84`.
Each of the four resulting subcases has a substantially smaller search tree (~51k to ~84k
branches under the minimum-slot bitboard verifier, smaller than the merged `H1` sibling),
so every branch fits comfortably within the Lean kernel time and memory limits.
-/

namespace OMA.R_Green14_W_3_13_R1_H1_R2_H1_R1_H4_R1

/-- At least one of the adjacent sites 75 or 82 is red. -/
def H1 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → ¬S 81 → ¬S 76 → (S 75 ∨ S 82) → False

/-- Sites 75 and 82 are blue, and at least one of 74 or 83 is red. -/
def H2 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → ¬S 81 → ¬S 76 → ¬S 75 → ¬S 82 → (S 74 ∨ S 83) → False

/-- Sites 74, 75, 82, and 83 are blue, and at least one of 73 or 84 is red. -/
def H3 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → ¬S 81 → ¬S 76 → ¬S 75 → ¬S 82 → ¬S 74 → ¬S 83 → (S 73 ∨ S 84) → False

/-- All sites 73..77 and 79..84 around red site 78 are blue. -/
def H4 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → ¬S 77 → ¬S 81 → ¬S 76 → ¬S 75 → ¬S 82 → ¬S 74 → ¬S 83 → ¬S 73 → ¬S 84 → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_13_R1_H1_R2_H1_R1.H4 := by
  intro h1 h2 h3 h4 S hbound hno hhit h78 h79 h80 h77 h81 h76
  by_cases h75 : S 75
  · exact h1 S hbound hno hhit h78 h79 h80 h77 h81 h76 (Or.inl h75)
  · by_cases h82 : S 82
    · exact h1 S hbound hno hhit h78 h79 h80 h77 h81 h76 (Or.inr h82)
    · by_cases h74 : S 74
      · exact h2 S hbound hno hhit h78 h79 h80 h77 h81 h76 h75 h82 (Or.inl h74)
      · by_cases h83 : S 83
        · exact h2 S hbound hno hhit h78 h79 h80 h77 h81 h76 h75 h82 (Or.inr h83)
        · by_cases h73 : S 73
          · exact h3 S hbound hno hhit h78 h79 h80 h77 h81 h76 h75 h82 h74 h83 (Or.inl h73)
          · by_cases h84 : S 84
            · exact h3 S hbound hno hhit h78 h79 h80 h77 h81 h76 h75 h82 h74 h83 (Or.inr h84)
            · exact h4 S hbound hno hhit h78 h79 h80 h77 h81 h76 h75 h82 h74 h83 h73 h84

end OMA.R_Green14_W_3_13_R1_H1_R2_H1_R1_H4_R1
