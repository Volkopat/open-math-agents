import OMAReductions.R_Green14_W_3_16_R2_H1_R1

/-! Partition reflection-symmetric colorings by three specified positions. -/

namespace OMA.R_Green14_W_3_16_R2_H1_R1_H2_R1

private def Admissible (c : Nat → Bool) : Prop :=
  (∀ x < 233, c (232-x) = c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d →
      a + ((if b then 16 else 3)-1)*d < 233 →
      ∃ t < (if b then 16 else 3), c (a+t*d) = b

def H1 : Prop := ∀ c : Nat → Bool,
  c 92 = false → c 98 = false → c 86 = false → ¬ Admissible c

def H2 : Prop := ∀ c : Nat → Bool,
  c 92 = false → c 98 = false → c 86 = true → ¬ Admissible c

def H3 : Prop := ∀ c : Nat → Bool,
  c 92 = false → c 98 = true → ¬ Admissible c

def H4 : Prop := ∀ c : Nat → Bool,
  c 92 = true → ¬ Admissible c

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_16_R2_H1_R1.H2 := by
  intro left right mixed red c good
  cases h92 : c 92
  · cases h98 : c 98
    · cases h86 : c 86
      · exact left c h92 h98 h86 good
      · exact right c h92 h98 h86 good
    · exact mixed c h92 h98 good
  · exact red c h92 good

end OMA.R_Green14_W_3_16_R2_H1_R1_H2_R1