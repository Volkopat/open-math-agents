import OMAReductions.R_Green14_W_3_14_R1_H1_R1

namespace OMA.R_Green14_W_3_14_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 91 = true → c 92 = true →
    (∀ q : Nat, 91 < q → q < 92 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 91 = true → c 93 = true →
    (∀ q : Nat, 91 < q → q < 93 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → OMA.R_Green14_W_3_14_R1_H1_R1.H1 := by
  intro first second c p lower upper anchor red between
  have choices : p = 92 ∨ p = 93 := by omega
  rcases choices with rfl | rfl
  · exact first c anchor red between
  · exact second c anchor red between

end OMA.R_Green14_W_3_14_R1_H1_R1_H1_R1