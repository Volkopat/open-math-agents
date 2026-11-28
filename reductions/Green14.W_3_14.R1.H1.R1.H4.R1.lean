import OMAReductions.R_Green14_W_3_14_R1_H1_R1

namespace OMA.R_Green14_W_3_14_R1_H1_R1_H4_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 91 = true → c 94 = true →
    (∀ q : Nat, 91 < q → q < 94 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 186 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 92 = true → c 95 = true →
    (∀ q : Nat, 92 < q → q < 95 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 186 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → OMA.R_Green14_W_3_14_R1_H1_R1.H4 := by
  intro first second c a lower upper anchor red blue1 blue2
  have choices : a = 91 ∨ a = 92 := by omega
  rcases choices with rfl | rfl
  · apply first c anchor red
    intro q hlo hhi
    interval_cases q <;> assumption
  · apply second c anchor red
    intro q hlo hhi
    interval_cases q <;> assumption

end OMA.R_Green14_W_3_14_R1_H1_R1_H4_R1