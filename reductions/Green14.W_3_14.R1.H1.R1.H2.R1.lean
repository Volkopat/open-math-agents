import OMAReductions.R_Green14_W_3_14_R1_H1_R1

namespace OMA.R_Green14_W_3_14_R1_H1_R1_H2_R1

def H1 : Prop :=
  ∀ (c : Nat → Bool), c 91 = true → c 95 = true →
    (∀ q : Nat, 91 < q → q < 95 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ (c : Nat → Bool), c 91 = true → c 96 = true →
    (∀ q : Nat, 91 < q → q < 96 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), (p = 97 ∨ p = 98) → c 91 = true → c p = true →
    (∀ q : Nat, 91 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), (p = 99 ∨ p = 100) → c 91 = true → c p = true →
    (∀ q : Nat, 91 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1_H1_R1.H2 := by
  intro h95 h96 pair1 pair2 c p lower upper anchor red gap
  have positions : p = 95 ∨ p = 96 ∨ (p = 97 ∨ p = 98) ∨ (p = 99 ∨ p = 100) := by omega
  rcases positions with rfl | rfl | small | large
  · exact h95 c anchor red gap
  · exact h96 c anchor red gap
  · exact pair1 c p small anchor red gap
  · exact pair2 c p large anchor red gap

end OMA.R_Green14_W_3_14_R1_H1_R1_H2_R1