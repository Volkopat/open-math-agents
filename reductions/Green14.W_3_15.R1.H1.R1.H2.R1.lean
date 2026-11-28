import OMAReductions.R_Green14_W_3_15_R1_H1_R1
import Mathlib

namespace OMA.R_Green14_W_3_15_R1_H1_R1_H2_R1

def H1 : Prop :=
  ∀ (r : Fin 217 → Bool) (p : Nat), 109 ≤ p → p ≤ 111 →
    r 108 = true → r (Fin.ofNat 217 p) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < p → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H2 : Prop :=
  ∀ (r : Fin 217 → Bool) (p : Nat), 112 ≤ p → p ≤ 114 →
    r 108 = true → r (Fin.ofNat 217 p) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < p → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H3 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r (Fin.ofNat 217 115) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 115 → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_15_R1_H1_R1.H2 := by
  classical
  intro through111 through114 at115 r midpoint inside noRed noBlue
  have any : ∃ p : Nat, 109 ≤ p ∧ p ≤ 115 ∧ r (Fin.ofNat 217 p) = true := by
    obtain ⟨i, low, high, red⟩ := inside
    have index : Fin.ofNat 217 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    exact ⟨i.val, low, high, index.symm ▸ red⟩
  let p := Nat.find any
  obtain ⟨low, high, picked⟩ : 109 ≤ p ∧ p ≤ 115 ∧ r (Fin.ofNat 217 p) = true :=
    Nat.find_spec any
  have earlier : ∀ i : Fin 217, 108 < i.val → i.val < p → r i = false := by
    intro i afterMid beforeRed
    apply Bool.eq_false_of_not_eq_true
    intro red
    have index : Fin.ofNat 217 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    exact Nat.find_min any beforeRed ⟨by omega, by omega, index.symm ▸ red⟩
  by_cases firstGroup : p ≤ 111
  · exact through111 r p low firstGroup midpoint picked earlier noRed noBlue
  by_cases secondGroup : p ≤ 114
  · exact through114 r p (by omega) secondGroup midpoint picked earlier noRed noBlue
  have last : p = 115 := by omega
  rw [last] at picked earlier
  exact at115 r midpoint picked earlier noRed noBlue

end OMA.R_Green14_W_3_15_R1_H1_R1_H2_R1