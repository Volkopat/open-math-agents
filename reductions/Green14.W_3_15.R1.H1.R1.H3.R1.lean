import OMAReductions.R_Green14_W_3_15_R1_H1_R1
import Mathlib

namespace OMA.R_Green14_W_3_15_R1_H1_R1_H3_R1

def H1 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = false → r 122 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H2 : Prop :=
  ∀ (r : Fin 217 → Bool) (p : Nat), 119 ≤ p → p ≤ 121 →
    r 108 = false → r (Fin.ofNat 217 p) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < p → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H3 : Prop :=
  ∀ (r : Fin 217 → Bool) (p : Nat), 109 ≤ p → p ≤ 118 →
    r 108 = false → r (Fin.ofNat 217 p) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < p → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_15_R1_H1_R1.H3 := by
  classical
  intro at122 later earlier r midpoint noRed noBlue
  have any : ∃ p : Nat, 109 ≤ p ∧ p ≤ 122 ∧ r (Fin.ofNat 217 p) = true := by
    by_contra! allBlue
    apply noBlue 108 1 (by decide) (by decide)
    intro t
    have bound := t.isLt
    change r (Fin.ofNat 217 (108+t.val*1)) = false
    by_cases zero : t.val = 0
    · simpa [zero] using midpoint
    · apply Bool.eq_false_of_not_eq_true
      exact allBlue (108+t.val*1) (by omega) (by omega)
  let p := Nat.find any
  obtain ⟨low, high, picked⟩ : 109 ≤ p ∧ p ≤ 122 ∧ r (Fin.ofNat 217 p) = true :=
    Nat.find_spec any
  have before : ∀ i : Fin 217, 108 < i.val → i.val < p → r i = false := by
    intro i afterMid beforeRed
    apply Bool.eq_false_of_not_eq_true
    intro red
    have index : Fin.ofNat 217 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    exact Nat.find_min any beforeRed ⟨by omega, by omega, index.symm ▸ red⟩
  by_cases last : p = 122
  · rw [last] at picked before
    exact at122 r midpoint picked before noRed noBlue
  by_cases lowGroup : p ≤ 118
  · exact earlier r p low lowGroup midpoint picked before noRed noBlue
  · exact later r p (by omega) (by omega) midpoint picked before noRed noBlue

end OMA.R_Green14_W_3_15_R1_H1_R1_H3_R1