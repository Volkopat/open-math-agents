import OMAReductions.R_Green14_W_3_15_R1_H1_R1
import Mathlib

namespace OMA.R_Green14_W_3_15_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r 120 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 120 → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H2 : Prop :=
  ∀ (r : Fin 217 → Bool) (p : Nat), 116 ≤ p → p ≤ 119 →
    r 108 = true → r (Fin.ofNat 217 p) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < p → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H3 : Prop :=
  ∀ (r : Fin 217 → Bool) (p : Nat), 121 ≤ p → p ≤ 123 →
    r 108 = true → r (Fin.ofNat 217 p) = true →
    (∀ i : Fin 217, 108 < i.val → i.val < p → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_15_R1_H1_R1.H1 := by
  classical
  intro at120 lower upper r midpointRed gap noRed noBlue
  have any : ∃ p : Nat, 109 ≤ p ∧ p ≤ 123 ∧ r (Fin.ofNat 217 p) = true := by
    by_contra! allBlue
    apply noBlue 109 1 (by decide) (by decide)
    intro t
    have tb := t.isLt
    apply Bool.eq_false_of_not_eq_true
    exact allBlue ((109 : Fin 217).val + t.val * (1 : Fin 217).val)
      (by change 109 ≤ 109+t.val*1; omega) (by change 109+t.val*1 ≤ 123; omega)
  let p := Nat.find any
  obtain ⟨low, high, picked⟩ : 109 ≤ p ∧ p ≤ 123 ∧ r (Fin.ofNat 217 p) = true :=
    Nat.find_spec any
  have afterGap : 116 ≤ p := by
    by_contra! early
    have val : (Fin.ofNat 217 p).val = p := Nat.mod_eq_of_lt (by omega)
    have blue := gap (Fin.ofNat 217 p) (by rw [val]; omega) (by rw [val]; omega)
    exact Bool.false_ne_true (blue.symm.trans picked)
  have earlier : ∀ i : Fin 217, 108 < i.val → i.val < p → r i = false := by
    intro i afterMid beforeRed
    apply Bool.eq_false_of_not_eq_true
    intro red
    have index : Fin.ofNat 217 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    exact Nat.find_min any beforeRed ⟨by omega, by omega, index.symm ▸ red⟩
  by_cases is120 : p = 120
  · rw [is120] at picked earlier
    exact at120 r midpointRed picked earlier noRed noBlue
  · by_cases before120 : p < 120
    · exact lower r p afterGap (by omega) midpointRed picked earlier noRed noBlue
    · exact upper r p (by omega) high midpointRed picked earlier noRed noBlue

end OMA.R_Green14_W_3_15_R1_H1_R1_H1_R1