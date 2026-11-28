import OMAReductions.R_Green14_W_3_15_R1_H2_R1

/-!
Split the endpoint case into three cases at positions 107 and 105.  The two
cases with position 107 red stay together, so the later finite certificates
can be distributed across proof files of comparable computational size.

The Boolean case distinctions also appear in the four-case reduction in
open-math-agents PR #17025.
-/

namespace OMA.R_Green14_W_3_15_R1_H2_R1_H2_R2

def H1 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r 122 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false) →
    r 107 = true →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

def H2 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r 122 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false) →
    r 107 = false → r 105 = true →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

def H3 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r 122 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false) →
    r 107 = false → r 105 = false →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_15_R1_H2_R1.H2 := by
  intro red107 red105 blueBoth r anchor108 anchor122 gap noRed noBlue
  cases h107 : r 107 with
  | true => exact red107 r anchor108 anchor122 gap h107 noRed noBlue
  | false =>
    cases h105 : r 105 with
    | true => exact red105 r anchor108 anchor122 gap h107 h105 noRed noBlue
    | false => exact blueBoth r anchor108 anchor122 gap h107 h105 noRed noBlue

end OMA.R_Green14_W_3_15_R1_H2_R1_H2_R2
