import OMAReductions.R_Green14_W_3_15_R1
import Mathlib

/-! Isolate two first-red positions when the new endpoint is blue. -/

-- Credit: @Genbox

namespace OMA.R_Green14_W_3_15_R1_H2_R1

def H1 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r 120 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 120 → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

def H2 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true → r 122 = true →
    (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

def H3 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true →
    ¬ (r 120 = true ∧ (∀ i : Fin 217, 108 < i.val → i.val < 120 → r i = false)) →
    ¬ (r 122 = true ∧ (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false)) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

def H4 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = false →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_15_R1.H2 := by
  classical
  intro first120 first122 remainder blueMid r noRed noBlue
  cases midpoint : r 108 with
  | false => exact blueMid r midpoint noRed noBlue
  | true =>
    by_cases at120 : r 120 = true ∧ (∀ i : Fin 217, 108 < i.val → i.val < 120 → r i = false)
    · exact first120 r midpoint at120.1 at120.2 noRed noBlue
    · by_cases at122 : r 122 = true ∧ (∀ i : Fin 217, 108 < i.val → i.val < 122 → r i = false)
      · exact first122 r midpoint at122.1 at122.2 noRed noBlue
      · exact remainder r midpoint at120 at122 noRed noBlue

end OMA.R_Green14_W_3_15_R1_H2_R1