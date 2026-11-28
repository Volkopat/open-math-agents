import OMAStatements.S_mo_365019
import Mathlib

open OMA.S_mo_365019

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_365019.main) := by
  intro conjecture
  have hbound := conjecture 1 (fun _ => 1) (by decide) (fun _ => by decide)
    (fun _ _ _ => Nat.coprime_one_left 1)
  have hone : h 1 = ⊤ := by
    simp [h]
  simp [hone] at hbound