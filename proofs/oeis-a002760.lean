import OMAStatements.S_oeis_a002760
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002760.main) := by
  intro claim
  have zero_eight : (0 : Nat) = 8 :=
    (claim 0).mp ⟨Or.inl ⟨0, by decide +kernel⟩, Or.inl ⟨1, by decide +kernel⟩⟩
  exact (by decide +kernel : (0 : Nat) ≠ 8) zero_eight