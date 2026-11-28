import OMAStatements.S_oeis_a081052
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a081052.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [OMA.S_oeis_a081052.a, OMA.S_oeis_a081052.s]
  simp only [show m + 3 + 1 = (m + 3) + 1 from rfl, Nat.stirlingFirst_succ_succ,
    Nat.stirlingFirst_succ_zero]
  push_cast
  ring
