import OMAStatements.S_oeis_a203159
import Mathlib.Tactic.Ring

/-! Expanding the product-and-omission recurrence cancels the three terms. -/

open OMA.S_oeis_a203159

theorem OMA.solution : type_of% @OMA.S_oeis_a203159.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp [a, products]
  ring
