import OMAStatements.S_oeis_a275482
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a275482.main) := by
  intro h
  obtain ⟨n, hn⟩ := h.2 0
  cases n with
  | zero =>
      simp [OMA.S_oeis_a275482.term, OMA.S_oeis_a275482.history] at hn
  | succ n =>
      simp [OMA.S_oeis_a275482.term, OMA.S_oeis_a275482.history,
        OMA.S_oeis_a275482.next] at hn
