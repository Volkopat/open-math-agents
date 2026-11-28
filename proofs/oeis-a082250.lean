import OMAStatements.S_oeis_a082250
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a082250.main) := by
  intro h
  have h1 := (h 2 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have h2 : (2 : ℕ) ∣ OMA.S_oeis_a082250.concat 1 (List.range' 2 1) := by
    simp [OMA.S_oeis_a082250.concat, List.range']
  have h3 := h1 h2
  simp [OMA.S_oeis_a082250.concat, List.range'] at h3
