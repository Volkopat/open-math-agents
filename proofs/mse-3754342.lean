import OMAStatements.S_mse_3754342
import Mathlib

open OMA.S_mse_3754342 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3754342.main) := fun h => by
  obtain ⟨L, hl, hi⟩ := h 1 1 one_pos one_pos
  have : ∀ k : ℕ, ⌊(10 : ℝ) ^ k⌋ = 10 ^ k := fun k => by exact_mod_cast Int.floor_intCast (R := ℝ) (10 ^ k)
  have hd : ∀ n, denominator 1 1 n = 1 := fun n => by
    induction n <;> simp [denominator, decimalDigit, *]
  obtain rfl := tendsto_nhds_unique hl (by rw [show quotient 1 1 = fun _ => 1 from funext fun n => by simp [quotient, hd]]; exact tendsto_const_nhds)
  exact hi ⟨1, by simp⟩
