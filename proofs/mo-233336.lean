import OMAStatements.S_mo_233336
import Mathlib

-- Problem: mo-233336, given n, A >= B > 0, an index j and the denominators before j, is x_j
-- bounded for all nondecreasing positive x with B <= sum 1/x_i <= A?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take n = 2, B = 1, A = 2, j the second index and x_1 = 1. Then (1, m) is admissible for
-- every m >= 1, since 1 <= 1 + 1/m <= 2, so x_2 = m is unbounded.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_233336.main) := by
  intro h
  obtain ⟨bound, hb⟩ := h 2 2 1 (by norm_num) (by norm_num) 1 (fun _ => 1)
  have hs : ∑ i, (1 : ℚ) / ((![1, bound + 1] i : ℕ) : ℚ) = 1 + 1 / ((bound : ℚ) + 1) := by
    rw [Fin.sum_univ_two]
    simp
  have hnn : (0 : ℚ) ≤ (bound : ℚ) := Nat.cast_nonneg bound
  have key := hb ![1, bound + 1]
    (by intro i; fin_cases i <;> simp)
    (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
    (by intro i hi; fin_cases i <;> simp_all)
    (by
      rw [hs]
      have h1 : (0 : ℚ) ≤ 1 / ((bound : ℚ) + 1) := by positivity
      linarith)
    (by
      rw [hs]
      have h1 : 1 / ((bound : ℚ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith)
  have key' : bound + 1 ≤ bound := key
  omega
