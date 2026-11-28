import OMAStatements.S_oeis_a051159

-- Source: George Beck's conjecture in OEIS A051159 (Dec 16, 2017).
-- https://oeis.org/A051159/internal
-- Solver: @grp06

open OMA.S_oeis_a051159

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a051159.main) := by
  intro h
  have hU : U 1 1 = -1 := by
    unfold U
    rw [Finset.prod_range_one, Polynomial.coeff_add,
      Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
    norm_num
  have hT : T 1 1 = 1 := by
    norm_num [T, Nat.choose_one_right]
  have hUV : triangularProduct U V 1 1 = -1 := by
    unfold triangularProduct
    rw [Finset.sum_range_succ _ 1, Finset.sum_range_one]
    norm_num [V, hU]
  have hEntry := h.2.1 1 1
  rw [hT, hUV] at hEntry
  norm_num at hEntry
