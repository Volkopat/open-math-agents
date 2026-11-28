import OMAStatements.S_oeis_a073023

-- Credit: @tjgksruf9801 (shorter proof). n = 102: the partial sum is 1025, and
-- 1025 ^ 2 ≤ 102 ^ 3, so 1025 ≤ 102 ^ (3 / 2).

set_option maxRecDepth 35000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a073023.main) := fun h => by
  have := h 102 (by decide)
  rw [show ∑ k ∈ Finset.Icc 1 102, OMA.S_oeis_a073023.a k = 1025 by
    unfold OMA.S_oeis_a073023.a; decide +kernel, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num), ← Real.sqrt_eq_rpow] at this
  norm_num at this
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 102 by norm_num), Real.sqrt_nonneg 102]
