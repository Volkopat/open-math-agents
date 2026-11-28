import OMAReductions.R_LanderParkinSelfridge_lander_parkin_selfridge_R1

-- Step LanderParkinSelfridge.lander_parkin_selfridge.R1.H1: hypothesis H1 of reduction LanderParkinSelfridge.lander_parkin_selfridge.R1
-- Credit: @Moti1125

/-
If `n + m < k ≤ 4`, then `n + m` is `2` or `3`, since `n` and `m` are positive.
* `n = m = 1`: `a ^ k = b ^ k` with `k ≠ 0` forces `a = b`, which is excluded.
* `n + m = 3`: then `k = 4`, and the equation is `a ^ 4 + b ^ 4 = c ^ 4` with positive terms,
  which Fermat's theorem for exponent four rules out.
-/
theorem OMA.solution : OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_R1.H1 := by
  intro k n m x y hk hn hm hx hy hxy h
  by_contra hlt
  push_neg at hlt
  have hcases : (n = 1 ∧ m = 1) ∨ (n = 1 ∧ m = 2) ∨ (n = 2 ∧ m = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Fin.sum_univ_one] at h
    exact hxy 0 0 (Nat.pow_left_injective (by omega) h)
  · obtain rfl : k = 4 := by omega
    simp only [Fin.sum_univ_one, Fin.sum_univ_two] at h
    exact fermatLastTheoremFour (y 0) (y 1) (x 0) (hy 0).ne' (hy 1).ne' (hx 0).ne' h.symm
  · obtain rfl : k = 4 := by omega
    simp only [Fin.sum_univ_one, Fin.sum_univ_two] at h
    exact fermatLastTheoremFour (x 0) (x 1) (y 0) (hx 0).ne' (hx 1).ne' (hy 0).ne' h
