import OMAReductions.R_Constant7b_c7b_upper_bound_R1

/-!
Proof of `OMA.R_Constant7b_c7b_upper_bound_R1.H2`.

Write `q = 10 ^ 143` and `δ = p - q > 0`. Since `n ^ δ → ∞`, eventually `C / c < n ^ δ`.
For such `n ≥ 1`, `n ^ p = n ^ q * n ^ δ`, and `C / n ^ p < c / n ^ q` is
`C * n ^ q < c * n ^ q * n ^ δ`.
-/

open Filter

theorem OMA.solution : OMA.R_Constant7b_c7b_upper_bound_R1.H2 := by
  intro c C hc hC p hp
  have hδ : 0 < p - (10 : ℝ) ^ 143 := by linarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (p - (10 : ℝ) ^ 143)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually_gt_atTop (C / c))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by linarith
  have key : C / c < (n : ℝ) ^ (p - (10 : ℝ) ^ 143) := hN n (le_of_max_le_left hn)
  have hq : 0 < (n : ℝ) ^ ((10 : ℝ) ^ 143) := Real.rpow_pos_of_pos hnpos _
  have hd : 0 < (n : ℝ) ^ (p - (10 : ℝ) ^ 143) := Real.rpow_pos_of_pos hnpos _
  have hp' : (n : ℝ) ^ p = (n : ℝ) ^ ((10 : ℝ) ^ 143) * (n : ℝ) ^ (p - (10 : ℝ) ^ 143) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hC' : C < c * (n : ℝ) ^ (p - (10 : ℝ) ^ 143) := by
    rw [div_lt_iff₀ hc] at key
    linarith
  rw [div_lt_div_iff₀ (by rw [hp']; positivity) hq, hp']
  nlinarith [mul_lt_mul_of_pos_right hC' hq]
