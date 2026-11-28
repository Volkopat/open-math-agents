import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3

/-! Cauchy condensation (`summable_condensed_iff_of_nonneg`): it suffices that `2^m f (2^m)` is summable,
and it is eventually bounded by the summable `1 / (m + 1)^2`. -/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2 := by
  intro f hf hanti hev
  rw [← summable_condensed_iff_of_nonneg hf (fun m n _ hmn => hanti hmn)]
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  filter_upwards [hev] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hf _))]
  exact hm
