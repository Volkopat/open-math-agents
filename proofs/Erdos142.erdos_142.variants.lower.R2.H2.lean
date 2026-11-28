import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/- Based on #38355 (@pmcao), consolidating #5265 (@Salofe), #32324
(@weizj99), and #37256 (@596050). Compare powers directly using strict
monotonicity; transport all chosen data together into the first block. -/
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k _ B hB f ⟨a, d, hd, h⟩
  choose! j b hb e using h
  have E {x y} (_ : 4 ^ x < 4 ^ y * 4) (_ : 4 ^ y < 4 ^ x * 4) : x = y := by
    simp [← Nat.pow_succ, Nat.pow_lt_pow_iff_right (by decide : 1 < 4)] at *
    omega
  have Q i (t : i < k) := (⟨Finset.mem_Icc.1 (hB _ (hb i t)), e i t⟩ : _ ∧ _)
  have u := Q 1 (by omega); have := Q 2 (by omega)
  rw [show j 1 = j 2 from E (by omega) (by omega)] at u
  have : d ≤ a := by omega
  have S i : i < k → j i = j 0 := by
    induction i with
    | zero => simp
    | succ i p =>
      intro t; have := Q i (by omega); have := Q (i + 1) t; have := Nat.add_mul i 1 d
      exact (E (by omega) (by omega)).trans (p (by omega))
  refine f (j 0) ⟨b 0, d, hd, fun i t => ?_⟩
  have := Q 0 (by omega); have := Q i t; have hbi := hb i t
  rw [S i t] at *
  rwa [show b 0 + i * d = b i by omega]
