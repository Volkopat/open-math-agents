import OMAReductions.R_oeis_a058887_R1

/-! Use the six covering divisors from PR #20286 and transport the residues using Nat.ModEq. -/

theorem OMA.solution : OMA.R_oeis_a058887_R1.H1 := by
  refine ⟨by norm_num, by decide, ?_⟩
  intro n _
  have cover : ∀ r < 24, ∃ q ∈ ([3, 5, 7, 13, 17, 241] : List ℕ),
      2 ≤ q ∧ q ≤ 241 ∧ 2 ^ 24 ≡ 1 [MOD q] ∧ 271129 * 2 ^ r + 1 ≡ 0 [MOD q] := by
    decide +kernel
  obtain ⟨q, _, hlo, hhi, period, residue⟩ := cover (n % 24) (Nat.mod_lt _ (by decide))
  have periodic : 2 ^ n ≡ 2 ^ (n % 24) [MOD q] := by
    conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
    simpa only [one_pow, one_mul] using (period.pow (n / 24)).mul_right (2 ^ (n % 24))
  have divisible := Nat.modEq_zero_iff_dvd.mp (((periodic.mul_left 271129).add_right 1).trans residue)
  have positive : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  exact Nat.not_prime_of_dvd_of_lt divisible hlo (by omega)
