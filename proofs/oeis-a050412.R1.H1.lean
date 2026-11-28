import OMAReductions.R_oeis_a050412_R1

/-! Use the covering congruences of PR #20279 and transport them with Nat.ModEq. -/

theorem OMA.solution : OMA.R_oeis_a050412_R1.H1 := by
  refine ⟨by decide, ?_⟩
  intro k hk
  have cover : ∀ r < 24, ∃ q ∈ ([3, 5, 7, 13, 17, 241] : List ℕ),
      2 ≤ q ∧ q ≤ 241 ∧ 2 ^ 24 ≡ 1 [MOD q] ∧ 509203 * 2 ^ r ≡ 1 [MOD q] := by
    decide +kernel
  obtain ⟨q, _, hlo, hhi, period, residue⟩ := cover (k % 24) (Nat.mod_lt _ (by decide))
  have periodic : 2 ^ k ≡ 2 ^ (k % 24) [MOD q] := by
    conv_lhs => rw [← Nat.div_add_mod k 24, pow_add, pow_mul]
    simpa only [one_pow, one_mul] using (period.pow (k / 24)).mul_right (2 ^ (k % 24))
  have hk₂ : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  exact Nat.not_prime_of_dvd_of_lt
    ((Nat.modEq_iff_dvd' (by omega)).mp ((periodic.mul_left 509203).trans residue).symm)
    hlo (by omega)
