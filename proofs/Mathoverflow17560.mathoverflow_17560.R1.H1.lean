import OMAReductions.R_Mathoverflow17560_mathoverflow_17560_R1

-- Rational-exponent case only. Taking the exponent of 2 in m^b = 2^a gives x directly.
theorem OMA.solution : OMA.R_Mathoverflow17560_mathoverflow_17560_R1.H1 := by
  rintro x ⟨q, rfl⟩ ⟨m, hm⟩
  have hmpos : 0 < m := by
    exact_mod_cast (hm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (q : ℝ))
  have hq : (0 : ℝ) ≤ q := by
    by_contra h
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (lt_of_not_ge h)
    rw [hm] at hlt
    have : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    exact (not_lt_of_ge this) hlt
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq)
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrep : (q : ℝ) * q.den = q.num.natAbs := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hd]
    have hi : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hi
    simpa only [Int.cast_natCast] using hr.symm
  have hp : m ^ q.den = 2 ^ q.num.natAbs := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [← hm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      hrep, Real.rpow_natCast]
  have hv := congrArg (fun z : ℕ => z.factorization 2) hp
  rw [Nat.factorization_pow_self Nat.prime_two] at hv
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hv
  refine ⟨m.factorization 2, ?_⟩
  apply (mul_left_inj' hd).mp
  rw [hrep, mul_comm]
  exact_mod_cast hv.symm
