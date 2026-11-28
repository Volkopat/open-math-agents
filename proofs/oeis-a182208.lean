import OMAStatements.S_oeis_a182208
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a182208.main := by
  rintro C ⟨h1, -, hF⟩ h7
  obtain ⟨e, r, hr, hCe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : C ≠ 0) 7 (by norm_num)
  obtain ⟨b, hb7, hbr⟩ := Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hr) 3 1
  have hbC : b.Coprime C := by
    rw [hCe]
    exact .mul_right (.pow_right e (by rw [Nat.Coprime, hb7.gcd_eq]; norm_num)) (by rw [Nat.Coprime, hbr.gcd_eq]; simp)
  have h3 := (hb7.pow (C - 1)).symm.trans ((hF b hbC).of_dvd h7)
  rw [Nat.ModEq, ← Nat.div_add_mod (C - 1) 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at h3
  have := Nat.mod_lt (C - 1) (by norm_num : 6 > 0)
  obtain ⟨k, hk⟩ := h7
  refine ⟨(k - 1) / 6, 0, Or.inl ?_⟩
  interval_cases h : (C - 1) % 6 <;> simp_all <;> omega
