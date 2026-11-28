import OMAStatements.S_oeis_a006519
import Mathlib

open ArithmeticFunction OMA.S_oeis_a006519

theorem OMA.solution : type_of% @OMA.S_oeis_a006519.main := by
  intro n hn
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hs (j) : (sigma 1 (2 ^ j * m) : ℚ) = (2 ^ (j + 1) - 1) * sigma 1 m := by
    rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_two_left.2 hm).pow_left j),
      sigma_one_apply_prime_pow Nat.prime_two]
    push_cast
    rw [geom_sum_eq (by norm_num)]
    ring
  have h0 : (sigma 1 m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (sigma_pos_iff.2 hm.pos).ne'
  have : (1 : ℚ) < 2 ^ (k + 1) := one_lt_pow₀ one_lt_two (by omega)
  rw [← mul_assoc, ← pow_succ', hs, hs, a]
  simp [Nat.factorization_mul, hm.pos.ne', Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat]
  field_simp [show (2 : ℚ) ^ (k + 1) - 1 ≠ 0 by linarith]
  ring
