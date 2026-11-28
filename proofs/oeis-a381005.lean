import OMAStatements.S_oeis_a381005

open OMA.S_oeis_a381005 in
theorem OMA.solution : type_of% @OMA.S_oeis_a381005.main := by
  intro n hn
  have := Nat.pow_le_pow_right two_pos (show 2 * n ≤ 4 * n - 2 by omega)
  have := dvd_pow_self 2 (show 4 * n - 2 ≠ 0 by omega)
  have := dvd_pow_self 2 (show 2 * n ≠ 0 by omega)
  have : 2 ^ (4 * n) = 4 * 2 ^ (4 * n - 2) := by
    rw [show 2 ^ (4 * n) = 2 ^ (4 * n - 2 + 2) from congrArg _ (by omega), pow_add]; ring
  have := @Nat.one_le_two_pow (2 * n)
  apply (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _))
  rw [← Nat.coprime_add_self_right, show C n + B n = 2 ^ (4 * n) * 2 by unfold B C; omega,
    Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right, and_self,
    Nat.odd_iff]
  unfold B
  omega
