import OMAStatements.S_oeis_a390871

theorem OMA.solution : type_of% @OMA.S_oeis_a390871.main := by
  intro k hk hpow m r _ hr h
  set f := Nat.log 2 k with hf
  have hlo : 2 ^ f ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hhi : k < 2 ^ (f + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  obtain ⟨d, rfl⟩ : ∃ d, k = r + d := ⟨k - r, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hsq : (r + d) ^ 2 - r ^ 2 = d * (2 * r + d) := by
    have : (r + d) ^ 2 = r ^ 2 + d * (2 * r + d) := by ring
    omega
  rw [hsq] at h
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  constructor
  · -- lower bound: k - r = 1 forces k to be a power of two, k - r = 2 breaks parity
    have hd3 : 3 ≤ d := by
      rcases (show d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with h1 | h1 | h1
      · subst h1
        exact absurd ⟨m - 1, by omega⟩ hpow
      · subst h1
        omega
      · exact h1
    have hbig : 6 * (r + d) ≤ d * (2 * r + d) + 9 := by
      nlinarith [Nat.mul_le_mul (show 3 ≤ d from hd3) (le_refl r)]
    have hpowlt : 2 ^ (f + 2) < 2 ^ m := by
      rw [pow_succ]; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hpowlt
    omega
  · -- upper bound: 2^m ≤ k^2 + 1 < 4^(f+1)
    have hk2 : (r + d) ^ 2 + 1 < 2 ^ (2 * f + 2) := by
      have : r + d + 1 ≤ 2 ^ (f + 1) := hhi
      have h22 : 2 ^ (2 * f + 2) = 2 ^ (f + 1) * 2 ^ (f + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [h22]
      nlinarith
    have hle : 2 ^ m ≤ (r + d) ^ 2 + 1 := by
      have : d * (2 * r + d) ≤ (r + d) ^ 2 := by nlinarith
      omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (lt_of_le_of_lt hle hk2)
    omega
