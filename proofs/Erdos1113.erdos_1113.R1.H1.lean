import OMAReductions.R_Erdos1113_erdos_1113_R1
import Mathlib

/-! `44745755 ^ 4` is a Sierpiński number (Filaseta, Finch and Kozek). For `n ≡ 2 (mod 4)`,
`k * 2 ^ n + 1 = 4 x ^ 4 + 1 = (2x² + 2x + 1)(2x² - 2x + 1)` with `x = 44745755 * 2 ^ (n / 4)`
(Sophie Germain). For every other residue of `n` modulo 48 one of 3, 17, 97, 241, 257, 673
divides `k * 2 ^ n + 1`, and the order of 2 modulo each of them divides 48. -/

set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Erdos1113_erdos_1113_R1.H1 := by
  refine ⟨by decide, fun n => ?_⟩
  have hpow := Nat.one_le_two_pow (n := n)
  by_cases h2 : n % 4 = 2
  · obtain ⟨u, rfl⟩ : ∃ u, n = 4 * u + 2 := ⟨n / 4, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, 44745755 * 2 ^ u = y + 1 := ⟨44745755 * 2 ^ u - 1, by
      have := Nat.one_le_two_pow (n := u); omega⟩
    have e : 44745755 ^ 4 * 2 ^ (4 * u + 2) + 1 =
        (2 * (y + 1) ^ 2 + 2 * (y + 1) + 1) * (2 * y ^ 2 + 2 * y + 1) := by
      have : 44745755 ^ 4 * 2 ^ (4 * u + 2) + 1 = 4 * (44745755 * 2 ^ u) ^ 4 + 1 := by ring
      rw [this, hy]; ring
    have hy1 : 1 ≤ y := by have := Nat.one_le_two_pow (n := u); nlinarith
    rw [e]
    refine ⟨by nlinarith, Nat.not_prime_mul (by nlinarith) (by nlinarith)⟩
  · have cover : ∀ r, r < 48 → r % 4 ≠ 2 → ∃ p ∈ ([3, 17, 97, 241, 257, 673] : List ℕ),
        p ∣ 44745755 ^ 4 * 2 ^ r + 1 := by decide +kernel
    obtain ⟨p, hp, hd⟩ := cover (n % 48) (Nat.mod_lt _ (by decide)) (by omega)
    have bounds : 1 < p ∧ p ≤ 673 := by fin_cases hp <;> decide
    have h48 : (2 : ℕ) ^ 48 ≡ 1 [MOD p] := by fin_cases hp <;> decide +kernel
    have he : (2 : ℕ) ^ n ≡ 2 ^ (n % 48) [MOD p] := by
      conv_lhs => rw [← Nat.div_add_mod n 48, pow_add, pow_mul]
      simpa using (h48.pow (n / 48)).mul_right (2 ^ (n % 48))
    have hdiv := (Nat.modEq_zero_iff_dvd).mp
      (((he.mul_left (44745755 ^ 4)).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr hd))
    have hbig : 673 < 44745755 ^ 4 * 2 ^ n + 1 := by
      have : (673 : ℕ) < 44745755 ^ 4 := by norm_num
      nlinarith
    refine ⟨by omega, fun hprime => ?_⟩
    rcases hprime.eq_one_or_self_of_dvd p hdiv with h | h <;> omega
