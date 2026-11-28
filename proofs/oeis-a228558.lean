import OMAStatements.S_oeis_a228558

open OMA.S_oeis_a228558

theorem OMA.solution : type_of% @OMA.S_oeis_a228558.main := by
  intro n hn
  obtain ⟨hnDvd, hnPrime⟩ := hn
  have hodd : Odd n := by
    by_contra hnodd
    obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp hnodd
    have hmod : 17 ^ (k + k) + 4 ^ (k + k) ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_trans (by decide : 3 ∣ 21) hnDvd)
    have h17 : (17 : ℕ) ^ 2 ≡ 1 [MOD 3] := by decide
    have h4 : (4 : ℕ) ^ 2 ≡ 1 [MOD 3] := by decide
    have hsum : 17 ^ (k + k) + 4 ^ (k + k) ≡ 2 [MOD 3] := by
      rw [← two_mul, pow_mul, pow_mul]
      simpa only [one_pow, one_add_one_eq_two] using (h17.pow k).add (h4.pow k)
    exact (by decide : ¬ (2 ≡ 0 [MOD 3])) (hsum.symm.trans hmod)
  have hn2 : 2 ≤ n := by
    have hn0 := hodd.pos
    by_contra! hsmall
    have e : n = 1 := by omega
    subst n
    norm_num at hnPrime
  by_contra hnNotPrime
  obtain ⟨d, ⟨e, he⟩, hd, hdn⟩ := Nat.exists_dvd_of_not_prime2 hn2 hnNotPrime
  have ⟨hdOdd, heOdd⟩ : Odd d ∧ Odd e := by rwa [he, Nat.odd_mul] at hodd
  have hdiv₁ : 21 ∣ 17 ^ d + 4 ^ d := hdOdd.nat_add_dvd_pow_add_pow 17 4
  have hdiv₂ : 17 ^ d + 4 ^ d ∣ 17 ^ n + 4 ^ n := by
    rw [he, pow_mul, pow_mul]
    exact heOdd.nat_add_dvd_pow_add_pow _ _
  have hs : 17 ^ d + 4 ^ d < 17 ^ n + 4 ^ n :=
    Nat.add_lt_add (Nat.pow_lt_pow_right (by decide) hdn)
      (Nat.pow_lt_pow_right (by decide) hdn)
  have hlarge : (17 : ℕ) ^ 2 ≤ 17 ^ d := Nat.pow_le_pow_right (by decide) hd
  have hlow : 21 < 17 ^ d + 4 ^ d :=
    (by decide : 21 < (17 : ℕ) ^ 2).trans_le (hlarge.trans (Nat.le_add_right _ _))
  have hscaled₁ : (17 ^ d + 4 ^ d) / 21 * 21 = 17 ^ d + 4 ^ d := Nat.div_mul_cancel hdiv₁
  have hscaled₂ : (17 ^ n + 4 ^ n) / 21 * 21 = 17 ^ n + 4 ^ n := Nat.div_mul_cancel hnDvd
  exact Nat.not_prime_of_dvd_of_lt (Nat.div_dvd_div hdiv₁ hdiv₂)
    (by omega) (by omega) hnPrime
