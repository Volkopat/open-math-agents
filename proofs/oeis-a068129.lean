import OMAStatements.S_oeis_a068129

-- Disproof at T = 1. A number with decimal digit sum 1 is a power of 10, and 10^j is
-- triangular only for j = 0, 1: if m(m+1) = 2 * 10^j = 2^(j+1) * 5^j with j >= 2, the
-- coprime factors m and m+1 split 2^(j+1) and 5^j, which forces 5^j = 2^(j+1) + 1 or
-- m + 1 <= 2^(j+1) < 5^j <= m, both impossible. So only 1 and 10 are triangular numbers with
-- digit sum 1, a finite set.

namespace OMA.P12_a068129

theorem digitSum_zero : ∀ k : ℕ, (Nat.digits 10 k).sum = 0 → k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hs
    rcases Nat.eq_zero_or_pos k with h0 | hk
    · exact h0
    · rw [Nat.digits_def' (by norm_num) hk, List.sum_cons] at hs
      have h1 : k / 10 = 0 := ih (k / 10) (Nat.div_lt_self hk (by norm_num)) (by omega)
      omega

theorem digitSum_one : ∀ k : ℕ, (Nat.digits 10 k).sum = 1 → ∃ j : ℕ, k = 10 ^ j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hs
    rcases Nat.eq_zero_or_pos k with h0 | hk
    · subst h0
      simp at hs
    · rw [Nat.digits_def' (by norm_num) hk, List.sum_cons] at hs
      have hlt : k / 10 < k := Nat.div_lt_self hk (by norm_num)
      by_cases hr : k % 10 = 1
      · have h1 : k / 10 = 0 := digitSum_zero (k / 10) (by omega)
        exact ⟨0, by rw [pow_zero]; omega⟩
      · obtain ⟨j, hj⟩ := ih (k / 10) hlt (by omega)
        refine ⟨j + 1, ?_⟩
        rw [pow_succ]
        omega

theorem pow_ineq1 : ∀ j : ℕ, 1 ≤ j → 2 ^ (j + 1) < 5 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ 5]
    omega

theorem pow_ineq2 : ∀ j : ℕ, 2 ≤ j → 2 ^ (j + 1) + 1 < 5 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ 5]
    omega

theorem not_tri_pow (j m : ℕ) (hj : 2 ≤ j) : m * (m + 1) ≠ 2 * 10 ^ j := by
  intro h
  have h10 : 2 * 10 ^ j = 2 ^ (j + 1) * 5 ^ j := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow, pow_succ]
    ring
  rw [h10] at h
  have i1 := pow_ineq1 j (by omega)
  have i2 := pow_ineq2 j hj
  have hA : 0 < 2 ^ (j + 1) := by positivity
  have hB : 0 < 5 ^ j := by positivity
  have hcop : Nat.Coprime m (m + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exfalso
      have hp : 0 < 2 ^ (j + 1) * 5 ^ j := by positivity
      rw [← h] at hp
      simp at hp
    · exact h0
  have hd5 : 5 ^ j ∣ m * (m + 1) := ⟨2 ^ (j + 1), by rw [h]; ring⟩
  have hd2 : 2 ^ (j + 1) ∣ m * (m + 1) := ⟨5 ^ j, by rw [h]⟩
  have h5 : 5 ^ j ∣ m ∨ 5 ^ j ∣ m + 1 := by
    by_cases h5m : 5 ∣ m
    · left
      have hn : ¬ 5 ∣ m + 1 := by
        intro h5m1
        have := Nat.dvd_gcd h5m h5m1
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        omega
      have hc : Nat.Coprime (5 ^ j) (m + 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn)
      exact hc.dvd_of_dvd_mul_right hd5
    · right
      have hc : Nat.Coprime (5 ^ j) m :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5m)
      exact hc.dvd_of_dvd_mul_left hd5
  have h2 : 2 ^ (j + 1) ∣ m ∨ 2 ^ (j + 1) ∣ m + 1 := by
    by_cases h2m : 2 ∣ m
    · left
      have hn : ¬ 2 ∣ m + 1 := by
        intro h2m1
        have := Nat.dvd_gcd h2m h2m1
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        omega
      have hc : Nat.Coprime (2 ^ (j + 1)) (m + 1) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn)
      exact hc.dvd_of_dvd_mul_right hd2
    · right
      have hc : Nat.Coprime (2 ^ (j + 1)) m :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h2m)
      exact hc.dvd_of_dvd_mul_left hd2
  have hc25 : Nat.Coprime (2 ^ (j + 1)) (5 ^ j) :=
    Nat.Coprime.pow _ _ (by norm_num)
  generalize 2 ^ (j + 1) = A at h i1 i2 hA hd2 h2 hc25
  generalize 5 ^ j = B at h i1 i2 hB hd5 h5 hc25
  rcases h5 with h5 | h5 <;> rcases h2 with h2 | h2
  · have hAB : A * B ∣ m := hc25.mul_dvd_of_dvd_of_dvd h2 h5
    have := Nat.le_of_dvd hm0 hAB
    nlinarith
  · have hm : B ≤ m := Nat.le_of_dvd hm0 h5
    have hle : (m + 1) * B ≤ A * B := by nlinarith
    have := Nat.le_of_mul_le_mul_right hle hB
    omega
  · have hm : A ≤ m := Nat.le_of_dvd hm0 h2
    have hm1 : B ≤ m + 1 := Nat.le_of_dvd (by omega) h5
    have hle : A * (m + 1) ≤ A * B := by nlinarith
    have hm1' : m + 1 ≤ B := Nat.le_of_mul_le_mul_left hle hA
    have heq : m + 1 = B := le_antisymm hm1' hm1
    subst heq
    have : m = A := Nat.eq_of_mul_eq_mul_right (by omega : 0 < m + 1) h
    omega
  · have hAB : A * B ∣ m + 1 := hc25.mul_dvd_of_dvd_of_dvd h2 h5
    have := Nat.le_of_dvd (by omega) hAB
    nlinarith

end OMA.P12_a068129

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068129.main) := by
  intro h
  have hinf := h 1 le_rfl ⟨1, by norm_num⟩
  apply hinf
  apply (Set.finite_le_nat 10).subset
  rintro k ⟨⟨m, rfl⟩, hs⟩
  show m * (m + 1) / 2 ≤ 10
  obtain ⟨j, hj⟩ := OMA.P12_a068129.digitSum_one _ hs
  by_contra hc
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push_neg at hlt
    interval_cases j <;> simp at hj <;> omega
  have hev : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)
  exact OMA.P12_a068129.not_tri_pow j m hj2 (by rw [← hev, hj])
