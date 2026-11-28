import OMAStatements.S_oeis_a309263

/-!
# A309263: every `4 * 5 ^ n` has consecutive cancelled ratios

`ConsecutiveRatios N` says: for consecutive divisors `a < b` of `N` there are `g`, `t` with
`a = g * t` and `b = g * (t + 1)` — the ratio `a/b` cancels to `t/(t+1)`.

Divisors of `4 * 5 ^ n` are exactly the `2^i * 5^j` with `i ≤ 2`, `j ≤ n`, and the sorted chain
is `5^j, 2*5^j, 4*5^j, 5^(j+1), ...`.  So the consecutive pairs are `(2^i 5^j, 2^(i+1) 5^j)` for
`i ≤ 1`, with `g = 2^i 5^j`, `t = 1`, and `(4*5^j, 5^(j+1))`, with `g = 5^j`, `t = 4`.
Separately `3 ∤ 4 * 5 ^ n`, so `6 ∤ 4 * 5 ^ n`.
-/

namespace OMA

open OMA.S_oeis_a309263

private lemma prime_three : Nat.Prime 3 := by norm_num
private lemma prime_five : Nat.Prime 5 := by norm_num
private lemma five_pos (j : ℕ) : 0 < 5 ^ j := pow_pos (by norm_num) j

private lemma two_pow_le_four {i : ℕ} (hi : i ≤ 2) : 2 ^ i ≤ 4 := by
  calc 2 ^ i ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hi
    _ = 4 := by norm_num

/-- `3` does not divide `4 * 5 ^ n`. -/
private lemma three_not_dvd (n : ℕ) : ¬ (3 ∣ 4 * 5 ^ n) := by
  intro h
  rcases prime_three.dvd_mul.mp h with h4 | h5
  · norm_num at h4
  · have h5' : 3 ∣ 5 := prime_three.dvd_of_dvd_pow h5
    norm_num at h5'

private lemma six_not_dvd (n : ℕ) : ¬ (6 ∣ 4 * 5 ^ n) := by
  intro h
  exact three_not_dvd n (Nat.dvd_trans (by norm_num) h)

/-- Every divisor of `4 * 5 ^ n` is `2^i * 5^j` with `i ≤ 2` and `j ≤ n`. -/
private lemma dvd_shape : ∀ (n d : ℕ), d ∣ 4 * 5 ^ n →
    ∃ i : ℕ, i ≤ 2 ∧ ∃ j : ℕ, j ≤ n ∧ d = 2 ^ i * 5 ^ j := by
  intro n
  induction n with
  | zero =>
    intro d hd
    have hd4 : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d
    · norm_num at hd
    · exact ⟨0, by norm_num, 0, le_refl 0, by norm_num⟩
    · exact ⟨1, by norm_num, 0, le_refl 0, by norm_num⟩
    · norm_num at hd
    · exact ⟨2, by norm_num, 0, le_refl 0, by norm_num⟩
  | succ n ih =>
    intro d hd
    have hd5 : d ∣ 5 * (4 * 5 ^ n) := by
      have h : 4 * 5 ^ (n + 1) = 5 * (4 * 5 ^ n) := by ring
      rwa [h] at hd
    by_cases h5 : 5 ∣ d
    · have hsplit : d / 5 ∣ 4 * 5 ^ n := by
        have hmul : d = 5 * (d / 5) := (Nat.mul_div_cancel' h5).symm
        rw [hmul] at hd5
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).mp hd5
      obtain ⟨i, hi, j, hj, hdj⟩ := ih (d / 5) hsplit
      refine ⟨i, hi, j + 1, by omega, ?_⟩
      calc d = 5 * (d / 5) := (Nat.mul_div_cancel' h5).symm
        _ = 5 * (2 ^ i * 5 ^ j) := by rw [hdj]
        _ = 2 ^ i * 5 ^ (j + 1) := by rw [pow_succ]; ring
    · have hcop : Nat.Coprime d 5 := (prime_five.coprime_iff_not_dvd.mpr h5).symm
      have hd' : d ∣ 4 * 5 ^ n := hcop.dvd_of_dvd_mul_left hd5
      obtain ⟨i, hi, j, hj, hdj⟩ := ih d hd'
      exact ⟨i, hi, j, by omega, hdj⟩

/-- The shape `2^i * 5^j` divides `4 * 5 ^ n` when the exponents are in range. -/
private lemma shape_dvd (i j n : ℕ) (hi : i ≤ 2) (hj : j ≤ n) : 2 ^ i * 5 ^ j ∣ 4 * 5 ^ n := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 hi) (pow_dvd_pow 5 hj)

/-- For `j >= 1`, `4 * 5^(j-1) < 5^j`. -/
private lemma four_pow_pred_lt (j : ℕ) (hj : 1 ≤ j) : 4 * 5 ^ (j - 1) < 5 ^ j := by
  have h : 5 ^ j = 5 ^ (j - 1) * 5 := by
    conv_lhs => rw [show j = (j - 1) + 1 from (Nat.sub_one_add_one (by omega : j ≠ 0)).symm]
    rw [pow_succ]
  rw [h]
  nlinarith [five_pos (j - 1)]

/-- A larger divisor has the larger five-part: `j ≤ j'`. -/
private lemma j_le_of_lt {i j i' j' : ℕ} (hi' : i' ≤ 2)
    (hlt : 2 ^ i * 5 ^ j < 2 ^ i' * 5 ^ j') : j ≤ j' := by
  by_contra h
  have hj1 : 1 ≤ j := by omega
  have hb : 2 ^ i' * 5 ^ j' ≤ 4 * 5 ^ (j - 1) := by
    have h1 : 2 ^ i' * 5 ^ j' ≤ 4 * 5 ^ j' := Nat.mul_le_mul_right _ (two_pow_le_four hi')
    have h2 : (4 : ℕ) * 5 ^ j' ≤ 4 * 5 ^ (j - 1) :=
      Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by norm_num) (by omega))
    exact le_trans h1 h2
  have h3 : 4 * 5 ^ (j - 1) < 5 ^ j := four_pow_pred_lt j hj1
  have h4 : 5 ^ j ≤ 2 ^ i * 5 ^ j := by
    have h1 : (1 : ℕ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    calc 5 ^ j = 1 * 5 ^ j := (one_mul _).symm
      _ ≤ 2 ^ i * 5 ^ j := Nat.mul_le_mul_right _ h1
  have h5 : 2 ^ i * 5 ^ j < 5 ^ j := lt_of_lt_of_le hlt (le_trans hb (le_of_lt h3))
  exact absurd h5 (not_lt.mpr h4)

/-- For `i ≤ 1` the successor of `2^i * 5^j` is `2^(i+1) * 5^j`: nothing lies between. -/
private lemma divisor_ge_double {i j i' j' : ℕ} (hi : i ≤ 1) (hi' : i' ≤ 2)
    (hlt : 2 ^ i * 5 ^ j < 2 ^ i' * 5 ^ j') :
    2 ^ (i + 1) * 5 ^ j ≤ 2 ^ i' * 5 ^ j' := by
  have hjj : j ≤ j' := j_le_of_lt hi' hlt
  by_cases hcase : i + 1 ≤ i'
  · calc 2 ^ (i + 1) * 5 ^ j ≤ 2 ^ i' * 5 ^ j :=
          Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by norm_num) hcase)
      _ ≤ 2 ^ i' * 5 ^ j' := Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by norm_num) hjj)
  · have hi'i : i' ≤ i := by omega
    have hjlt : j < j' := by
      by_contra hle
      have hje : j' = j := by omega
      have hle' : 2 ^ i' * 5 ^ j' ≤ 2 ^ i * 5 ^ j := by
        rw [hje]
        exact Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by norm_num) hi'i)
      exact absurd hlt (not_lt.mpr hle')
    have h4 : 2 ^ (i + 1) ≤ 5 := by
      have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl <;> norm_num
    calc 2 ^ (i + 1) * 5 ^ j ≤ 5 * 5 ^ j := Nat.mul_le_mul_right _ h4
      _ = 5 ^ (j + 1) := by rw [pow_succ]; ring
      _ ≤ 5 ^ j' := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ 2 ^ i' * 5 ^ j' := by
          have h1 : (1 : ℕ) ≤ 2 ^ i' := one_le_pow₀ (by norm_num)
          calc 5 ^ j' = 1 * 5 ^ j' := (one_mul _).symm
            _ ≤ 2 ^ i' * 5 ^ j' := Nat.mul_le_mul_right _ h1

/-- For `i = 2` the successor of `2^i * 5^j` is `5^(j+1)`. -/
private lemma divisor_ge_five {i j i' j' : ℕ} (hi : i = 2) (hi' : i' ≤ 2)
    (hlt : 2 ^ i * 5 ^ j < 2 ^ i' * 5 ^ j') : 5 ^ (j + 1) ≤ 2 ^ i' * 5 ^ j' := by
  have hjj : j ≤ j' := j_le_of_lt hi' hlt
  have hjne : j' ≠ j := by
    intro hje
    have hle' : 2 ^ i' * 5 ^ j' ≤ 2 ^ i * 5 ^ j := by
      rw [hje]
      exact Nat.mul_le_mul_right _ (by rw [hi]; simpa using two_pow_le_four hi')
    exact absurd hlt (not_lt.mpr hle')
  calc 5 ^ (j + 1) ≤ 5 ^ j' := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ 2 ^ i' * 5 ^ j' := by
        have h1 : (1 : ℕ) ≤ 2 ^ i' := one_le_pow₀ (by norm_num)
        calc 5 ^ j' = 1 * 5 ^ j' := (one_mul _).symm
          _ ≤ 2 ^ i' * 5 ^ j' := Nat.mul_le_mul_right _ h1

private lemma consecutive (n : ℕ) : ConsecutiveRatios (4 * 5 ^ n) := by
  intro a b ha hb hab hbetween
  obtain ⟨i, hi2, j, hjn, ha_eq⟩ := dvd_shape n a ha
  obtain ⟨i', hi2', j', hj'n, hb_eq⟩ := dvd_shape n b hb
  rw [ha_eq] at hab hbetween ⊢
  rw [hb_eq] at hab hbetween ⊢
  by_cases hi : i ≤ 1
  · have hdvd : 2 ^ (i + 1) * 5 ^ j ∣ 4 * 5 ^ n := shape_dvd (i + 1) j n (by omega) hjn
    have hgt : 2 ^ i * 5 ^ j < 2 ^ (i + 1) * 5 ^ j := by
      have h2 : 2 ^ i < 2 ^ (i + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      exact Nat.mul_lt_mul_of_pos_right h2 (five_pos j)
    have hge := divisor_ge_double hi hi2' hab
    have heq : 2 ^ i' * 5 ^ j' = 2 ^ (i + 1) * 5 ^ j := by
      by_contra hne
      exact hbetween _ hdvd hgt (lt_of_le_of_ne hge (Ne.symm hne))
    refine ⟨2 ^ i * 5 ^ j, 1, by ring, ?_⟩
    rw [heq, pow_succ]
    ring
  · have hi_eq : i = 2 := by omega
    have hjn' : j < n := by
      by_contra h
      have hble : 2 ^ i' * 5 ^ j' ≤ 4 * 5 ^ n := by
        calc 2 ^ i' * 5 ^ j' ≤ 4 * 5 ^ j' := Nat.mul_le_mul_right _ (two_pow_le_four hi2')
          _ ≤ 4 * 5 ^ n := Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by norm_num) hj'n)
      have hje : j = n := by omega
      rw [hi_eq, hje] at hab
      norm_num at hab
      omega
    have hdvd : 5 ^ (j + 1) ∣ 4 * 5 ^ n := by
      have h := shape_dvd 0 (j + 1) n (by norm_num) (by omega)
      simpa using h
    have hgt : 2 ^ i * 5 ^ j < 5 ^ (j + 1) := by
      rw [hi_eq, pow_succ]
      calc 2 ^ 2 * 5 ^ j = 4 * 5 ^ j := by norm_num
        _ < 5 * 5 ^ j := Nat.mul_lt_mul_of_pos_right (by norm_num) (five_pos j)
        _ = 5 ^ j * 5 := by ring
    have hge := divisor_ge_five hi_eq hi2' hab
    have heq : 2 ^ i' * 5 ^ j' = 5 ^ (j + 1) := by
      by_contra hne
      exact hbetween _ hdvd hgt (lt_of_le_of_ne hge (Ne.symm hne))
    refine ⟨5 ^ j, 4, ?_, ?_⟩
    · rw [hi_eq]
      ring
    · calc 2 ^ i' * 5 ^ j' = 5 ^ (j + 1) := heq
        _ = 5 ^ j * (4 + 1) := by norm_num [pow_succ]

private theorem key : ∀ n : ℕ, ¬6 ∣ 4 * 5 ^ n ∧ ConsecutiveRatios (4 * 5 ^ n) :=
  fun n => ⟨six_not_dvd n, consecutive n⟩

end OMA

open OMA.S_oeis_a309263

theorem OMA.solution : type_of% @OMA.S_oeis_a309263.main := OMA.key
