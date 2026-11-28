import OMAStatements.S_oeis_a173039
import Mathlib

/-!
`1/4 - 1/n^2 = (n^2 - 4)/(4 n^2)`. In lowest terms the numerator is `n^2 - 4` for odd `n`,
`4 s^2 - 1` for `n = 4 s` (this also matches the convention at `n = 0`) and the even number
`s (s + 1)` for `n = 4 s + 2`. Hence `IsOddNum m ↔ m % 4 ≠ 0`, the `j`-th such `m` is
`j + j / 3 + 1`, and on each residue class of `k` mod 3 the value `a k` is a quadratic polynomial
in `k / 3`. A vanishing third difference gives the recurrence, which gives the generating function
since `(X - 1)^3 (1 + X + X^2)^3 = (X^3 - 1)^3`.
-/

namespace R173039
open OMA.S_oeis_a173039 PowerSeries

theorem num_eq (n p q : ℤ) (hn : n ≠ 0) (hq : 0 < q) (hc : IsCoprime p q)
    (he : (1 / 4 : ℚ) - 1 / (n : ℚ) ^ 2 = (p : ℚ) / (q : ℚ)) : num n = p := by
  unfold num
  rw [if_neg hn, he]
  exact Rat.num_div_eq_of_coprime hq (Int.isCoprime_iff_gcd_eq_one.mp hc)

theorem key (x : ℚ) (hx : x ≠ 0) : 1 / 4 - 1 / x ^ 2 = (x ^ 2 - 4) / (4 * x ^ 2) := by
  rw [div_sub_div _ _ (by norm_num) (pow_ne_zero 2 hx)]
  ring

theorem num_odd (n : ℤ) (h : n % 2 = 1) : num n = n ^ 2 - 4 := by
  have hn : n ≠ 0 := by omega
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hsq : 0 < n ^ 2 := lt_of_le_of_ne (sq_nonneg n) (Ne.symm (pow_ne_zero 2 hn))
  have hcop : IsCoprime (n ^ 2 - 4) (4 * n ^ 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    exact ⟨(k ^ 2 + k) - (2 * k + 1) ^ 2 * (k ^ 2 + k - 1), (k ^ 2 + k - 1) ^ 2, by ring⟩
  refine num_eq n (n ^ 2 - 4) (4 * n ^ 2) hn (mul_pos (by norm_num) hsq) hcop ?_
  push_cast
  exact key _ hnq

theorem num_four (s : ℤ) : num (4 * s) = 4 * s ^ 2 - 1 := by
  by_cases hs : s = 0
  · subst hs
    unfold num
    norm_num
  · have hn : 4 * s ≠ 0 := by omega
    have hsq' : (s : ℚ) ≠ 0 := by exact_mod_cast hs
    have hsq : 0 < s ^ 2 := lt_of_le_of_ne (sq_nonneg s) (Ne.symm (pow_ne_zero 2 hs))
    have h4 : 4 * (s : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hsq'
    have hA : 4 * (4 * (s : ℚ)) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 h4)
    have hB : 16 * (s : ℚ) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hsq')
    refine num_eq (4 * s) (4 * s ^ 2 - 1) (16 * s ^ 2) hn (mul_pos (by norm_num) hsq)
      ⟨-(4 * s ^ 2 + 1), s ^ 2, by ring⟩ ?_
    push_cast
    exact (key (4 * (s : ℚ)) h4).trans ((div_eq_div_iff hA hB).mpr (by ring))

theorem num_two (s : ℤ) : num (4 * s + 2) = s * (s + 1) := by
  have hn : 4 * s + 2 ≠ 0 := by omega
  have h1 : 2 * s + 1 ≠ 0 := by omega
  have hq1 : (4 * (s : ℚ) + 2) ≠ 0 := by exact_mod_cast hn
  have hq2 : (2 * (s : ℚ) + 1) ≠ 0 := by exact_mod_cast h1
  have hA : 4 * (4 * (s : ℚ) + 2) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hq1)
  have hB : (2 * (s : ℚ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hq2
  refine num_eq (4 * s + 2) (s * (s + 1)) ((2 * s + 1) ^ 2) hn
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))) ⟨-4, 1, by ring⟩ ?_
  push_cast
  exact (key (4 * (s : ℚ) + 2) hq1).trans ((div_eq_div_iff hA hB).mpr (by ring))

theorem odd_iff (m : ℕ) : IsOddNum m ↔ m % 4 ≠ 0 := by
  unfold IsOddNum
  obtain ⟨q, r, hr, hm⟩ : ∃ q r, r < 4 ∧ m = 4 * q + r :=
    ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · rw [show (m : ℤ) - 2 = 4 * ((q : ℤ) - 1) + 2 by omega, num_two]
    exact iff_of_false (Int.not_odd_iff_even.mpr (Int.even_mul_succ_self _)) (by omega)
  · rw [show (m : ℤ) - 2 = 4 * (q : ℤ) - 1 by omega, num_odd (4 * (q : ℤ) - 1) (by omega)]
    exact iff_of_true ⟨8 * (q : ℤ) ^ 2 - 4 * q - 2, by ring⟩ (by omega)
  · rw [show (m : ℤ) - 2 = 4 * (q : ℤ) by omega, num_four]
    exact iff_of_true ⟨2 * (q : ℤ) ^ 2 - 1, by ring⟩ (by omega)
  · rw [show (m : ℤ) - 2 = 4 * (q : ℤ) + 1 by omega, num_odd (4 * (q : ℤ) + 1) (by omega)]
    exact iff_of_true ⟨8 * (q : ℤ) ^ 2 + 4 * q - 2, by ring⟩ (by omega)

theorem count_eq (n : ℕ) : Nat.count (fun m => m % 4 ≠ 0) n = n - (n + 3) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, ih]
    split_ifs with h <;> omega

theorem nth_eq (j : ℕ) : Nat.nth IsOddNum j = j + j / 3 + 1 := by
  have hp : IsOddNum = fun m => m % 4 ≠ 0 := funext fun m => propext (odd_iff m)
  have h1 : (j + j / 3 + 1) % 4 ≠ 0 := by omega
  have h2 : Nat.count (fun m => m % 4 ≠ 0) (j + j / 3 + 1) = j := by
    rw [count_eq]
    omega
  have h3 := Nat.nth_count (p := fun m => m % 4 ≠ 0) h1
  rw [h2] at h3
  rw [hp]
  exact h3

theorem a_r0 (k t : ℕ) (h : k = 3 * t + 1) : a k = (4 * (t : ℤ) - 1) ^ 2 - 4 := by
  have e : ((Nat.nth IsOddNum (k - 1) : ℕ) : ℤ) - 2 = 4 * (t : ℤ) - 1 := by
    rw [nth_eq]
    omega
  unfold a
  rw [e]
  exact num_odd (4 * (t : ℤ) - 1) (by omega)

theorem a_r1 (k t : ℕ) (h : k = 3 * t + 2) : a k = 4 * (t : ℤ) ^ 2 - 1 := by
  have e : ((Nat.nth IsOddNum (k - 1) : ℕ) : ℤ) - 2 = 4 * (t : ℤ) := by
    rw [nth_eq]
    omega
  unfold a
  rw [e]
  exact num_four (t : ℤ)

theorem a_r2 (k t : ℕ) (h : k = 3 * t + 3) : a k = (4 * (t : ℤ) + 1) ^ 2 - 4 := by
  have e : ((Nat.nth IsOddNum (k - 1) : ℕ) : ℤ) - 2 = 4 * (t : ℤ) + 1 := by
    rw [nth_eq]
    omega
  unfold a
  rw [e]
  exact num_odd (4 * (t : ℤ) + 1) (by omega)

theorem rec_main (n : ℕ) (hn : 10 ≤ n) : a n = 3 * a (n - 3) - 3 * a (n - 6) + a (n - 9) := by
  obtain ⟨t, r, hr, hnt⟩ : ∃ t r, r < 3 ∧ n = 3 * t + r + 10 :=
    ⟨(n - 10) / 3, (n - 10) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · rw [a_r0 n (t + 3) (by omega), a_r0 (n - 3) (t + 2) (by omega),
      a_r0 (n - 6) (t + 1) (by omega), a_r0 (n - 9) t (by omega)]
    push_cast
    ring
  · rw [a_r1 n (t + 3) (by omega), a_r1 (n - 3) (t + 2) (by omega),
      a_r1 (n - 6) (t + 1) (by omega), a_r1 (n - 9) t (by omega)]
    push_cast
    ring
  · rw [a_r2 n (t + 3) (by omega), a_r2 (n - 3) (t + 2) (by omega),
      a_r2 (n - 6) (t + 1) (by omega), a_r2 (n - 9) t (by omega)]
    push_cast
    ring

theorem v1 : a 1 = -3 := by rw [a_r0 1 0 (by norm_num)]; norm_num
theorem v2 : a 2 = -1 := by rw [a_r1 2 0 (by norm_num)]; norm_num
theorem v3 : a 3 = -3 := by rw [a_r2 3 0 (by norm_num)]; norm_num
theorem v4 : a 4 = 5 := by rw [a_r0 4 1 (by norm_num)]; norm_num
theorem v5 : a 5 = 3 := by rw [a_r1 5 1 (by norm_num)]; norm_num
theorem v6 : a 6 = 21 := by rw [a_r2 6 1 (by norm_num)]; norm_num
theorem v7 : a 7 = 45 := by rw [a_r0 7 2 (by norm_num)]; norm_num
theorem v8 : a 8 = 15 := by rw [a_r1 8 2 (by norm_num)]; norm_num
theorem v9 : a 9 = 77 := by rw [a_r2 9 2 (by norm_num)]; norm_num

theorem series :
    PowerSeries.mk (fun k => a (k + 1)) * ((X - 1) ^ 3 * (1 + X + X ^ 2) ^ 3) =
      (3 + X + 3 * X ^ 2 - 14 * X ^ 3 - 6 * X ^ 4 - 30 * X ^ 5 - 21 * X ^ 6 - 3 * X ^ 7
        - 5 * X ^ 8 : PowerSeries ℤ) := by
  have e1 : PowerSeries.mk (fun k => a (k + 1)) * ((X - 1) ^ 3 * (1 + X + X ^ 2) ^ 3) =
      PowerSeries.mk (fun k => a (k + 1)) * X ^ 9
        - C 3 * (PowerSeries.mk (fun k => a (k + 1)) * X ^ 6)
        + C 3 * (PowerSeries.mk (fun k => a (k + 1)) * X ^ 3)
        - PowerSeries.mk (fun k => a (k + 1)) := by
    simp only [map_ofNat]
    ring
  have e2 : (3 + X + 3 * X ^ 2 - 14 * X ^ 3 - 6 * X ^ 4 - 30 * X ^ 5 - 21 * X ^ 6 - 3 * X ^ 7
        - 5 * X ^ 8 : PowerSeries ℤ) = C 3 + X ^ 1 + C 3 * X ^ 2 - C 14 * X ^ 3 - C 6 * X ^ 4
        - C 30 * X ^ 5 - C 21 * X ^ 6 - C 3 * X ^ 7 - C 5 * X ^ 8 := by
    simp only [map_ofNat, pow_one]
    try ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_C, coeff_C_mul_X_pow, coeff_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · have hr := rec_main (n + 1) (by omega)
    rw [show n + 1 - 3 = n - 3 + 1 by omega, show n + 1 - 6 = n - 6 + 1 by omega,
      show n + 1 - 9 = n - 9 + 1 by omega] at hr
    rw [if_pos (show 9 ≤ n by omega), if_pos (show 6 ≤ n by omega), if_pos (show 3 ≤ n by omega),
      if_neg (show ¬ (n = 0) by omega), if_neg (show ¬ (n = 1) by omega),
      if_neg (show ¬ (n = 2) by omega), if_neg (show ¬ (n = 3) by omega),
      if_neg (show ¬ (n = 4) by omega), if_neg (show ¬ (n = 5) by omega),
      if_neg (show ¬ (n = 6) by omega), if_neg (show ¬ (n = 7) by omega),
      if_neg (show ¬ (n = 8) by omega)]
    linarith

end R173039

theorem OMA.solution : type_of% @OMA.S_oeis_a173039.main := by
  exact ⟨R173039.rec_main, R173039.series⟩
