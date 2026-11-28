import OMAStatements.S_oeis_a267185
import Mathlib

open OMA.S_oeis_a267185
open PowerSeries

namespace P267185

theorem T_sub (i j : ℕ) (hi : 0 < i) (h : i < j) : T i j = T i (j - i) + 1 := by
  rw [T, dif_neg (by omega), dif_neg (by omega)]

theorem T_swap (i j : ℕ) (h : j < i) : T i j = T j i + 1 := by
  rw [T, dif_neg (by omega), dif_pos h]

theorem r_odd (q : ℕ) : T 2 (2 * q + 1) = q + 2 := by
  induction q with
  | zero => simp [T]
  | succ q ih =>
    rw [T_sub 2 _ (by norm_num) (by omega), show 2 * (q + 1) + 1 - 2 = 2 * q + 1 by omega, ih]

theorem r_even (q : ℕ) : T 2 (2 * q + 2) = q := by
  induction q with
  | zero => simp [T]
  | succ q ih =>
    rw [T_sub 2 _ (by norm_num) (by omega), show 2 * (q + 1) + 2 - 2 = 2 * q + 2 by omega, ih]

theorem a_even (q : ℕ) (hq : 2 ≤ q) : a (2 * q) = q := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  rw [a, T_swap _ _ (by omega), show 2 * (p + 1) = 2 * p + 2 by ring, r_even]

theorem a_odd (q : ℕ) (hq : 1 ≤ q) : a (2 * q + 1) = q + 3 := by
  rw [a, T_swap _ _ (by omega), r_odd]

theorem closed (n : ℕ) (hn : 2 < n) : 4 * (a n : ℤ) = 2 * n - 5 * ((-1) ^ n - 1) := by
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · rw [a_even q (by omega), pow_mul]; norm_num; ring
  · rw [a_odd q (by omega), pow_succ, pow_mul]; push_cast; norm_num; ring

theorem ev (n : ℕ) (hn : 2 < n) (he : Even n) : a n = n / 2 := by
  obtain ⟨q, rfl⟩ := he
  rw [← two_mul, a_even q (by omega)]; omega

theorem od (n : ℕ) (hn : 2 < n) (ho : Odd n) : a n = (n + 5) / 2 := by
  obtain ⟨q, rfl⟩ := ho
  rw [a_odd q (by omega)]; omega

theorem recur (n : ℕ) (hn : 5 < n) : (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3) := by
  have h0 := closed n (by omega)
  have h1 := closed (n - 1) (by omega)
  have h2 := closed (n - 2) (by omega)
  have h3 := closed (n - 3) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega] at h1 h2 h3 ⊢
  have p0 : (-1 : ℤ) ^ (m + 6) = (-1) ^ m := by rw [pow_add]; norm_num
  have p1 : (-1 : ℤ) ^ (m + 5) = -(-1) ^ m := by rw [pow_add]; norm_num
  have p2 : (-1 : ℤ) ^ (m + 4) = (-1) ^ m := by rw [pow_add]; norm_num
  have p3 : (-1 : ℤ) ^ (m + 3) = -(-1) ^ m := by rw [pow_add]; norm_num
  rw [p0] at h0; rw [p1] at h1; rw [p2] at h2; rw [p3] at h3
  push_cast at h0 h1 h2 h3
  have : (4 : ℤ) * ((a (m + 6) : ℤ) - (a (m + 5) + a (m + 4) - a (m + 3))) = 0 := by
    linear_combination h0 - h1 - h2 + h3
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

open PowerSeries in
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X)) =
      (X * (1 - X + 3 * X ^ 2 - X ^ 3 - X ^ 4) : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 2 * (1 + X)) = F + (-1 : ℤ) • (F * X ^ 1) + (-1 : ℤ) • (F * X ^ 2) + (1 : ℤ) • (F * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (X * (1 - X + 3 * X ^ 2 - X ^ 3 - X ^ 4) : PowerSeries ℤ) = (1 : ℤ) • X ^ 1 + (-1 : ℤ) • X ^ 2 + (3 : ℤ) • X ^ 3 + (-1 : ℤ) • X ^ 4 + (-1 : ℤ) • X ^ 5 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 5 < n
  · have hr := recur n h
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      if_true, if_false]
    linarith
  · interval_cases n <;> simp [a, T] <;> decide +kernel

end P267185

theorem OMA.solution : type_of% @OMA.S_oeis_a267185.main :=
  ⟨P267185.closed, P267185.ev, P267185.od, P267185.recur, P267185.gf⟩
