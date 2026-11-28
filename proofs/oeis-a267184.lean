import OMAStatements.S_oeis_a267184
import Mathlib

open OMA.S_oeis_a267184
open PowerSeries

namespace P267184

theorem T_sub (i j : ℕ) (hi : 0 < i) (h : i < j) : T i j = T i (j - i) + 1 := by
  rw [T, dif_neg (by omega), dif_neg (by omega)]

theorem step (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + 1 := by
  rw [a, a, T_sub 4 (n + 4) (by norm_num) (by omega), Nat.add_sub_cancel]

theorem recur (n : ℕ) (hn : 5 < n) : (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 5 = m + 1 by omega]
  have h1 := step (m + 2) (by omega)
  have h2 := step (m + 1) (by omega)
  rw [show m + 2 + 4 = m + 6 by omega] at h1
  rw [show m + 1 + 4 = m + 5 by omega] at h2
  rw [h1, h2]; push_cast; ring

theorem v0 : a 0 = 1 := by simp [a, T]
theorem v1 : a 1 = 4 := by simp [a, T]
theorem v2 : a 2 = 2 := by simp [a, T]
theorem v3 : a 3 = 5 := by simp [a, T]
theorem v4 : a 4 = 0 := by simp [a, T]

open PowerSeries in
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
      (1 + 3 * X - 2 * X ^ 2 + 3 * X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℤ) := by
  have v5 : a 5 = 5 := by simp [a, T]
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) = F + (-1 : ℤ) • (F * X ^ 1) + (-1 : ℤ) • (F * X ^ 4) + (1 : ℤ) • (F * X ^ 5) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 3 * X - 2 * X ^ 2 + 3 * X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (3 : ℤ) • X ^ 1 + (-2 : ℤ) • X ^ 2 + (3 : ℤ) • X ^ 3 + (-6 : ℤ) • X ^ 4 + (2 : ℤ) • X ^ 5 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 5 < n
  · have hr := recur n h
    simp only [show 1 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]

theorem c1 (q : ℕ) : a (4 * q + 1) = q + 4 := by
  induction q with
  | zero => exact v1
  | succ q ih => rw [show 4 * (q + 1) + 1 = 4 * q + 1 + 4 by ring, step _ (by omega), ih]
theorem c2 (q : ℕ) : a (4 * q + 2) = q + 2 := by
  induction q with
  | zero => exact v2
  | succ q ih => rw [show 4 * (q + 1) + 2 = 4 * q + 2 + 4 by ring, step _ (by omega), ih]
theorem c3 (q : ℕ) : a (4 * q + 3) = q + 5 := by
  induction q with
  | zero => exact v3
  | succ q ih => rw [show 4 * (q + 1) + 3 = 4 * q + 3 + 4 by ring, step _ (by omega), ih]
theorem c4 (q : ℕ) : a (4 * q + 4) = q := by
  induction q with
  | zero => exact v4
  | succ q ih => rw [show 4 * (q + 1) + 4 = 4 * q + 4 + 4 by ring, step _ (by omega), ih]

theorem fne (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n

open PowerSeries in
theorem egf : 4 * mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      8 - 5 * cos ℚ + (1 + X) * cosh - sin ℚ + (16 + X) * sinh := by
  have e : (8 - 5 * cos ℚ + (1 + X) * cosh - sin ℚ + (16 + X) * sinh : PowerSeries ℚ) =
      C (8 : ℚ) - C (5 : ℚ) * cos ℚ + cosh + X * cosh - sin ℚ + C (16 : ℚ) * sinh + X * sinh := by
    simp only [map_ofNat]; ring
  have e4 : (4 : PowerSeries ℚ) = C (4 : ℚ) := by simp only [map_ofNat]
  rw [e, e4]
  ext n
  rcases n with _ | m
  · simp [coeff_C, cos, sin, cosh, sinh, v0]
    norm_num
  · simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_succ_X_mul, coeff_mk, cos, sin, cosh,
      sinh, if_neg (Nat.succ_ne_zero m)]
    rw [Nat.factorial_succ]
    have hm := fne m
    obtain ⟨q, hq⟩ : ∃ q, m = 4 * q ∨ m = 4 * q + 1 ∨ m = 4 * q + 2 ∨ m = 4 * q + 3 :=
      ⟨m / 4, by omega⟩
    rcases hq with rfl | rfl | rfl | rfl
    · have p1 : ¬ Even (4 * q + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨2 * q, by ring⟩
      have p0 : Even (4 * q) := ⟨2 * q, by ring⟩
      have d : (4 * q + 1) / 2 = 2 * q := by omega
      simp only [p1, p0, if_true, if_false, not_false_eq_true, not_true_eq_false]
      rw [d, c1, pow_mul]
      push_cast; norm_num
      field_simp; ring
    · have p1 : Even (4 * q + 1 + 1) := ⟨2 * q + 1, by ring⟩
      have p0 : ¬ Even (4 * q + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨2 * q, by ring⟩
      have d : (4 * q + 1 + 1) / 2 = 2 * q + 1 := by omega
      simp only [p1, p0, if_true, if_false, not_false_eq_true, not_true_eq_false]
      rw [d, show 4 * q + 1 + 1 = 4 * q + 2 by ring, c2,
        pow_succ, pow_mul]
      push_cast; norm_num
      field_simp; ring
    · have p1 : ¬ Even (4 * q + 2 + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨2 * q + 1, by ring⟩
      have p0 : Even (4 * q + 2) := ⟨2 * q + 1, by ring⟩
      have d : (4 * q + 2 + 1) / 2 = 2 * q + 1 := by omega
      simp only [p1, p0, if_true, if_false, not_false_eq_true, not_true_eq_false]
      rw [d, show 4 * q + 2 + 1 = 4 * q + 3 by ring, c3,
        pow_succ, pow_mul]
      push_cast; norm_num
      field_simp; ring
    · have p1 : Even (4 * q + 3 + 1) := ⟨2 * q + 2, by ring⟩
      have p0 : ¬ Even (4 * q + 3) := by rw [Nat.not_even_iff_odd]; exact ⟨2 * q + 1, by ring⟩
      have d : (4 * q + 3 + 1) / 2 = 2 * (q + 1) := by omega
      simp only [p1, p0, if_true, if_false, not_false_eq_true, not_true_eq_false]
      rw [d, show 4 * q + 3 + 1 = 4 * q + 4 by ring, c4,
        pow_mul]
      push_cast; norm_num
      field_simp; ring

end P267184

theorem OMA.solution : type_of% @OMA.S_oeis_a267184.main := ⟨P267184.recur, P267184.gf, P267184.egf⟩
