import OMAStatements.S_oeis_a267183
import Mathlib

open OMA.S_oeis_a267183
open PowerSeries

namespace P267183

theorem T_sub (i j : ℕ) (hi : 0 < i) (h : i < j) : T i j = T i (j - i) + 1 := by
  rw [T, dif_neg (by omega), dif_neg (by omega)]

theorem step (n : ℕ) (hn : 1 ≤ n) : a (n + 3) = a n + 1 := by
  rw [a, a, T_sub 3 (n + 3) (by norm_num) (by omega), Nat.add_sub_cancel]

theorem recur (n : ℕ) (hn : 4 < n) : (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  have h1 := step (m + 2) (by omega)
  have h2 := step (m + 1) (by omega)
  rw [show m + 2 + 3 = m + 5 by omega] at h1
  rw [show m + 1 + 3 = m + 4 by omega] at h2
  rw [h1, h2]; push_cast; ring

open PowerSeries in
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X + X ^ 2)) =
      (1 + 2 * X + X ^ 2 - 5 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 2 * (1 + X + X ^ 2)) = F + (-1 : ℤ) • (F * X ^ 1) + (-1 : ℤ) • (F * X ^ 3) + (1 : ℤ) • (F * X ^ 4) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 2 * X + X ^ 2 - 5 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (2 : ℤ) • X ^ 1 + (1 : ℤ) • X ^ 2 + (-5 : ℤ) • X ^ 3 + (2 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := recur n h
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      if_true, if_false]
    linarith
  · interval_cases n <;> simp [a, T] <;> decide +kernel

end P267183

theorem OMA.solution : type_of% @OMA.S_oeis_a267183.main := ⟨P267183.recur, P267183.gf⟩
