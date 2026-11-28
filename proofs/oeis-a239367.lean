import OMAStatements.S_oeis_a239367
import Mathlib

open OMA.S_oeis_a239367
open PowerSeries

namespace P239367

theorem b_closed (n : ℕ) (hn : 1 ≤ n) :
    108 * b n = 36 * (n : ℤ) ^ 2 + 48 * n + 8 + 27 * 2 ^ n + 19 * (-2) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => norm_num [b]
    | m + 2, _ =>
      rw [b]
      have h := ih (m + 1) (by omega) (by omega)
      push_cast at h ⊢
      rw [pow_succ, pow_succ (2 : ℤ) (m + 1), pow_succ (-2 : ℤ) (m + 1)] at *
      linear_combination (-2 : ℤ) * h

theorem closed (n : ℕ) (hn : 1 ≤ n) : 27 * a n = -1 + 4 ^ n - 12 * n + 36 * (n : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := b_closed (2 * m + 1) (by omega)
  rw [a, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  have e1 : (2 : ℤ) ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; try ring
  have e2 : (-2 : ℤ) ^ (2 * m + 1) = -2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; try ring
  rw [e1, e2] at h
  push_cast at h ⊢
  have h4 : (4 : ℤ) * (27 * b (2 * m + 1) - (-1 + 4 ^ (m + 1) - 12 * ((m : ℤ) + 1) + 36 * ((m : ℤ) + 1) ^ 2)) = 0 := by
    rw [pow_succ]; linear_combination h
  have := (mul_eq_zero.mp h4).resolve_left (by norm_num)
  linarith

theorem recur (n : ℕ) (hn : 6 ≤ n) :
    a n = 6 * a (n - 1) - 8 * a (n - 2) - 2 * a (n - 3) + 9 * a (n - 4) - 4 * a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  have h0 := closed (m + 6) (by omega)
  have h1 := closed (m + 5) (by omega)
  have h2 := closed (m + 4) (by omega)
  have h3 := closed (m + 3) (by omega)
  have h4 := closed (m + 2) (by omega)
  have h5 := closed (m + 1) (by omega)
  simp only [pow_succ] at h0 h1 h2 h3 h4 h5
  push_cast at h0 h1 h2 h3 h4 h5
  have : (27 : ℤ) * (a (m + 6) - (6 * a (m + 5) - 8 * a (m + 4) - 2 * a (m + 3) + 9 * a (m + 2) - 4 * a (m + 1))) = 0 := by
    linear_combination h0 - 6 * h1 + 8 * h2 + 2 * h3 - 9 * h4 + 4 * h5
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

theorem recur4 (n : ℕ) (hn : 5 ≤ n) :
    a n = 7 * a (n - 1) - 15 * a (n - 2) + 13 * a (n - 3) - 4 * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  have h0 := closed (m + 5) (by omega)
  have h1 := closed (m + 4) (by omega)
  have h2 := closed (m + 3) (by omega)
  have h3 := closed (m + 2) (by omega)
  have h4 := closed (m + 1) (by omega)
  simp only [pow_succ] at h0 h1 h2 h3 h4
  push_cast at h0 h1 h2 h3 h4
  have : (27 : ℤ) * (a (m + 5) - (7 * a (m + 4) - 15 * a (m + 3) + 13 * a (m + 2) - 4 * a (m + 1))) = 0 := by
    linear_combination h0 - 7 * h1 + 15 * h2 - 13 * h3 + 4 * h4
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

open PowerSeries in
theorem gf : mk (fun n => if n = 0 then 0 else a n) * ((X - 1) ^ 3 * (4 * X - 1)) =
      (-X * (7 * X ^ 2 + 2 * X - 1) : PowerSeries ℤ) := by
  have v1 : a 1 = 1 := by decide
  have v2 : a 2 = 5 := by decide
  have v3 : a 3 = 13 := by decide
  have v4 : a 4 = 29 := by decide
  set F : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else a n) with hF
  have product : F * ((X - 1) ^ 3 * (4 * X - 1)) = F + (-7 : ℤ) • (F * X) + (15 : ℤ) • (F * X ^ 2) + (-13 : ℤ) • (F * X ^ 3) + (4 : ℤ) • (F * X ^ 4) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (-X * (7 * X ^ 2 + 2 * X - 1) : PowerSeries ℤ) = (1 : ℤ) • X ^ 1 + (-2 : ℤ) • X ^ 2 + (-7 : ℤ) • X ^ 3 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs, ← pow_one (F * X)]
  rw [show (F * X) ^ 1 = F * X ^ 1 by ring]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := recur4 n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v1, v2, v3, v4]

end P239367

theorem OMA.solution : type_of% @OMA.S_oeis_a239367.main :=
  ⟨P239367.closed, P239367.recur, P239367.gf⟩
