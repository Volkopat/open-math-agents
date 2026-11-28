import OMAStatements.S_oeis_a308215
import Mathlib

open OMA.S_oeis_a308215
open PowerSeries

namespace P308215

theorem inv_val (N A B k : ℕ) (hA : A < N) (h : A * B = N * k + 1) :
    (((B : ℕ) : ZMod N)⁻¹).val = A := by
  have h1 : ((B : ℕ) : ZMod N) * ((A : ℕ) : ZMod N) = 1 := by
    rw [← Nat.cast_mul, mul_comm, h]; simp
  rw [ZMod.inv_eq_of_mul_eq_one N _ _ h1, ZMod.val_natCast_of_lt hA]

theorem a_even (m : ℕ) (hm : 1 ≤ m) : a (2 * m) = 8 * m ^ 2 + 3 * m + 1 := by
  unfold a
  have e1 : cs (2 * m) = 8 * m ^ 2 + 4 * m + 1 := by unfold cs; ring
  have e2 : cs (2 * m + 1) = 8 * m ^ 2 + 12 * m + 5 := by unfold cs; ring
  rw [e1, e2]
  apply inv_val _ _ _ (8 * m ^ 2 + 11 * m + 4)
  · nlinarith
  · ring

theorem a_odd (m : ℕ) : a (2 * m + 1) = 4 * m ^ 2 + 5 * m + 2 := by
  unfold a
  have e1 : cs (2 * m + 1) = 8 * m ^ 2 + 12 * m + 5 := by unfold cs; ring
  have e2 : cs (2 * m + 1 + 1) = 8 * m ^ 2 + 20 * m + 13 := by unfold cs; ring
  rw [e1, e2]
  apply inv_val _ _ _ (4 * m ^ 2 + 9 * m + 5)
  · nlinarith
  · ring

theorem a_zero : a 0 = 0 := by
  unfold a
  have : cs 0 = 1 := rfl
  rw [this]
  exact Nat.lt_one_iff.mp (ZMod.val_lt _)

theorem ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
theorem od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

theorem closed (n : ℕ) (hn : 0 < n) :
    4 * (a n : ℤ) = 3 + (-1) ^ n + 2 * (2 + (-1) ^ n) * n + 2 * (3 + (-1) ^ n) * n ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [ev, a_even m (by omega)]; push_cast; ring
  · rw [od, a_odd m]; push_cast; ring

theorem recur (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  simp only [show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 6 = m + 1 by omega]
  have h0 := closed (m + 7) (by omega)
  have h2 := closed (m + 5) (by omega)
  have h4 := closed (m + 3) (by omega)
  have h6 := closed (m + 1) (by omega)
  have p0 : (-1 : ℤ) ^ (m + 7) = -(-1) ^ m := by rw [pow_add]; norm_num
  have p2 : (-1 : ℤ) ^ (m + 5) = -(-1) ^ m := by rw [pow_add]; norm_num
  have p4 : (-1 : ℤ) ^ (m + 3) = -(-1) ^ m := by rw [pow_add]; norm_num
  have p6 : (-1 : ℤ) ^ (m + 1) = -(-1) ^ m := by rw [pow_add]; norm_num
  rw [p0] at h0; rw [p2] at h2; rw [p4] at h4; rw [p6] at h6
  push_cast at h0 h2 h4 h6
  have : (4 : ℤ) * ((a (m + 7) : ℤ) - (3 * a (m + 5) - 3 * a (m + 3) + a (m + 1))) = 0 := by
    linear_combination h0 - 3 * h2 + 3 * h4 - h6
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

open PowerSeries in
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3) =
    (X * (2 + 12 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5) : PowerSeries ℤ) := by
  have v0 : a 0 = 0 := a_zero
  have v1 : a 1 = 2 := by simpa using a_odd 0
  have v2 : a 2 = 12 := by simpa using a_even 1 le_rfl
  have v3 : a 3 = 11 := by simpa using a_odd 1
  have v4 : a 4 = 39 := by simpa using a_even 2 (by norm_num)
  have v5 : a 5 = 28 := by simpa using a_odd 2
  have v6 : a 6 = 82 := by simpa using a_even 3 (by norm_num)
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 3 * (1 + X) ^ 3) = F + (-3 : ℤ) • (F * X ^ 2) + (3 : ℤ) • (F * X ^ 4) + (-1 : ℤ) • (F * X ^ 6) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (X * (2 + 12 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5) : PowerSeries ℤ) = (2 : ℤ) • X ^ 1 + (12 : ℤ) • X ^ 2 + (5 : ℤ) • X ^ 3 + (3 : ℤ) • X ^ 4 + (1 : ℤ) • X ^ 5 + (1 : ℤ) • X ^ 6 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 6 < n
  · have hr := recur n h
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6]

end P308215

theorem OMA.solution : type_of% @OMA.S_oeis_a308215.main :=
  ⟨P308215.gf, P308215.closed, P308215.recur⟩
