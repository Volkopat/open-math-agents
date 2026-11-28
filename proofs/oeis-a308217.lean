import OMAStatements.S_oeis_a308217
import Mathlib

open OMA.S_oeis_a308217

private lemma inv_val {m c k q : ℕ} (hk : k < m) (h : k * c = q * m + 1) :
    ((c : ZMod m)⁻¹).val = k := by
  have h1 : (c : ZMod m) * (k : ZMod m) = 1 := by
    have : ((k * c : ℕ) : ZMod m) = ((q * m + 1 : ℕ) : ZMod m) := by rw [h]
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, zero_add] at this
    rw [mul_comm]; exact this
  rw [ZMod.inv_eq_of_mul_eq_one _ _ _ h1, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

private lemma a_even (j : ℕ) : a (2 * j) = j + 1 := by
  unfold a
  apply inv_val (q := j)
  · unfold c; nlinarith
  · unfold c; ring

private lemma a_odd (j : ℕ) : a (2 * j + 1) = 4 * j ^ 2 + 11 * j + 8 := by
  unfold a
  apply inv_val (q := 4 * j ^ 2 + 7 * j + 3)
  · unfold c; nlinarith
  · unfold c; ring

private lemma closed (n : ℕ) : 4 * (a n : ℤ) =
    9 - 5 * (-1) ^ n + (8 - 6 * (-1) ^ n) * n - 2 * (-1 + (-1) ^ n) * n ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · rw [a_even, (Even.neg_one_pow ⟨j, by ring⟩)]; push_cast; ring
  · rw [a_odd, (Odd.neg_one_pow ⟨j, rfl⟩)]; push_cast; ring

private lemma recur (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 6 = m by omega]
  have h0 := closed m
  have h2 := closed (m + 2)
  have h4 := closed (m + 4)
  have h6 := closed (m + 6)
  simp only [pow_add, neg_one_sq] at h2 h4 h6
  push_cast at h0 h2 h4 h6
  have : (4 : ℤ) * (a (m + 6) - (3 * a (m + 4) - 3 * a (m + 2) + a m)) = 0 := by
    linear_combination h6 - 3 * h4 + 3 * h2 - h0
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a308217.main := by
  refine ⟨?_, recur, closed⟩
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      F - (3 : ℤ) • (F * X ^ 2) + (3 : ℤ) • (F * X ^ 4) - F * X ^ 6 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 8 * X - X ^ 2 - X ^ 3 + X ^ 5 : PowerSeries ℤ) =
      1 + (8 : ℤ) • X ^ 1 - X ^ 2 - X ^ 3 + X ^ 5 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  have i0 : a 0 = 1 := a_even 0
  have i1 : a 1 = 8 := a_odd 0
  have i2 : a 2 = 2 := a_even 1
  have i3 : a 3 = 23 := a_odd 1
  have i4 : a 4 = 3 := a_even 2
  have i5 : a 5 = 46 := a_odd 2
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_one,
    coeff_X_pow, smul_eq_mul]
  by_cases h : 5 < n
  · have hr := recur n h
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 5 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [i0, i1, i2, i3, i4, i5]
