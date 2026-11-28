import OMAStatements.S_oeis_a038261
import Mathlib
open OMA.S_oeis_a038261 PowerSeries

theorem Pa038261.eqn1 (n : ℕ) (h : 5 ≤ n) (hr : n % 4 = 1) : w n = w (n - 1) + w (n - 2) := by
  rw [w, dif_neg (by omega), if_pos hr]

theorem Pa038261.eqn (n p q : ℕ) (h : 5 ≤ n) (hp : p = n - 1)
    (hq : q = n - (if n % 4 = 1 then 2 else if n % 4 = 2 then 4 else if n % 4 = 3 then 6 else 8)) :
    w n = w p + w q := by
  subst hp hq
  rw [w, dif_neg (by omega)]
  split_ifs <;> rfl

theorem Pa038261.eqn2 (n : ℕ) (h : 5 ≤ n) (hr : n % 4 = 2) : w n = w (n - 1) + w (n - 4) := by
  rw [w, dif_neg (by omega), if_neg (by omega), if_pos hr]

theorem Pa038261.eqn3 (n : ℕ) (h : 5 ≤ n) (hr : n % 4 = 3) : w n = w (n - 1) + w (n - 6) := by
  rw [w, dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hr]

theorem Pa038261.eqn0 (n : ℕ) (h : 5 ≤ n) (hr : n % 4 = 0) : w n = w (n - 1) + w (n - 8) := by
  rw [w, dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem Pa038261.vals : w 0 = 1 ∧ w 8 = 5 ∧ w 16 = 55 ∧ w 24 = 671 ∧ w 32 = 8272 := by
  have h0 : w 0 = 1 := by rw [w, dif_pos (by norm_num)]
  have h1 : w 1 = 1 := by rw [w, dif_pos (by norm_num)]
  have h2 : w 2 = 1 := by rw [w, dif_pos (by norm_num)]
  have h3 : w 3 = 1 := by rw [w, dif_pos (by norm_num)]
  have h4 : w 4 = 1 := by rw [w, dif_pos (by norm_num)]
  have h5 : w 5 = 2 := by
    have e := Pa038261.eqn1 5 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h4, h3]
  have h6 : w 6 = 3 := by
    have e := Pa038261.eqn2 6 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h5, h2]
  have h7 : w 7 = 4 := by
    have e := Pa038261.eqn3 7 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h6, h1]
  have h8 : w 8 = 5 := by
    have e := Pa038261.eqn0 8 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h7, h0]
  have h9 : w 9 = 9 := by
    have e := Pa038261.eqn1 9 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h8, h7]
  have h10 : w 10 = 12 := by
    have e := Pa038261.eqn2 10 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h9, h6]
  have h11 : w 11 = 14 := by
    have e := Pa038261.eqn3 11 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h10, h5]
  have h12 : w 12 = 15 := by
    have e := Pa038261.eqn0 12 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h11, h4]
  have h13 : w 13 = 29 := by
    have e := Pa038261.eqn1 13 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h12, h11]
  have h14 : w 14 = 41 := by
    have e := Pa038261.eqn2 14 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h13, h10]
  have h15 : w 15 = 50 := by
    have e := Pa038261.eqn3 15 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h14, h9]
  have h16 : w 16 = 55 := by
    have e := Pa038261.eqn0 16 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h15, h8]
  have h17 : w 17 = 105 := by
    have e := Pa038261.eqn1 17 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h16, h15]
  have h18 : w 18 = 146 := by
    have e := Pa038261.eqn2 18 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h17, h14]
  have h19 : w 19 = 175 := by
    have e := Pa038261.eqn3 19 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h18, h13]
  have h20 : w 20 = 190 := by
    have e := Pa038261.eqn0 20 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h19, h12]
  have h21 : w 21 = 365 := by
    have e := Pa038261.eqn1 21 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h20, h19]
  have h22 : w 22 = 511 := by
    have e := Pa038261.eqn2 22 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h21, h18]
  have h23 : w 23 = 616 := by
    have e := Pa038261.eqn3 23 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h22, h17]
  have h24 : w 24 = 671 := by
    have e := Pa038261.eqn0 24 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h23, h16]
  have h25 : w 25 = 1287 := by
    have e := Pa038261.eqn1 25 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h24, h23]
  have h26 : w 26 = 1798 := by
    have e := Pa038261.eqn2 26 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h25, h22]
  have h27 : w 27 = 2163 := by
    have e := Pa038261.eqn3 27 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h26, h21]
  have h28 : w 28 = 2353 := by
    have e := Pa038261.eqn0 28 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h27, h20]
  have h29 : w 29 = 4516 := by
    have e := Pa038261.eqn1 29 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h28, h27]
  have h30 : w 30 = 6314 := by
    have e := Pa038261.eqn2 30 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h29, h26]
  have h31 : w 31 = 7601 := by
    have e := Pa038261.eqn3 31 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h30, h25]
  have h32 : w 32 = 8272 := by
    have e := Pa038261.eqn0 32 (by norm_num) (by norm_num)
    norm_num at e
    rw [e, h31, h24]
  exact ⟨h0, h8, h16, h24, h32⟩

theorem Pa038261.eqs (m : ℕ) : w (8 * m + 8) = w (8 * m + 7) + w (8 * m + 0) ∧ w (8 * m + 9) = w (8 * m + 8) + w (8 * m + 7) ∧ w (8 * m + 15) = w (8 * m + 14) + w (8 * m + 9) ∧ w (8 * m + 16) = w (8 * m + 15) + w (8 * m + 8) ∧ w (8 * m + 17) = w (8 * m + 16) + w (8 * m + 15) ∧ w (8 * m + 18) = w (8 * m + 17) + w (8 * m + 14) ∧ w (8 * m + 22) = w (8 * m + 21) + w (8 * m + 18) ∧ w (8 * m + 23) = w (8 * m + 22) + w (8 * m + 17) ∧ w (8 * m + 24) = w (8 * m + 23) + w (8 * m + 16) ∧ w (8 * m + 25) = w (8 * m + 24) + w (8 * m + 23) ∧ w (8 * m + 26) = w (8 * m + 25) + w (8 * m + 22) ∧ w (8 * m + 27) = w (8 * m + 26) + w (8 * m + 21) ∧ w (8 * m + 29) = w (8 * m + 28) + w (8 * m + 27) ∧ w (8 * m + 30) = w (8 * m + 29) + w (8 * m + 26) ∧ w (8 * m + 31) = w (8 * m + 30) + w (8 * m + 25) ∧ w (8 * m + 32) = w (8 * m + 31) + w (8 * m + 24) ∧ w (8 * m + 33) = w (8 * m + 32) + w (8 * m + 31) ∧ w (8 * m + 34) = w (8 * m + 33) + w (8 * m + 30) ∧ w (8 * m + 35) = w (8 * m + 34) + w (8 * m + 29) ∧ w (8 * m + 36) = w (8 * m + 35) + w (8 * m + 28) ∧ w (8 * m + 37) = w (8 * m + 36) + w (8 * m + 35) ∧ w (8 * m + 38) = w (8 * m + 37) + w (8 * m + 34) ∧ w (8 * m + 39) = w (8 * m + 38) + w (8 * m + 33) ∧ w (8 * m + 40) = w (8 * m + 39) + w (8 * m + 32) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Pa038261.eqn <;> (try split_ifs) <;> omega

theorem Pa038261.rec (m : ℕ) : (w (8 * m + 40) : ℤ) - 15 * w (8 * m + 32) + 35 * w (8 * m + 24) - 28 * w (8 * m + 16) + 9 * w (8 * m + 8) - w (8 * m) = 0 := by
  obtain ⟨e8, e9, e15, e16, e17, e18, e22, e23, e24, e25, e26, e27, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40⟩ := Pa038261.eqs m
  zify at e8 e9 e15 e16 e17 e18 e22 e23 e24 e25 e26 e27 e29 e30 e31 e32 e33 e34 e35 e36 e37 e38 e39 e40
  linear_combination (1) * e8 + (-1) * e9 + (-1) * e15 + (-7) * e16 + (6) * e17 + (1) * e18 + (1) * e22 + (5) * e23 + (15) * e24 + (-10) * e25 + (-4) * e26 + (-1) * e27 + (-1) * e29 + (-3) * e30 + (-6) * e31 + (-10) * e32 + (4) * e33 + (3) * e34 + (2) * e35 + (1) * e36 + (1) * e37 + (1) * e38 + (1) * e39 + (1) * e40

theorem Pa038261.cm (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (C c * (PowerSeries.mk f * X ^ k)) = c * (if k ≤ n then f (n - k) else 0) := by
  rw [coeff_C_mul, coeff_mul_X_pow', coeff_mk]

theorem OMA.solution : type_of% @OMA.S_oeis_a038261.main := by
  set A := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have hL : A * (-1 + 15 * X - 35 * X ^ 2 + 28 * X ^ 3 - 9 * X ^ 4 + X ^ 5) =
      C (-1) * (A * X ^ 0) + C 15 * (A * X ^ 1) + C (-35) * (A * X ^ 2) + C 28 * (A * X ^ 3)
        + C (-9) * (A * X ^ 4) + C 1 * (A * X ^ 5) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  have hR : -(X - 1) * (X ^ 3 - 6 * X ^ 2 + 9 * X - 1) =
      C (-1) + C 10 * X ^ 1 + C (-15) * X ^ 2 + C 7 * X ^ 3 + C (-1) * X ^ 4 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, Pa038261.cm, hA, coeff_C_mul_X_pow, coeff_C]
  obtain ⟨v0, v1, v2, v3, v4⟩ := Pa038261.vals
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [a, v0, v1, v2, v3, v4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have hr := Pa038261.rec m
    simp [a]
    ring_nf
    ring_nf at hr
    linear_combination (-1 : ℤ) * hr
