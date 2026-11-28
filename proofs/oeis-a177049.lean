import OMAStatements.S_oeis_a177049
import Mathlib

namespace A177049Aux
open OMA.S_oeis_a177049 PowerSeries

lemma a_of_half (n : ℕ) (c : ℤ) (h : (3 * (n : ℤ) + 1) * (3 * n + 2) = 2 * c)
    (hc : ∃ t : ℤ, c = 2 * t + 1) : a n = c := by
  unfold a
  have h' : ((3 * (n : ℚ) + 1) * (3 * n + 2) : ℚ) = 2 * c := by exact_mod_cast h
  have e : ((3 * (n : ℚ) + 1) * (3 * n + 2) / 4 : ℚ) = (c : ℚ) / ((2 : ℤ) : ℚ) := by
    rw [h']; push_cast; ring
  rw [e]
  apply Rat.num_div_eq_of_coprime (by norm_num)
  obtain ⟨t, rfl⟩ := hc
  apply Nat.Coprime.symm
  show Nat.Coprime 2 (2 * t + 1).natAbs
  rw [Nat.prime_two.coprime_iff_not_dvd]
  intro hd
  have hd' := Int.natCast_dvd.mpr hd
  omega

lemma a_of_quarter (n : ℕ) (c : ℤ) (h : (3 * (n : ℤ) + 1) * (3 * n + 2) = 4 * c) : a n = c := by
  unfold a
  have h' : ((3 * (n : ℚ) + 1) * (3 * n + 2) : ℚ) = 4 * c := by exact_mod_cast h
  rw [h', mul_div_cancel_left₀ _ (by norm_num : (4 : ℚ) ≠ 0), Rat.num_intCast]

lemma A0 (q : ℕ) : a (4 * q) = (12 * (q : ℤ) + 1) * (6 * q + 1) :=
  a_of_half _ _ (by push_cast; ring) ⟨36 * q * q + 9 * q, by ring⟩
lemma A1 (q : ℕ) : a (4 * q + 1) = (3 * (q : ℤ) + 1) * (12 * q + 5) :=
  a_of_quarter _ _ (by push_cast; ring)
lemma A2 (q : ℕ) : a (4 * q + 2) = (12 * (q : ℤ) + 7) * (3 * q + 2) :=
  a_of_quarter _ _ (by push_cast; ring)
lemma A3 (q : ℕ) : a (4 * q + 3) = (6 * (q : ℤ) + 5) * (12 * q + 11) :=
  a_of_half _ _ (by push_cast; ring) ⟨36 * q * q + 63 * q + 27, by ring⟩

lemma a_0 : a 0 = 1 := a_of_half 0 1 (by norm_num) ⟨0, by norm_num⟩
lemma a_1 : a 1 = 5 := a_of_quarter 1 5 (by norm_num)
lemma a_2 : a 2 = 14 := a_of_quarter 2 14 (by norm_num)
lemma a_3 : a 3 = 55 := a_of_half 3 55 (by norm_num) ⟨27, by norm_num⟩
lemma a_4 : a 4 = 91 := a_of_half 4 91 (by norm_num) ⟨45, by norm_num⟩
lemma a_5 : a 5 = 68 := a_of_quarter 5 68 (by norm_num)
lemma a_6 : a 6 = 95 := a_of_quarter 6 95 (by norm_num)
lemma a_7 : a 7 = 253 := a_of_half 7 253 (by norm_num) ⟨126, by norm_num⟩
lemma a_8 : a 8 = 325 := a_of_half 8 325 (by norm_num) ⟨162, by norm_num⟩

lemma R0 (q : ℕ) : a (4 * q + 9) = 3 * a (4 * q + 8) - 6 * a (4 * q + 7) + 10 * a (4 * q + 6) - 12 * a (4 * q + 5) + 12 * a (4 * q + 4) - 10 * a (4 * q + 3) + 6 * a (4 * q + 2) - 3 * a (4 * q + 1) + a (4 * q) := by
  have e0 : a (4 * q) = (12 * ((q : ℕ) : ℤ) + 1) * (6 * ((q : ℕ) : ℤ) + 1) := A0 q
  have e1 : a (4 * q + 1) = (3 * ((q : ℕ) : ℤ) + 1) * (12 * ((q : ℕ) : ℤ) + 5) := A1 q
  have e2 : a (4 * q + 2) = (12 * ((q : ℕ) : ℤ) + 7) * (3 * ((q : ℕ) : ℤ) + 2) := A2 q
  have e3 : a (4 * q + 3) = (6 * ((q : ℕ) : ℤ) + 5) * (12 * ((q : ℕ) : ℤ) + 11) := A3 q
  have e4 : a (4 * q + 4) = (12 * ((q + 1 : ℕ) : ℤ) + 1) * (6 * ((q + 1 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 4 = 4 * (q + 1) by ring]; exact A0 (q + 1)
  have e5 : a (4 * q + 5) = (3 * ((q + 1 : ℕ) : ℤ) + 1) * (12 * ((q + 1 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 5 = 4 * (q + 1) + 1 by ring]; exact A1 (q + 1)
  have e6 : a (4 * q + 6) = (12 * ((q + 1 : ℕ) : ℤ) + 7) * (3 * ((q + 1 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 6 = 4 * (q + 1) + 2 by ring]; exact A2 (q + 1)
  have e7 : a (4 * q + 7) = (6 * ((q + 1 : ℕ) : ℤ) + 5) * (12 * ((q + 1 : ℕ) : ℤ) + 11) := by
    rw [show 4 * q + 7 = 4 * (q + 1) + 3 by ring]; exact A3 (q + 1)
  have e8 : a (4 * q + 8) = (12 * ((q + 2 : ℕ) : ℤ) + 1) * (6 * ((q + 2 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 8 = 4 * (q + 2) by ring]; exact A0 (q + 2)
  have e9 : a (4 * q + 9) = (3 * ((q + 2 : ℕ) : ℤ) + 1) * (12 * ((q + 2 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 9 = 4 * (q + 2) + 1 by ring]; exact A1 (q + 2)
  rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  push_cast; ring
lemma R1 (q : ℕ) : a (4 * q + 10) = 3 * a (4 * q + 9) - 6 * a (4 * q + 8) + 10 * a (4 * q + 7) - 12 * a (4 * q + 6) + 12 * a (4 * q + 5) - 10 * a (4 * q + 4) + 6 * a (4 * q + 3) - 3 * a (4 * q + 2) + a (4 * q + 1) := by
  have e0 : a (4 * q + 1) = (3 * ((q : ℕ) : ℤ) + 1) * (12 * ((q : ℕ) : ℤ) + 5) := A1 q
  have e1 : a (4 * q + 2) = (12 * ((q : ℕ) : ℤ) + 7) * (3 * ((q : ℕ) : ℤ) + 2) := A2 q
  have e2 : a (4 * q + 3) = (6 * ((q : ℕ) : ℤ) + 5) * (12 * ((q : ℕ) : ℤ) + 11) := A3 q
  have e3 : a (4 * q + 4) = (12 * ((q + 1 : ℕ) : ℤ) + 1) * (6 * ((q + 1 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 4 = 4 * (q + 1) by ring]; exact A0 (q + 1)
  have e4 : a (4 * q + 5) = (3 * ((q + 1 : ℕ) : ℤ) + 1) * (12 * ((q + 1 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 5 = 4 * (q + 1) + 1 by ring]; exact A1 (q + 1)
  have e5 : a (4 * q + 6) = (12 * ((q + 1 : ℕ) : ℤ) + 7) * (3 * ((q + 1 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 6 = 4 * (q + 1) + 2 by ring]; exact A2 (q + 1)
  have e6 : a (4 * q + 7) = (6 * ((q + 1 : ℕ) : ℤ) + 5) * (12 * ((q + 1 : ℕ) : ℤ) + 11) := by
    rw [show 4 * q + 7 = 4 * (q + 1) + 3 by ring]; exact A3 (q + 1)
  have e7 : a (4 * q + 8) = (12 * ((q + 2 : ℕ) : ℤ) + 1) * (6 * ((q + 2 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 8 = 4 * (q + 2) by ring]; exact A0 (q + 2)
  have e8 : a (4 * q + 9) = (3 * ((q + 2 : ℕ) : ℤ) + 1) * (12 * ((q + 2 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 9 = 4 * (q + 2) + 1 by ring]; exact A1 (q + 2)
  have e9 : a (4 * q + 10) = (12 * ((q + 2 : ℕ) : ℤ) + 7) * (3 * ((q + 2 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 10 = 4 * (q + 2) + 2 by ring]; exact A2 (q + 2)
  rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  push_cast; ring
lemma R2 (q : ℕ) : a (4 * q + 11) = 3 * a (4 * q + 10) - 6 * a (4 * q + 9) + 10 * a (4 * q + 8) - 12 * a (4 * q + 7) + 12 * a (4 * q + 6) - 10 * a (4 * q + 5) + 6 * a (4 * q + 4) - 3 * a (4 * q + 3) + a (4 * q + 2) := by
  have e0 : a (4 * q + 2) = (12 * ((q : ℕ) : ℤ) + 7) * (3 * ((q : ℕ) : ℤ) + 2) := A2 q
  have e1 : a (4 * q + 3) = (6 * ((q : ℕ) : ℤ) + 5) * (12 * ((q : ℕ) : ℤ) + 11) := A3 q
  have e2 : a (4 * q + 4) = (12 * ((q + 1 : ℕ) : ℤ) + 1) * (6 * ((q + 1 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 4 = 4 * (q + 1) by ring]; exact A0 (q + 1)
  have e3 : a (4 * q + 5) = (3 * ((q + 1 : ℕ) : ℤ) + 1) * (12 * ((q + 1 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 5 = 4 * (q + 1) + 1 by ring]; exact A1 (q + 1)
  have e4 : a (4 * q + 6) = (12 * ((q + 1 : ℕ) : ℤ) + 7) * (3 * ((q + 1 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 6 = 4 * (q + 1) + 2 by ring]; exact A2 (q + 1)
  have e5 : a (4 * q + 7) = (6 * ((q + 1 : ℕ) : ℤ) + 5) * (12 * ((q + 1 : ℕ) : ℤ) + 11) := by
    rw [show 4 * q + 7 = 4 * (q + 1) + 3 by ring]; exact A3 (q + 1)
  have e6 : a (4 * q + 8) = (12 * ((q + 2 : ℕ) : ℤ) + 1) * (6 * ((q + 2 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 8 = 4 * (q + 2) by ring]; exact A0 (q + 2)
  have e7 : a (4 * q + 9) = (3 * ((q + 2 : ℕ) : ℤ) + 1) * (12 * ((q + 2 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 9 = 4 * (q + 2) + 1 by ring]; exact A1 (q + 2)
  have e8 : a (4 * q + 10) = (12 * ((q + 2 : ℕ) : ℤ) + 7) * (3 * ((q + 2 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 10 = 4 * (q + 2) + 2 by ring]; exact A2 (q + 2)
  have e9 : a (4 * q + 11) = (6 * ((q + 2 : ℕ) : ℤ) + 5) * (12 * ((q + 2 : ℕ) : ℤ) + 11) := by
    rw [show 4 * q + 11 = 4 * (q + 2) + 3 by ring]; exact A3 (q + 2)
  rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  push_cast; ring
lemma R3 (q : ℕ) : a (4 * q + 12) = 3 * a (4 * q + 11) - 6 * a (4 * q + 10) + 10 * a (4 * q + 9) - 12 * a (4 * q + 8) + 12 * a (4 * q + 7) - 10 * a (4 * q + 6) + 6 * a (4 * q + 5) - 3 * a (4 * q + 4) + a (4 * q + 3) := by
  have e0 : a (4 * q + 3) = (6 * ((q : ℕ) : ℤ) + 5) * (12 * ((q : ℕ) : ℤ) + 11) := A3 q
  have e1 : a (4 * q + 4) = (12 * ((q + 1 : ℕ) : ℤ) + 1) * (6 * ((q + 1 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 4 = 4 * (q + 1) by ring]; exact A0 (q + 1)
  have e2 : a (4 * q + 5) = (3 * ((q + 1 : ℕ) : ℤ) + 1) * (12 * ((q + 1 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 5 = 4 * (q + 1) + 1 by ring]; exact A1 (q + 1)
  have e3 : a (4 * q + 6) = (12 * ((q + 1 : ℕ) : ℤ) + 7) * (3 * ((q + 1 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 6 = 4 * (q + 1) + 2 by ring]; exact A2 (q + 1)
  have e4 : a (4 * q + 7) = (6 * ((q + 1 : ℕ) : ℤ) + 5) * (12 * ((q + 1 : ℕ) : ℤ) + 11) := by
    rw [show 4 * q + 7 = 4 * (q + 1) + 3 by ring]; exact A3 (q + 1)
  have e5 : a (4 * q + 8) = (12 * ((q + 2 : ℕ) : ℤ) + 1) * (6 * ((q + 2 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 8 = 4 * (q + 2) by ring]; exact A0 (q + 2)
  have e6 : a (4 * q + 9) = (3 * ((q + 2 : ℕ) : ℤ) + 1) * (12 * ((q + 2 : ℕ) : ℤ) + 5) := by
    rw [show 4 * q + 9 = 4 * (q + 2) + 1 by ring]; exact A1 (q + 2)
  have e7 : a (4 * q + 10) = (12 * ((q + 2 : ℕ) : ℤ) + 7) * (3 * ((q + 2 : ℕ) : ℤ) + 2) := by
    rw [show 4 * q + 10 = 4 * (q + 2) + 2 by ring]; exact A2 (q + 2)
  have e8 : a (4 * q + 11) = (6 * ((q + 2 : ℕ) : ℤ) + 5) * (12 * ((q + 2 : ℕ) : ℤ) + 11) := by
    rw [show 4 * q + 11 = 4 * (q + 2) + 3 by ring]; exact A3 (q + 2)
  have e9 : a (4 * q + 12) = (12 * ((q + 3 : ℕ) : ℤ) + 1) * (6 * ((q + 3 : ℕ) : ℤ) + 1) := by
    rw [show 4 * q + 12 = 4 * (q + 3) by ring]; exact A0 (q + 3)
  rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  push_cast; ring

lemma rec9 : ∀ n : ℕ, 9 ≤ n → a n = 3 * a (n - 1) - 6 * a (n - 2) + 10 * a (n - 3) -
    12 * a (n - 4) + 12 * a (n - 5) - 10 * a (n - 6) + 6 * a (n - 7) -
    3 * a (n - 8) + a (n - 9) := by
  intro n hn
  obtain ⟨q, hq⟩ : ∃ q, n = 4 * q + 9 ∨ n = 4 * q + 10 ∨ n = 4 * q + 11 ∨ n = 4 * q + 12 :=
    ⟨(n - 9) / 4, by omega⟩
  rcases hq with rfl | rfl | rfl | rfl
  · rw [show 4 * q + 9 - 1 = 4 * q + 8 by omega, show 4 * q + 9 - 2 = 4 * q + 7 by omega, show 4 * q + 9 - 3 = 4 * q + 6 by omega, show 4 * q + 9 - 4 = 4 * q + 5 by omega, show 4 * q + 9 - 5 = 4 * q + 4 by omega, show 4 * q + 9 - 6 = 4 * q + 3 by omega, show 4 * q + 9 - 7 = 4 * q + 2 by omega, show 4 * q + 9 - 8 = 4 * q + 1 by omega, show 4 * q + 9 - 9 = 4 * q by omega]
    exact R0 q
  · rw [show 4 * q + 10 - 1 = 4 * q + 9 by omega, show 4 * q + 10 - 2 = 4 * q + 8 by omega, show 4 * q + 10 - 3 = 4 * q + 7 by omega, show 4 * q + 10 - 4 = 4 * q + 6 by omega, show 4 * q + 10 - 5 = 4 * q + 5 by omega, show 4 * q + 10 - 6 = 4 * q + 4 by omega, show 4 * q + 10 - 7 = 4 * q + 3 by omega, show 4 * q + 10 - 8 = 4 * q + 2 by omega, show 4 * q + 10 - 9 = 4 * q + 1 by omega]
    exact R1 q
  · rw [show 4 * q + 11 - 1 = 4 * q + 10 by omega, show 4 * q + 11 - 2 = 4 * q + 9 by omega, show 4 * q + 11 - 3 = 4 * q + 8 by omega, show 4 * q + 11 - 4 = 4 * q + 7 by omega, show 4 * q + 11 - 5 = 4 * q + 6 by omega, show 4 * q + 11 - 6 = 4 * q + 5 by omega, show 4 * q + 11 - 7 = 4 * q + 4 by omega, show 4 * q + 11 - 8 = 4 * q + 3 by omega, show 4 * q + 11 - 9 = 4 * q + 2 by omega]
    exact R2 q
  · rw [show 4 * q + 12 - 1 = 4 * q + 11 by omega, show 4 * q + 12 - 2 = 4 * q + 10 by omega, show 4 * q + 12 - 3 = 4 * q + 9 by omega, show 4 * q + 12 - 4 = 4 * q + 8 by omega, show 4 * q + 12 - 5 = 4 * q + 7 by omega, show 4 * q + 12 - 6 = 4 * q + 6 by omega, show 4 * q + 12 - 7 = 4 * q + 5 by omega, show 4 * q + 12 - 8 = 4 * q + 4 by omega, show 4 * q + 12 - 9 = 4 * q + 3 by omega]
    exact R3 q

lemma hD : denominator = (1 - C 3 * X + C 6 * X ^ 2 - C 10 * X ^ 3 + C 12 * X ^ 4 - C 12 * X ^ 5 + C 10 * X ^ 6 - C 6 * X ^ 7 + C 3 * X ^ 8 - X ^ 9 : PowerSeries ℤ) := by
  unfold denominator
  simp only [map_ofNat]
  ring
lemma hN : numerator = (1 + C 2 * X + C 5 * X ^ 2 + C 33 * X ^ 3 - C 28 * X ^ 4 + C 33 * X ^ 5 + C 5 * X ^ 6 + C 2 * X ^ 7 + X ^ 8 : PowerSeries ℤ) := by
  unfold numerator
  simp only [map_ofNat]
  ring
lemma dcoeff (k : ℕ) : coeff k denominator =
    ((if k = 0 then 1 else 0) - 3 * (if k = 1 then 1 else 0) + 6 * (if k = 2 then 1 else 0) - 10 * (if k = 3 then 1 else 0) + 12 * (if k = 4 then 1 else 0) - 12 * (if k = 5 then 1 else 0) + 10 * (if k = 6 then 1 else 0) - 6 * (if k = 7 then 1 else 0) + 3 * (if k = 8 then 1 else 0) - (if k = 9 then 1 else 0) : ℤ) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]
lemma ncoeff (k : ℕ) : coeff k numerator =
    ((if k = 0 then 1 else 0) + 2 * (if k = 1 then 1 else 0) + 5 * (if k = 2 then 1 else 0) + 33 * (if k = 3 then 1 else 0) - 28 * (if k = 4 then 1 else 0) + 33 * (if k = 5 then 1 else 0) + 5 * (if k = 6 then 1 else 0) + 2 * (if k = 7 then 1 else 0) + (if k = 8 then 1 else 0) : ℤ) := by
  rw [hN]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]
lemma sum_d (f : ℕ → ℤ) (n : ℕ) (hn : 9 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), coeff k denominator * f k =
      f 0 - 3 * f 1 + 6 * f 2 - 10 * f 3 + 12 * f 4 - 12 * f 5 + 10 * f 6 - 6 * f 7 + 3 * f 8 - f 9 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 10 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 10 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega, show k ≠ 5 by omega, show k ≠ 6 by omega, show k ≠ 7 by omega, show k ≠ 8 by omega, show k ≠ 9 by omega]

lemma part2 : denominator * generating = numerator := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i denominator * coeff j generating)]
  simp only [generating, coeff_mk]
  by_cases hn : 9 ≤ n
  · rw [sum_d (fun k => a (n - k)) n hn]
    have hr := rec9 n hn
    have hz : coeff n numerator = 0 := by
      rw [ncoeff]
      simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega]
    rw [hz, Nat.sub_zero]
    linarith
  · have hn' : n ≤ 8 := by omega
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, ncoeff, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]
end A177049Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a177049.main :=
  ⟨A177049Aux.rec9, A177049Aux.part2⟩
