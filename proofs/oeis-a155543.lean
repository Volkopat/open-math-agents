import OMAStatements.S_oeis_a155543
import Mathlib

-- Problem: A155543, a(n) = 2*A081294(n) equals A090129(2n+2), the smallest positive exponent e
--   such that 2^(2n+2) divides 3^e - 1.
-- Credit: @canneyi
-- The series P = (1-2x)/(1-4x) satisfies P*(1-4x) = 1-2x, so its coefficients are 1, 2, 8, 32, ...
-- For even e > 0 the 2-adic valuation of 3^e - 1 is 2 + v2(e) (lifting the exponent).
-- For odd e, 3^e - 1 is 2 modulo 4.

open OMA.S_oeis_a155543

namespace OMAa155543

theorem v_even (e : ℕ) (he : e ≠ 0) (hev : Even e) :
    padicValNat 2 (3 ^ e - 1) = 2 + padicValNat 2 e := by
  have h := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by decide) (by decide) (by decide)
    he hev
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    have e4 : (3 + 1 : ℕ) = 2 ^ 2 := by norm_num
    rw [e4, padicValNat.prime_pow]
  have h2 : padicValNat 2 (3 - 1) = 1 := by
    have e2 : (3 - 1 : ℕ) = 2 ^ 1 := by norm_num
    rw [e2, padicValNat.prime_pow]
  rw [one_pow, h4, h2] at h
  omega

theorem odd_case (e : ℕ) (ho : Odd e) : ¬ 4 ∣ 3 ^ e - 1 := by
  obtain ⟨k, rfl⟩ := ho
  have h : 3 ^ (2 * k + 1) % 4 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
  generalize 3 ^ (2 * k + 1) = x at h hpos ⊢
  omega

theorem sub_ne_zero (e : ℕ) (he : 0 < e) : 3 ^ e - 1 ≠ 0 := by
  have h : 3 ^ 1 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  omega

theorem dvd_of (n e : ℕ) (he : 0 < e) (hev : Even e) (hd : 2 ^ (2 * n) ∣ e) :
    2 ^ (2 * n + 2) ∣ 3 ^ e - 1 := by
  refine (padicValNat_dvd_iff_le (sub_ne_zero e he)).mpr ?_
  have h := (padicValNat_dvd_iff_le (by omega : e ≠ 0)).mp hd
  rw [v_even e (by omega) hev]
  omega

theorem of_dvd (n e : ℕ) (he : 0 < e) (h : 2 ^ (2 * n + 2) ∣ 3 ^ e - 1) :
    2 ^ (2 * n) ∣ e ∧ Even e := by
  have hev : Even e := by
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have h4 : 4 ∣ 2 ^ (2 * n + 2) := ⟨2 ^ (2 * n), by ring⟩
    exact odd_case e hne (h4.trans h)
  have hv := (padicValNat_dvd_iff_le (sub_ne_zero e he)).mp h
  rw [v_even e (by omega) hev] at hv
  exact ⟨(padicValNat_dvd_iff_le (by omega : e ≠ 0)).mpr (by omega), hev⟩

theorem least0 : IsLeast {k : ℕ | 0 < k ∧ 2 ^ (2 * 0 + 2) ∣ 3 ^ k - 1} 2 := by
  constructor
  · show 0 < 2 ∧ 2 ^ (2 * 0 + 2) ∣ 3 ^ 2 - 1
    exact ⟨by norm_num, by norm_num⟩
  · intro e he
    obtain ⟨hpos, hdvd⟩ := he
    obtain ⟨hd, hev⟩ := of_dvd 0 e hpos hdvd
    obtain ⟨k, rfl⟩ := hev
    omega

theorem leastS (m : ℕ) :
    IsLeast {k : ℕ | 0 < k ∧ 2 ^ (2 * (m + 1) + 2) ∣ 3 ^ k - 1} (2 ^ (2 * (m + 1))) := by
  constructor
  · show 0 < 2 ^ (2 * (m + 1)) ∧ 2 ^ (2 * (m + 1) + 2) ∣ 3 ^ 2 ^ (2 * (m + 1)) - 1
    exact ⟨by positivity, dvd_of (m + 1) _ (by positivity) ⟨2 ^ (2 * m + 1), by ring⟩ dvd_rfl⟩
  · intro e he
    obtain ⟨hpos, hdvd⟩ := he
    obtain ⟨hd, hev⟩ := of_dvd (m + 1) e hpos hdvd
    exact Nat.le_of_dvd hpos hd

open PowerSeries in
theorem expand (P : PowerSeries ℚ) : P * (1 - 4 * X) = P - (4 : ℕ) • (P * X) := by
  simp only [nsmul_eq_mul]
  ring

open PowerSeries in
theorem rhs : (1 - 2 * X : PowerSeries ℚ) = 1 - (2 : ℕ) • X := by
  simp only [nsmul_eq_mul]
  ring

open PowerSeries in
theorem coeff_h (P : PowerSeries ℚ) (hP : P * (1 - 4 * X) = 1 - 2 * X) (n : ℕ) :
    coeff n (P - (4 : ℕ) • (P * X)) = coeff n (1 - (2 : ℕ) • X) := by
  rw [← expand P, ← rhs, hP]

open PowerSeries in
theorem one_succ (n : ℕ) : coeff (n + 1) (1 : PowerSeries ℚ) = 0 := by
  rw [coeff_one, if_neg (show ¬ (n + 1 = 0) by omega)]

open PowerSeries in
theorem X_one : coeff (0 + 1) (X : PowerSeries ℚ) = 1 := by
  rw [coeff_X, if_pos (show 0 + 1 = 1 from rfl)]

open PowerSeries in
theorem X_succ (n : ℕ) : coeff (n + 1 + 1) (X : PowerSeries ℚ) = 0 := by
  rw [coeff_X, if_neg (show ¬ (n + 1 + 1 = 1) by omega)]

open PowerSeries in
theorem p0 (P : PowerSeries ℚ) (hP : P * (1 - 4 * X) = 1 - 2 * X) : coeff 0 P = 1 := by
  have h := coeff_h P hP 0
  simp only [map_sub, map_nsmul, coeff_zero_mul_X, coeff_zero_one, coeff_zero_X] at h
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
  linarith

open PowerSeries in
theorem psucc (P : PowerSeries ℚ) (hP : P * (1 - 4 * X) = 1 - 2 * X) (n : ℕ) :
    coeff (n + 1) P = 4 * coeff n P - 2 * coeff (n + 1) (X : PowerSeries ℚ) := by
  have h := coeff_h P hP (n + 1)
  simp only [map_sub, map_nsmul, coeff_succ_mul_X, one_succ] at h
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
  linarith

open PowerSeries in
theorem closed (P : PowerSeries ℚ) (hP : P * (1 - 4 * X) = 1 - 2 * X) (n : ℕ) :
    coeff (n + 1) P = 2 * 4 ^ n := by
  induction n with
  | zero =>
    have h := psucc P hP 0
    rw [p0 P hP, X_one] at h
    rw [h]
    norm_num
  | succ k ih =>
    have h := psucc P hP (k + 1)
    rw [ih, X_succ] at h
    rw [h, pow_succ]
    ring

open PowerSeries in
theorem hP0 : ((1 - 2 * X : PowerSeries ℚ) * (1 - 4 * X)⁻¹) * (1 - 4 * X) = 1 - 2 * X := by
  have hc : constantCoeff (1 - 4 * X : PowerSeries ℚ) ≠ 0 := by simp
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]

end OMAa155543

theorem OMA.solution : type_of% @OMA.S_oeis_a155543.main := by
  intro n
  cases n with
  | zero =>
    have hs : A090129 (2 * 0 + 2) = 2 := OMAa155543.least0.csInf_eq
    have hc := OMAa155543.p0 _ OMAa155543.hP0
    unfold a A081294
    rw [hs, hc]
    norm_num
  | succ m =>
    have hs : A090129 (2 * (m + 1) + 2) = 2 ^ (2 * (m + 1)) := (OMAa155543.leastS m).csInf_eq
    have hc := OMAa155543.closed _ OMAa155543.hP0 m
    have h4 : (4 : ℚ) ^ m = 2 ^ (2 * m) := by
      rw [pow_mul]
      norm_num
    unfold a A081294
    rw [hs, hc, h4]
    push_cast
    ring
