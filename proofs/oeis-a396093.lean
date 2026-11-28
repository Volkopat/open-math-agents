import OMAStatements.S_oeis_a396093
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a396093

open OMA.S_oeis_a396093

private lemma B_op_spec (F : PowerSeries ℤ) (hF : PowerSeries.constantCoeff F = 0) :
    (1 - F) ^ 2 * B_op F = F ∧ PowerSeries.constantCoeff (B_op F) = 0 := by
  have hconst : PowerSeries.constantCoeff ((1 - F) ^ 2) = 1 := by
    simp [map_pow, map_sub, hF]
  have hu : IsUnit ((1 - F) ^ 2) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hconst]; exact isUnit_one)
  constructor
  · unfold B_op
    rw [← mul_assoc, mul_comm ((1 - F) ^ 2) F, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
  · unfold B_op
    simp [map_mul, hF]

private lemma zmod2_ps_two_eq_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (y : PowerSeries (ZMod 2)) : y + y = 0 := by
  rw [← two_mul, zmod2_ps_two_eq_zero, zero_mul]

private lemma zmod2_ps_neg (y : PowerSeries (ZMod 2)) : -y = y := by
  have := zmod2_ps_add_self y
  exact neg_eq_of_add_eq_zero_right this

private lemma zmod2_ps_sub (x y : PowerSeries (ZMod 2)) : x - y = x + y := by
  rw [sub_eq_add_neg, zmod2_ps_neg]

private lemma zmod2_ps_add_sq (x y : PowerSeries (ZMod 2)) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  calc (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    _ = x ^ 2 + 0 * (x * y) + y ^ 2 := by rw [zmod2_ps_two_eq_zero]
    _ = x ^ 2 + y ^ 2 := by ring

private lemma zmod2_ps_one_sub_sq (y : PowerSeries (ZMod 2)) : (1 - y) ^ 2 = 1 + y ^ 2 := by
  rw [zmod2_ps_sub, zmod2_ps_add_sq, one_pow]

private lemma a_mod2_algebra (b1 b2 a2 : PowerSeries (ZMod 2))
    (hb1 : (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) * b1 = PowerSeries.X)
    (hb2 : (1 + b1 ^ 2) * b2 = b1)
    (ha2 : (1 + b2 ^ 2) * a2 = b2) :
    (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ 10) * a2 =
      PowerSeries.X + PowerSeries.X ^ 3 + PowerSeries.X ^ 7 + PowerSeries.X ^ 9 := by
  set X2 : PowerSeries (ZMod 2) := PowerSeries.X
  -- Step 1: (1 + X^2 + X^4) * b2 = X * (1 + X^2)
  have hstep1 : (1 + X2 ^ 2 + X2 ^ 4) * b2 = X2 * (1 + X2 ^ 2) := by
    have hsq1 : (1 + X2 ^ 2) ^ 2 = 1 + X2 ^ 4 := by
      rw [zmod2_ps_add_sq, one_pow]; ring
    have hmul := congrArg (fun z => (1 + X2 ^ 2) ^ 2 * z) hb2
    have hlhs : (1 + X2 ^ 2) ^ 2 * ((1 + b1 ^ 2) * b2) =
        ((1 + X2 ^ 2) ^ 2 + ((1 + X2 ^ 2) * b1) ^ 2) * b2 := by ring
    have hrhs : (1 + X2 ^ 2) ^ 2 * b1 = (1 + X2 ^ 2) * ((1 + X2 ^ 2) * b1) := by ring
    rw [hlhs, hrhs, hb1, hsq1] at hmul
    linear_combination hmul
  -- Step 2: (1 + X^2 + X^4 + X^6 + X^8) * a2 = X * (1 + X^6)
  have hstep2 : (1 + X2 ^ 2 + X2 ^ 4 + X2 ^ 6 + X2 ^ 8) * a2 = X2 * (1 + X2 ^ 6) := by
    have hsq2 : (1 + X2 ^ 2 + X2 ^ 4) ^ 2 = 1 + X2 ^ 4 + X2 ^ 8 := by
      rw [zmod2_ps_add_sq, zmod2_ps_add_sq, one_pow]; ring
    have hsq3 : (X2 * (1 + X2 ^ 2)) ^ 2 = X2 ^ 2 + X2 ^ 6 := by
      rw [mul_pow, zmod2_ps_add_sq, one_pow]; ring
    have hmul := congrArg (fun z => (1 + X2 ^ 2 + X2 ^ 4) ^ 2 * z) ha2
    have hlhs : (1 + X2 ^ 2 + X2 ^ 4) ^ 2 * ((1 + b2 ^ 2) * a2) =
        ((1 + X2 ^ 2 + X2 ^ 4) ^ 2 + ((1 + X2 ^ 2 + X2 ^ 4) * b2) ^ 2) * a2 := by ring
    have hrhs : (1 + X2 ^ 2 + X2 ^ 4) ^ 2 * b2 =
        (1 + X2 ^ 2 + X2 ^ 4) * ((1 + X2 ^ 2 + X2 ^ 4) * b2) := by ring
    rw [hlhs, hrhs, hstep1, hsq2, hsq3] at hmul
    have hfactor : (1 + X2 ^ 2 + X2 ^ 4) * (X2 * (1 + X2 ^ 2)) = X2 * (1 + X2 ^ 6) := by
      have hmid : X2 ^ 3 + X2 ^ 3 = 0 := zmod2_ps_add_self _
      have hmid2 : X2 ^ 5 + X2 ^ 5 = 0 := zmod2_ps_add_self _
      calc (1 + X2 ^ 2 + X2 ^ 4) * (X2 * (1 + X2 ^ 2))
          = X2 + (X2 ^ 3 + X2 ^ 3) + (X2 ^ 5 + X2 ^ 5) + X2 ^ 7 := by ring
        _ = X2 + 0 + 0 + X2 ^ 7 := by rw [hmid, hmid2]
        _ = X2 * (1 + X2 ^ 6) := by ring
    rw [hfactor] at hmul
    convert hmul using 2
    ring
  -- Step 3: multiply by (1 + X^2) to get (1 + X^10) * a2 = X + X^3 + X^7 + X^9
  have hmul3 := congrArg (fun z => (1 + X2 ^ 2) * z) hstep2
  have hlhs3 : (1 + X2 ^ 2) * ((1 + X2 ^ 2 + X2 ^ 4 + X2 ^ 6 + X2 ^ 8) * a2) =
      (1 + X2 ^ 10) * a2 := by
    have h2 : X2 ^ 2 + X2 ^ 2 = 0 := zmod2_ps_add_self _
    have h4 : X2 ^ 4 + X2 ^ 4 = 0 := zmod2_ps_add_self _
    have h6 : X2 ^ 6 + X2 ^ 6 = 0 := zmod2_ps_add_self _
    have h8 : X2 ^ 8 + X2 ^ 8 = 0 := zmod2_ps_add_self _
    have hpoly : (1 + X2 ^ 2) * (1 + X2 ^ 2 + X2 ^ 4 + X2 ^ 6 + X2 ^ 8) = 1 + X2 ^ 10 := by
      calc (1 + X2 ^ 2) * (1 + X2 ^ 2 + X2 ^ 4 + X2 ^ 6 + X2 ^ 8)
          = 1 + (X2 ^ 2 + X2 ^ 2) + (X2 ^ 4 + X2 ^ 4) + (X2 ^ 6 + X2 ^ 6) +
              (X2 ^ 8 + X2 ^ 8) + X2 ^ 10 := by ring
        _ = 1 + 0 + 0 + 0 + 0 + X2 ^ 10 := by rw [h2, h4, h6, h8]
        _ = 1 + X2 ^ 10 := by ring
    rw [← mul_assoc, hpoly]
  have hrhs3 : (1 + X2 ^ 2) * (X2 * (1 + X2 ^ 6)) = X2 + X2 ^ 3 + X2 ^ 7 + X2 ^ 9 := by ring
  rw [hlhs3, hrhs3] at hmul3
  exact hmul3

private lemma a_mod2_eq :
    let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
    (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ 10) * φ A =
      PowerSeries.X + PowerSeries.X ^ 3 + PowerSeries.X ^ 7 + PowerSeries.X ^ 9 := by
  intro φ
  have h1 := B_op_spec PowerSeries.X PowerSeries.constantCoeff_X
  have h2 := B_op_spec (B_op PowerSeries.X) h1.2
  have h3 := B_op_spec (B_op (B_op PowerSeries.X)) h2.2
  apply a_mod2_algebra (φ (B_op PowerSeries.X)) (φ (B_op (B_op PowerSeries.X))) (φ A)
  · have hm := congrArg φ h1.1
    rw [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X, zmod2_ps_one_sub_sq] at hm
    exact hm
  · have hm := congrArg φ h2.1
    rw [map_mul, map_pow, map_sub, map_one, zmod2_ps_one_sub_sq] at hm
    exact hm
  · have hm := congrArg φ h3.1
    rw [map_mul, map_pow, map_sub, map_one, zmod2_ps_one_sub_sq] at hm
    exact hm

private lemma coeff_a_mod2 (m : ℕ) :
    (a m : ZMod 2) = if m % 10 = 1 ∨ m % 10 = 3 ∨ m % 10 = 7 ∨ m % 10 = 9 then 1 else 0 := by
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hcast : ∀ k, (a k : ZMod 2) = PowerSeries.coeff k (φ A) := by
    intro k
    unfold a
    rw [PowerSeries.coeff_map]
    rfl
  rw [hcast m]
  have hkey := a_mod2_eq
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hc := congrArg (PowerSeries.coeff m) hkey
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul'] at hc
    simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow] at hc
    by_cases hm10 : m < 10
    · rw [if_neg (by omega), add_zero] at hc
      rw [hc]
      interval_cases m <;> decide
    · have hm_ge : 10 ≤ m := by omega
      rw [if_pos hm_ge] at hc
      have hrhs : (if m = 1 then (1 : ZMod 2) else 0) + (if m = 3 then 1 else 0) +
          (if m = 7 then 1 else 0) + (if m = 9 then 1 else 0) = 0 := by
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simp
      rw [hrhs] at hc
      have heq : PowerSeries.coeff m (φ A) = PowerSeries.coeff (m - 10) (φ A) := by
        have hsum : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
        exact hsum _ _ hc
      rw [heq, ih (m - 10) (by omega), show (m - 10) % 10 = m % 10 by omega]

private lemma even_iff_zmod2_eq_zero (z : ℤ) : Even z ↔ (z : ZMod 2) = 0 := by
  rw [even_iff_two_dvd, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem prove_main : type_of% @OMA.S_oeis_a396093.main := by
  constructor
  · intro n _
    rw [even_iff_zmod2_eq_zero, coeff_a_mod2 (2 * n)]
    rw [if_neg (by omega)]
  · intro n hn
    rw [even_iff_zmod2_eq_zero, coeff_a_mod2 (2 * n - 1)]
    constructor
    · intro h
      have hnot : ¬ ((2 * n - 1) % 10 = 1 ∨ (2 * n - 1) % 10 = 3 ∨
          (2 * n - 1) % 10 = 7 ∨ (2 * n - 1) % 10 = 9) := by
        intro hcond
        rw [if_pos hcond] at h
        exact one_ne_zero h
      refine ⟨(n + 2) / 5, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      rw [if_neg (by omega)]

end OMA.P_oeis_a396093

theorem OMA.solution : type_of% @OMA.S_oeis_a396093.main :=
  OMA.P_oeis_a396093.prove_main
