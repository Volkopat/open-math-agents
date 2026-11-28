import OMAStatements.S_oeis_a261594
import Mathlib

open OMA.S_oeis_a261594
open PowerSeries

namespace P261594

abbrev R3 := ZMod 3

theorem three_eq : (3 : R3) = 0 := rfl

theorem two_pow (k : ℕ) : (2 : R3) ^ (k * (k - 1)) = 1 := by
  obtain ⟨j, hj⟩ : Even (k * (k - 1)) := Nat.even_mul_pred_self k
  rw [hj, ← two_mul, pow_mul, show (2 : R3) ^ 2 = 1 from rfl, one_pow]

theorem dig_succ (n : ℕ) : IsNoDigitTwoBase3 n ↔ n % 3 ≠ 2 ∧ IsNoDigitTwoBase3 (n / 3) := by
  unfold IsNoDigitTwoBase3
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun k => ?_⟩
    have := h (k + 1)
    rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this
  · rintro ⟨h0, h⟩ k
    rcases k with _ | k
    · simpa using h0
    · rw [pow_succ', ← Nat.div_div_eq_div_mul]; exact h k

theorem P_iff (n : ℕ) : (∃ m : ℕ, IsNoDigitTwoBase3 m ∧
    (n = 9 * m ∨ n = 9 * m + 1 ∨ n = 9 * m + 3 ∨ n = 9 * m + 4)) ↔ IsNoDigitTwoBase3 n := by
  rw [dig_succ n, dig_succ (n / 3)]
  constructor
  · rintro ⟨m, hm, h⟩
    have e : n / 3 / 3 = m := by omega
    rw [e]
    exact ⟨by omega, by omega, hm⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨n / 3 / 3, h2, by omega⟩

open Classical in
noncomputable def H : PowerSeries R3 := mk fun n => if IsNoDigitTwoBase3 n then 1 else 0

theorem hs3 : HasSubst (X ^ 3 : PowerSeries R3) := HasSubst.X_pow (by norm_num)

theorem H_eq : H = (1 + X) * H.subst (X ^ 3 : PowerSeries R3) := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp [H, coeff_subst_X_pow, IsNoDigitTwoBase3]
  · rw [coeff_succ_X_mul, coeff_subst_X_pow (by norm_num), coeff_subst_X_pow (by norm_num)]
    simp only [H, coeff_mk]
    rw [dig_succ (n + 1)]
    rcases (by omega : (n + 1) % 3 = 0 ∨ (n + 1) % 3 = 1 ∨ (n + 1) % 3 = 2) with h | h | h
    · rw [if_pos (show 3 ∣ n + 1 by omega), if_neg (show ¬ 3 ∣ n by omega)]
      have h2 : ¬ (n + 1) % 3 = 2 := by omega
      by_cases hD : IsNoDigitTwoBase3 ((n + 1) / 3)
      · rw [if_pos ⟨h2, hD⟩, if_pos hD]; simp
      · rw [if_neg (fun hh => hD hh.2), if_neg hD]; simp
    · rw [if_neg (show ¬ 3 ∣ n + 1 by omega), if_pos (show 3 ∣ n by omega),
        show n / 3 = (n + 1) / 3 by omega]
      have h2 : ¬ (n + 1) % 3 = 2 := by omega
      by_cases hD : IsNoDigitTwoBase3 ((n + 1) / 3)
      · rw [if_pos ⟨h2, hD⟩, if_pos hD]; simp
      · rw [if_neg (fun hh => hD hh.2), if_neg hD]; simp
    · rw [if_neg (show ¬ 3 ∣ n + 1 by omega), if_neg (show ¬ 3 ∣ n by omega)]
      simp [h]

theorem H0 : constantCoeff H = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp only [H, coeff_mk]
  rw [if_pos]
  intro k; simp

theorem K_one : H ^ 2 * (1 + X) = 1 := by
  set K := H ^ 2 * (1 + X) with hK
  set S := H.subst (X ^ 3 : PowerSeries R3) with hS
  have hcube : ((1 + X) ^ 3 : PowerSeries R3) = 1 + X ^ 3 := by
    have : ((1 + X) ^ 3 : PowerSeries R3) = 1 + X ^ 3 + C 3 * (X + X ^ 2) := by
      simp only [map_ofNat]; ring
    rw [this, three_eq, map_zero, zero_mul, add_zero]
  have hKs : K = K.subst (X ^ 3 : PowerSeries R3) := by
    have e : K = (1 + X ^ 3) * S ^ 2 := by
      rw [hK, ← hcube]; nth_rewrite 1 [H_eq]; ring
    have t : K.subst (X ^ 3 : PowerSeries R3) = S ^ 2 * (1 + X ^ 3) := by
      rw [hK, ← coe_substAlgHom hs3, map_mul, map_pow, map_add, map_one, coe_substAlgHom, subst_X hs3]
    rw [t, e]; ring
  have hK0 : constantCoeff K = 1 := by
    rw [hK, map_mul, map_pow, H0]; simp
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hK0
    · rw [coeff_one, if_neg (by omega), hKs, coeff_subst_X_pow (by norm_num)]
      by_cases hd : 3 ∣ n
      · rw [if_pos hd]
        have := ih (n / 3) (by omega)
        rw [this, coeff_one, if_neg (by omega)]
        simp
      · rw [if_neg hd]

end P261594

theorem OMA.solution : type_of% @OMA.S_oeis_a261594.main := by
  intro A hA hE n
  set φ := Int.castRingHom (ZMod 3)
  set B := A.map φ with hBdef
  have hF : F261594.map φ * (1 + X) = 1 := by
    have hc : F261594.map φ = mk fun n => (2 : ZMod 3) ^ n := by
      ext n
      simp only [F261594, coeff_map, coeff_mk, φ, map_sum, map_mul, map_pow, map_natCast, map_ofNat]
      simp only [P261594.two_pow, mul_one]
      rw [show (2 : ZMod 3) = 1 + 1 by rfl, add_pow]
      simp
    rw [hc]
    ext n
    rw [mul_add, mul_one, map_add, coeff_mk, coeff_one]
    rcases n with _ | n
    · simp
    · rw [coeff_succ_mul_X, coeff_mk, pow_succ]
      simp only [Nat.succ_ne_zero, if_false]
      have : (2 : ZMod 3) + 1 = 0 := rfl
      linear_combination (2 : ZMod 3) ^ n * this
  have hB2 : B ^ 2 * (1 + X) = 1 := by
    rw [hBdef, ← map_pow, hE, hF]
  have hsq : B ^ 2 = P261594.H ^ 2 := by
    have : (B ^ 2 - P261594.H ^ 2) * (1 + X) = 0 := by
      rw [sub_mul, hB2, P261594.K_one, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have := congrArg constantCoeff h
      simp at this
  have hBH : B = P261594.H := by
    have : (B - P261594.H) * (B + P261594.H) = 0 := by
      rw [show (B - P261594.H) * (B + P261594.H) = B ^ 2 - P261594.H ^ 2 by ring, hsq, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have := congrArg constantCoeff h
      rw [map_add, P261594.H0, hBdef] at this
      have hB0 : constantCoeff (A.map φ) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hA]
        simp
      rw [hB0] at this
      revert this; decide
  have := congrArg (coeff n) hBH
  rw [hBdef, coeff_map] at this
  change ((coeff n A : ℤ) : ZMod 3) = _ at this
  rw [this]
  simp only [P261594.H, coeff_mk]
  by_cases hp : IsNoDigitTwoBase3 n
  · rw [if_pos hp, if_pos ((P261594.P_iff n).mpr hp)]
  · rw [if_neg hp, if_neg (fun h => hp ((P261594.P_iff n).mp h))]
