import OMAStatements.S_oeis_a053532
import Mathlib

namespace A053532

open OMA.S_oeis_a053532 PowerSeries in
lemma key (k : ℕ) :
    2 * ((Nat.centralBinom (k + 1) : ℚ) / (4 : ℚ) ^ (k + 1) * ((k : ℚ) + 1))
      = (2 * (k : ℚ) + 1) * ((Nat.centralBinom k : ℚ) / (4 : ℚ) ^ k) := by
  have hc := Nat.succ_mul_centralBinom_succ k
  have hc' : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
    exact_mod_cast hc
  have hc2 : (Nat.centralBinom (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff (by positivity)]
    linarith
  have hp : (4 : ℚ) ^ (k + 1) = 4 * 4 ^ k := by ring
  rw [hc2, hp]
  field_simp
  ring

open OMA.S_oeis_a053532 PowerSeries in
lemma hY : (C 2 - C 2 * X) * (derivative ℚ) Y = Y := by
  ext n
  have e : (C 2 - C 2 * X) * (derivative ℚ) Y
      = C 2 * (derivative ℚ) Y - C 2 * (X * (derivative ℚ) Y) := by ring
  rw [e, map_sub, coeff_C_mul, coeff_C_mul]
  rcases n with _ | m
  · rw [coeff_zero_X_mul, coeff_derivative]
    simp only [Y, coeff_mk]
    have h0 := key 0
    push_cast at h0 ⊢
    linear_combination h0
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    simp only [Y, coeff_mk]
    have h1 := key (m + 1)
    push_cast at h1 ⊢
    linear_combination h1

open OMA.S_oeis_a053532 PowerSeries in
lemma dP : (derivative ℚ) P = C (-1 / 2) * (1 + X + X ^ 2) := by
  have h6 : (C 6 : PowerSeries ℚ) = 6 := map_ofNat C 6
  have h3 : (C 3 : PowerSeries ℚ) = 3 := map_ofNat C 3
  have h2 : (C 2 : PowerSeries ℚ) = 2 := map_ofNat C 2
  have e : P = C (-1 / 12) * (C 6 * X ^ 1 + C 3 * X ^ 2 + C 2 * X ^ 3) := by
    unfold P
    rw [h6, h3, h2]
    ring
  have e' : (C (-1 / 2) * (1 + X + X ^ 2) : PowerSeries ℚ)
      = C (-1 / 2) * (X ^ 0 + X ^ 1 + X ^ 2) := by ring
  ext n
  rw [coeff_derivative, e, e']
  simp only [coeff_C_mul, map_add, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · norm_num
  · norm_num
  · norm_num
  · have a1 : n + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have a2 : n + 1 + 1 + 1 + 1 ≠ 2 := by omega
    have a3 : n + 1 + 1 + 1 + 1 ≠ 3 := by omega
    have b0 : n + 1 + 1 + 1 ≠ 0 := by omega
    have b1 : n + 1 + 1 + 1 ≠ 1 := by omega
    have b2 : n + 1 + 1 + 1 ≠ 2 := by omega
    rw [if_neg a1, if_neg a2, if_neg a3, if_neg b0, if_neg b1, if_neg b2]
    ring

open OMA.S_oeis_a053532 PowerSeries in
lemma dE : (derivative ℚ) E = E * (derivative ℚ) P := by
  unfold E
  have hP : HasSubst P := HasSubst.of_constantCoeff_zero' (by simp [P])
  rw [derivative_subst hP, derivative_exp]

open OMA.S_oeis_a053532 PowerSeries in
lemma hg : (C 2 - C 2 * X) * (derivative ℚ) egf = X ^ 3 * egf := by
  unfold egf
  have hl : (derivative ℚ) (Y * E) = Y * (derivative ℚ) E + E * (derivative ℚ) Y := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hcc : (C 2 : PowerSeries ℚ) * C (-1 / 2) = -1 := by
    rw [← map_mul]
    norm_num
  have hP2 : (C 2 - C 2 * X) * (derivative ℚ) P = X ^ 3 - 1 := by
    rw [dP]
    linear_combination (1 - X ^ 3) * hcc
  rw [hl, dE]
  linear_combination E * hY + (Y * E) * hP2

open OMA.S_oeis_a053532 PowerSeries in
lemma hcoef (m : ℕ) :
    2 * (coeff (m + 4) egf * ((m : ℚ) + 4)) - 2 * (coeff (m + 3) egf * ((m : ℚ) + 3))
      = coeff m egf := by
  have h := congrArg (coeff (m + 3)) hg
  have e1 : (C 2 - C 2 * X) * (derivative ℚ) egf
      = C 2 * (derivative ℚ) egf - C 2 * (X * (derivative ℚ) egf) := by ring
  have e3 : m + 3 - 3 = m := by omega
  have hL : coeff (m + 3) (C 2 * (derivative ℚ) egf - C 2 * (X * (derivative ℚ) egf))
      = 2 * (coeff (m + 3 + 1) egf * ((m : ℚ) + 3 + 1))
        - 2 * (coeff (m + 2 + 1) egf * ((m : ℚ) + 2 + 1)) := by
    rw [map_sub, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    push_cast
    ring
  have hR : coeff (m + 3) (X ^ 3 * egf) = coeff m egf := by
    rw [coeff_X_pow_mul', if_pos (by omega), e3]
  rw [e1, hL, hR] at h
  have e4 : coeff (m + 3 + 1) egf = coeff (m + 4) egf := rfl
  have e5 : coeff (m + 2 + 1) egf = coeff (m + 3) egf := rfl
  rw [e4, e5] at h
  linarith

end A053532

theorem OMA.solution : type_of% @OMA.S_oeis_a053532.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e4 : m + 4 - 4 = m := by omega
  rw [e1, e4]
  unfold OMA.S_oeis_a053532.a
  have h := A053532.hcoef m
  have f3 : ((m + 3).factorial : ℚ)
      = ((m : ℚ) + 3) * (((m : ℚ) + 2) * (((m : ℚ) + 1) * (m.factorial : ℚ))) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f4 : ((m + 4).factorial : ℚ)
      = ((m : ℚ) + 4) * (((m : ℚ) + 3) * (((m : ℚ) + 2) * (((m : ℚ) + 1) * (m.factorial : ℚ)))) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [f3, f4]
  push_cast
  linear_combination ((m.factorial : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3)) * h
