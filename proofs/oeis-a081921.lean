import OMAStatements.S_oeis_a081921
import Mathlib

namespace A081921

open OMA.S_oeis_a081921 PowerSeries in
lemma coeff_E (n : ℕ) : coeff n E = (3 : ℚ) ^ n / (n.factorial : ℚ) := by
  have h : E = rescale (3 : ℚ) (exp ℚ) := by
    unfold E
    rw [rescale_eq_subst, smul_eq_C_mul]
  rw [h, coeff_rescale, coeff_exp]
  simp [div_eq_mul_inv]

open OMA.S_oeis_a081921 PowerSeries in
lemma coeff_B (n : ℕ) :
    coeff n B = if 2 ∣ n then (Nat.centralBinom (n / 2) : ℚ) / (4 : ℚ) ^ (n / 2) else 0 := by
  unfold B
  rw [coeff_subst_X_pow (by norm_num)]
  simp [Y]

open OMA.S_oeis_a081921 PowerSeries in
lemma dE : (derivative ℚ) E = C 3 * E := by
  ext n
  rw [coeff_derivative, coeff_C_mul, coeff_E, coeff_E, Nat.factorial_succ]
  have h : (n.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

open OMA.S_oeis_a081921 PowerSeries in
lemma hB : (1 - X ^ 2) * (derivative ℚ) B = X * B := by
  ext n
  have e : (1 - X ^ 2) * (derivative ℚ) B = (derivative ℚ) B - X ^ 2 * (derivative ℚ) B := by
    ring
  rw [e, map_sub, coeff_X_pow_mul', coeff_derivative]
  rcases n with _ | _ | m
  · norm_num [coeff_B]
  · have c1 : Nat.centralBinom 1 = 2 := by decide
    norm_num [coeff_B, c1]
  · rw [if_pos (by omega), coeff_derivative, coeff_succ_X_mul]
    have e2 : m + 1 + 1 - 2 = m := by omega
    rw [e2, coeff_B, coeff_B]
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rw [if_neg (by omega), if_neg (by omega)]
      simp
    · rw [if_pos (by omega), if_pos (by omega)]
      have d1 : (2 * k + 1 + 1 + 1 + 1) / 2 = k + 2 := by omega
      have d2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [d1, d2]
      have hc := Nat.succ_mul_centralBinom_succ (k + 1)
      have hc' : ((k : ℚ) + 2) * (Nat.centralBinom (k + 2) : ℚ)
          = 2 * (2 * ((k : ℚ) + 1) + 1) * (Nat.centralBinom (k + 1) : ℚ) := by
        exact_mod_cast hc
      have hc2 : (Nat.centralBinom (k + 2) : ℚ)
          = 2 * (2 * ((k : ℚ) + 1) + 1) * (Nat.centralBinom (k + 1) : ℚ) / ((k : ℚ) + 2) := by
        rw [eq_div_iff (by positivity)]
        linarith
      have hp : (4 : ℚ) ^ (k + 2) = 4 * 4 ^ (k + 1) := by ring
      rw [hc2, hp]
      push_cast
      field_simp
      ring

open OMA.S_oeis_a081921 PowerSeries in
lemma hg : (1 - X ^ 2) * (derivative ℚ) egf = (C 3 - C 3 * X ^ 2 + X) * egf := by
  unfold egf
  have hl : (derivative ℚ) (E * B) = E * (derivative ℚ) B + B * (derivative ℚ) E := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  rw [hl, dE]
  linear_combination E * hB

open OMA.S_oeis_a081921 PowerSeries in
lemma hcoef (m : ℕ) :
    coeff (m + 3) egf * ((m : ℚ) + 3) - coeff (m + 1) egf * ((m : ℚ) + 1)
      = 3 * coeff (m + 2) egf - 3 * coeff m egf + coeff (m + 1) egf := by
  have h := congrArg (coeff (m + 2)) hg
  have e1 : (1 - X ^ 2) * (derivative ℚ) egf
      = (derivative ℚ) egf - X ^ 2 * (derivative ℚ) egf := by ring
  have e2 : (C 3 - C 3 * X ^ 2 + X) * egf = C 3 * egf - C 3 * (X ^ 2 * egf) + X * egf := by ring
  have e3 : m + 2 - 2 = m := by omega
  have hL : coeff (m + 2) ((derivative ℚ) egf - X ^ 2 * (derivative ℚ) egf)
      = coeff (m + 2 + 1) egf * ((m : ℚ) + 2 + 1) - coeff (m + 1) egf * ((m : ℚ) + 1) := by
    rw [map_sub, coeff_X_pow_mul', if_pos (by omega), coeff_derivative, coeff_derivative, e3]
    push_cast
    ring
  have hR : coeff (m + 2) (C 3 * egf - C 3 * (X ^ 2 * egf) + X * egf)
      = 3 * coeff (m + 2) egf - 3 * coeff m egf + coeff (m + 1) egf := by
    rw [map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
      coeff_succ_X_mul, e3]
  rw [e1, e2, hL, hR] at h
  have e4 : coeff (m + 2 + 1) egf = coeff (m + 3) egf := rfl
  rw [e4] at h
  linarith

end A081921

theorem OMA.solution : type_of% @OMA.S_oeis_a081921.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  unfold OMA.S_oeis_a081921.a
  have h := A081921.hcoef m
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * (((m : ℚ) + 1) * (m.factorial : ℚ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((m + 3).factorial : ℚ)
      = ((m : ℚ) + 3) * (((m : ℚ) + 2) * (((m : ℚ) + 1) * (m.factorial : ℚ))) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [f1, f2, f3]
  push_cast
  linear_combination ((m.factorial : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2)) * h
