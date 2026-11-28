import OMAStatements.S_oeis_a122648
import Mathlib

namespace R122648
open OMA.S_oeis_a122648 PowerSeries

lemma hX2 : HasSubst (X ^ 2 : ℚ⟦X⟧) := HasSubst.X_pow (by norm_num)

lemma hC2X : HasSubst (C 2 * X : ℚ⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp)

lemma C2 : (C 2 : ℚ⟦X⟧) = 2 := by
  first
  | exact map_ofNat C 2
  | simp
  | (ext n; simp [coeff_C])

lemma dCX : PowerSeries.derivative ℚ (C 2 * X : ℚ⟦X⟧) = C 2 := by
  first
  | rw [Derivation.leibniz, derivative_X, derivative_C, smul_zero, add_zero, smul_eq_mul,
      mul_one]
  | simp [Derivation.leibniz]

lemma dE : PowerSeries.derivative ℚ E = C 2 * (X * E) := by
  unfold E
  rw [derivative_subst hX2, derivative_exp, derivative_pow, derivative_X, C2]
  first
  | (rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one, Nat.cast_ofNat]; ring)
  | (norm_num <;> ring)

lemma dH : PowerSeries.derivative ℚ H = C 2 * H := by
  unfold H
  rw [derivative_subst hC2X, derivative_exp, dCX]
  ring

lemma dG : PowerSeries.derivative ℚ (E * H) = C 2 * (X * (E * H)) + C 2 * (E * H) := by
  rw [Derivation.leibniz, dE, dH]
  first
  | (rw [smul_eq_mul, smul_eq_mul]; ring)
  | (simp only [smul_eq_mul]; ring)

lemma e_rec (k : ℕ) : coeff (k + 2) E * ((k : ℚ) + 2) = 2 * coeff k E := by
  have h := congrArg (coeff (k + 1)) dE
  rw [coeff_derivative, show k + 1 + 1 = k + 2 from rfl] at h
  rw [coeff_C_mul, coeff_succ_X_mul] at h
  push_cast at h
  linear_combination h

lemma g_rec (k : ℕ) :
    coeff (k + 2) (E * H) * ((k : ℚ) + 2) = 2 * coeff k (E * H) + 2 * coeff (k + 1) (E * H) := by
  have h := congrArg (coeff (k + 1)) dG
  rw [coeff_derivative, show k + 1 + 1 = k + 2 from rfl] at h
  rw [map_add, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul] at h
  push_cast at h
  linear_combination h

noncomputable def b (k : ℕ) : ℚ := (k.factorial : ℚ) * coeff k (E * H)

noncomputable def c (k : ℕ) : ℚ := (k.factorial : ℚ) * coeff k E

lemma f1 (k : ℕ) : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
  rw [Nat.factorial_succ k]
  push_cast
  ring

lemma f2 (k : ℕ) : ((k + 2).factorial : ℚ) = ((k : ℚ) + 2) * ((k + 1).factorial : ℚ) := by
  rw [show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ (k + 1)]
  push_cast
  ring

lemma a_eq (k : ℕ) : a k = (b k + c k) / 2 := by
  simp only [a, b, c, egf, coeff_C_mul, mul_add, mul_one, map_add]
  ring

lemma c_rec (k : ℕ) : c (k + 2) = 2 * ((k : ℚ) + 1) * c k := by
  have h := e_rec k
  unfold c
  rw [f2, f1]
  linear_combination ((k : ℚ) + 1) * (k.factorial : ℚ) * h

lemma b_rec (k : ℕ) : b (k + 2) = 2 * b (k + 1) + 2 * ((k : ℚ) + 1) * b k := by
  have h := g_rec k
  unfold b
  rw [f2, f1]
  linear_combination ((k : ℚ) + 1) * (k.factorial : ℚ) * h

end R122648

theorem OMA.solution : type_of% @OMA.S_oeis_a122648.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  simp only [R122648.a_eq]
  have B2 := R122648.b_rec (m + 2)
  have B0 := R122648.b_rec m
  have C2 := R122648.c_rec (m + 2)
  have C1 := R122648.c_rec (m + 1)
  have C0 := R122648.c_rec m
  rw [show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at B2
  rw [show m + 2 + 2 = m + 4 by omega] at C2
  rw [show m + 1 + 2 = m + 3 by omega] at C1
  push_cast at B2 C2 C1 ⊢
  linear_combination (1 / 2 : ℚ) * (B2 - 2 * ((m : ℚ) + 2) * B0 + C2 - 2 * C1
    - 2 * ((m : ℚ) + 2) * C0)
