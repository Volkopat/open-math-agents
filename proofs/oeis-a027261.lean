import OMAStatements.S_oeis_a027261
import Mathlib

-- Problem: A027261: a(n) = Sum_{k=0..2n} (k+1) * A025177(n, k).
-- Upstream: formal-conjectures statements/oeis-a027261.lean:0 (declaration OMA.S_oeis_a027261.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Row n + 1 of the array is the coefficient list of P = (1 + x^2) (1 + x + x^2)^n, by induction
from the recurrence. Hence a(n + 1) is the value at 1 of the derivative of x P, which the product
rule evaluates to 2 (n + 2) 3^n. The recurrence and the generating function follow from this
closed form together with a(0) = 1. -/

namespace A027261Aux

open Polynomial OMA.S_oeis_a027261

/-- The row polynomial of row n + 1. -/
noncomputable def P (n : ℕ) : ℤ[X] := (1 + X ^ 2) * (1 + X + X ^ 2) ^ n

theorem T_eq (n k : ℕ) : T (n + 1) k = (P n).coeff k := by
  induction n generalizing k with
  | zero =>
    have hP : P 0 = 1 + X ^ 2 := by simp [P]
    rw [hP, coeff_add, coeff_one, coeff_X_pow]
    show (if k = 0 ∨ k = 2 then (1 : ℤ) else 0) = _
    by_cases h0 : k = 0
    · subst h0
      simp
    · by_cases h2 : k = 2
      · subst h2
        simp
      · simp [h0, h2]
  | succ n ih =>
    have hP : P (n + 1) = P n + P n * X ^ 1 + P n * X ^ 2 := by
      simp only [P]
      ring
    rw [hP, coeff_add, coeff_add, coeff_mul_X_pow', coeff_mul_X_pow']
    show (if 2 ≤ k then T (n + 1) (k - 2) else 0) + (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      T (n + 1) k = _
    rw [ih, ih, ih]
    ring

theorem natDegree_P (n : ℕ) : (P n).natDegree ≤ 2 * n + 2 := by
  unfold P
  have h1 : (1 + X ^ 2 : ℤ[X]).natDegree ≤ 2 := by compute_degree
  have h2 : (1 + X + X ^ 2 : ℤ[X]).natDegree ≤ 2 := by compute_degree
  calc ((1 + X ^ 2) * (1 + X + X ^ 2) ^ n : ℤ[X]).natDegree
      ≤ (1 + X ^ 2 : ℤ[X]).natDegree + ((1 + X + X ^ 2) ^ n : ℤ[X]).natDegree := natDegree_mul_le
    _ ≤ 2 + n * 2 := Nat.add_le_add h1 ((natDegree_pow_le).trans (Nat.mul_le_mul_left n h2))
    _ = 2 * n + 2 := by ring

theorem a_eq_eval (n : ℕ) : a (n + 1) = (derivative (X * P n)).eval 1 := by
  have hdeg : (derivative (X * P n)).natDegree < 2 * (n + 1) + 1 := by
    have h1 : (X * P n).natDegree ≤ 2 * n + 3 := by
      calc (X * P n).natDegree ≤ (X : ℤ[X]).natDegree + (P n).natDegree := natDegree_mul_le
        _ ≤ 1 + (2 * n + 2) := Nat.add_le_add natDegree_X_le (natDegree_P n)
        _ = 2 * n + 3 := by ring
    have h2 := natDegree_derivative_le (X * P n)
    omega
  rw [eval_eq_sum_range' hdeg]
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_derivative, coeff_X_mul, T_eq, one_pow, mul_one]
  ring

theorem eval_closed (n : ℕ) : (derivative (X * P n)).eval 1 = 2 * ((n : ℤ) + 2) * 3 ^ n := by
  cases n with
  | zero =>
    simp [P]
  | succ j =>
    simp only [P, derivative_mul, derivative_pow, derivative_add, derivative_one, derivative_X,
      eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_C, eval_zero, Nat.add_sub_cancel]
    push_cast
    ring

theorem a_succ (n : ℕ) : a (n + 1) = 2 * ((n : ℤ) + 2) * 3 ^ n := by
  rw [a_eq_eval, eval_closed]

theorem a_zero : a 0 = 1 := by
  simp [a, T]

end A027261Aux

namespace A027261Gf

open PowerSeries OMA.S_oeis_a027261

theorem c_succ (f : ℤ⟦X⟧) (c : ℤ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℤ⟦X⟧) (c : ℤ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem coeff_quad (u v w : ℤ) (m : ℕ) :
    coeff m (C u + C v * X + C w * X * X : ℤ⟦X⟧) =
      if m = 0 then u else if m = 1 then v else if m = 2 then w else 0 := by
  rcases m with _ | _ | _ | m
  · simp only [map_add, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_C, add_zero, if_true]
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp

theorem gf : PowerSeries.mk a * (1 - 3 * X) ^ 2 = 1 - 2 * X + 3 * X ^ 2 := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have h3 : (C 3 : ℤ⟦X⟧) = 3 := map_ofNat C 3
  have h2 : (C (-2) : ℤ⟦X⟧) = -2 := by rw [map_neg, map_ofNat]
  have hl : PowerSeries.mk a * (1 - 3 * X) ^ 2 =
      PowerSeries.mk a * (1 - C 3 * X) * (1 - C 3 * X) := by
    rw [h3]
    ring
  have hr : (1 - 2 * X + 3 * X ^ 2 : ℤ⟦X⟧) = C 1 + C (-2) * X + C 3 * X * X := by
    rw [h1, h2, h3]
    ring
  rw [hl, hr]
  ext m
  rw [coeff_quad]
  rcases m with _ | _ | _ | m
  · simp only [c_zero, PowerSeries.coeff_mk, A027261Aux.a_zero]
    simp
  · simp only [c_succ, c_zero, PowerSeries.coeff_mk]
    rw [A027261Aux.a_zero, A027261Aux.a_succ 0]
    simp
  · simp only [c_succ, PowerSeries.coeff_mk]
    rw [A027261Aux.a_zero, A027261Aux.a_succ 0, A027261Aux.a_succ 1]
    simp
  · simp only [c_succ, PowerSeries.coeff_mk]
    rw [A027261Aux.a_succ (m + 2), A027261Aux.a_succ (m + 1), A027261Aux.a_succ m]
    simp
    ring

end A027261Gf

theorem OMA.solution : type_of% @OMA.S_oeis_a027261.main := by
  refine ⟨?_, ?_, A027261Gf.gf⟩
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [A027261Aux.a_succ, Nat.add_sub_cancel]
    push_cast
    ring
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    have e1 : j + 3 - 1 = j + 2 := by omega
    have e2 : j + 3 - 2 = j + 1 := by omega
    rw [e1, e2, A027261Aux.a_succ (j + 2), A027261Aux.a_succ (j + 1), A027261Aux.a_succ j]
    push_cast
    ring
