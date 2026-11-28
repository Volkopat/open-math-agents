import OMAStatements.S_oeis_a285474
import Mathlib

/-!
With rule 3 a cell turns on exactly when its four neighbors are off.
The isolated origin and the complement of its four neighbors form a two-cycle.
-/

open OMA.S_oeis_a285474 PowerSeries

namespace RuleThreeDiagonal

private theorem step (n : ℕ) (x y : ℤ) : state (n+1) (x,y) = true ↔
    state n (x+1,y) = false ∧ state n (x-1,y) = false ∧
    state n (x,y+1) = false ∧ state n (x,y-1) = false := by
  simp only [state, nbrs, List.countP_cons, List.countP_nil]
  cases state n (x,y) <;> cases state n (x+1,y) <;> cases state n (x-1,y) <;>
    cases state n (x,y+1) <;> cases state n (x,y-1) <;> decide

private def cross (x y : ℤ) : Prop :=
  (x = 0 ∧ (y = 1 ∨ y = -1)) ∨ (y = 0 ∧ (x = 1 ∨ x = -1))

private theorem odd_of_even (n : ℕ)
    (h : ∀ x y : ℤ, state (2*n) (x,y) = true ↔ x=0 ∧ y=0) (x y : ℤ) :
    state (2*n+1) (x,y) = true ↔ ¬ cross x y := by
  rw [step]
  simp only [Bool.eq_false_iff, ne_eq, h, cross]
  omega

private theorem even_stage (n : ℕ) (x y : ℤ) :
    state (2*n) (x,y) = true ↔ x=0 ∧ y=0 := by
  induction n generalizing x y with
  | zero => simp [state, Prod.ext_iff]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, step]
    simp only [Bool.eq_false_iff, ne_eq, odd_of_even n ih, not_not, cross]
    omega

private theorem even_val (n : ℕ) : a (2*n) = 10^(2*n) := by
  simp [a, even_stage, Finset.sum_ite_eq']

private theorem odd_val (n : ℕ) : a (2*n+1) = ∑ j ∈ Finset.range (2*n+2), 10^j := by
  have h (j : ℕ) : state (2*n+1) ((j:ℤ),(j:ℤ)) = true :=
    (odd_of_even n (even_stage n) _ _).2 (by unfold cross; omega)
  simpa only [a, h, if_true, show 2*n+2-1=2*n+1 by omega, show 2*n+1+1=2*n+2 by omega] using Finset.sum_range_reflect (fun i : ℕ => (10:ℕ)^i) (2*n+2)

private theorem closed_form (n : ℕ) :
    (a n : ℚ) = (-1 - (-10) ^ n + (-1) ^ n + 19 * 10 ^ n) / 18 := by
  obtain ⟨i,hi|hi⟩ : ∃ i, n=2*i ∨ n=2*i+1 := ⟨n/2,by omega⟩
  · subst n
    rw [even_val]
    push_cast
    norm_num [pow_mul]
    ring
  · subst n
    have h := geom_sum_mul (10 : ℚ) (2*i+2)
    rw [show 2*i+2 = 2*i+1+1 by omega, pow_succ, pow_succ, pow_mul] at h
    rw [odd_val]
    push_cast
    norm_num [pow_add, pow_mul] at h ⊢
    linarith

private theorem recurrence (n : ℕ) :
    (a (n+4) : ℤ) = 101 * a (n+2) - 100 * a n := by
  have h : (a (n+4) : ℚ) = 101 * a (n+2) - 100 * a n := by
    rw [closed_form, closed_form, closed_form]
    norm_num [pow_add]
    ring
  exact_mod_cast h

private theorem coefficients (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) := (map_ofNat C n).symm

private theorem generating :
    A = (1 + 11 * X - X^2) * ((1-X)*(1+X)*(1-10*X)*(1+10*X))⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
  rw [show A*((1-X)*(1+X)*(1-10*X)*(1+10*X)) =
    A - 101*(X*(X*A)) + 100*(X*(X*(X*(X*A)))) by ring]
  ext n
  have coeff_A (i : ℕ) : coeff i A = (a i : ℚ) := coeff_mk _ _
  rcases n with _ | _ | _ | _ | m
  all_goals simp only [map_add, map_sub, coefficients, coeff_C_mul, coeff_succ_X_mul,
    coeff_zero_X_mul, coeff_A, pow_succ, pow_zero, one_mul, coeff_X, coeff_one]
  · norm_num [closed_form]
  · norm_num [closed_form]
  · norm_num [closed_form]
  · norm_num [closed_form]
  · have h : (a (m+4) : ℚ) = 101*a (m+2)-100*a m := by exact_mod_cast recurrence m
    simp at *
    linarith

end RuleThreeDiagonal

theorem OMA.solution : type_of% @OMA.S_oeis_a285474.main := by
  refine ⟨RuleThreeDiagonal.generating, RuleThreeDiagonal.closed_form, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n=m+4 := ⟨n-4, by omega⟩
  simpa using RuleThreeDiagonal.recurrence m
