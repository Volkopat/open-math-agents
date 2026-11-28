import OMAStatements.S_oeis_a001723
import Mathlib

-- Problem: A001723: Generalized Stirling numbers, [n+8,8]_5.
-- Upstream: formal-conjectures statements/oeis-a001723.lean:0 (declaration OMA.S_oeis_a001723.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let Q(N) be the product of x + 5 + t for t < N. It is the rising factorial of length N
composed with x + 5, and the coefficients of the rising factorial are the unsigned Stirling
numbers of the first kind, so the coefficient of x^r in Q(N) is the sum over j of
c(N,j) 5^(j-r) binomial(j,r); in particular a(n) is the coefficient of x^3 in Q(n+3). From
Q(N+1) = Q(N) (x + 5 + N) the coefficients satisfy c_0(N+1) = (5+N) c_0(N) and
c_(k+1)(N+1) = c_k(N) + (5+N) c_(k+1)(N), and substituting these turns the recurrence into a
polynomial identity. -/

namespace A001723Aux

open Polynomial OMA.S_oeis_a001723

/-- The product of x + 5 + t for t < N. -/
noncomputable def Q (N : ℕ) : ℤ[X] := ∏ t ∈ Finset.range N, (X + C (5 + (t : ℤ)))

theorem Q_succ (N : ℕ) : Q (N + 1) = Q N * (X + C (5 + (N : ℤ))) := by
  unfold Q
  rw [Finset.prod_range_succ]

theorem c_succ (N k : ℕ) :
    (Q (N + 1)).coeff (k + 1) = (Q N).coeff k + (5 + (N : ℤ)) * (Q N).coeff (k + 1) := by
  rw [Q_succ, mul_add, coeff_add, coeff_mul_X, coeff_mul_C]
  ring

theorem c_zero (N : ℕ) : (Q (N + 1)).coeff 0 = (5 + (N : ℤ)) * (Q N).coeff 0 := by
  rw [Q_succ, mul_add, coeff_add, coeff_mul_X_zero, coeff_mul_C]
  ring

theorem Q_eq (N : ℕ) : Q N = (ascPochhammer ℤ N).comp (X + C 5) := by
  induction N with
  | zero => simp [Q]
  | succ N ih =>
    rw [Q_succ, ih, ascPochhammer_succ_right, mul_comp, add_comp, X_comp, natCast_comp]
    congr 1
    rw [C_add]
    simp [add_assoc]

theorem stirling_zero_mul (n : ℕ) : Nat.stirlingFirst n 0 * n = 0 := by
  cases n <;> simp

theorem coeff_asc (n k : ℕ) :
    (ascPochhammer ℤ n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_natCast]
    cases k with
    | zero =>
      rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, mul_zero, zero_add, ih,
        Nat.stirlingFirst_succ_zero, Nat.cast_zero]
      exact_mod_cast stirling_zero_mul n
    | succ k =>
      rw [Polynomial.coeff_mul_X, ih, ih, Nat.stirlingFirst_succ_succ]
      push_cast
      ring

theorem bridge (N r : ℕ) :
    (Q N).coeff r = ∑ j ∈ Finset.range (N + 1),
      (Nat.stirlingFirst N j : ℤ) * (5 ^ (j - r) * (j.choose r : ℤ)) := by
  rw [Q_eq, comp_eq_sum_left,
    Polynomial.sum_over_range' _ (fun j => by simp) (N + 1) (by
      rw [ascPochhammer_natDegree]
      omega), finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_C_mul, coeff_X_add_C_pow, coeff_asc]

theorem a_eq (n : ℕ) : a n = (Q (n + 3)).coeff 3 := by
  rw [bridge]
  have e : n + 3 + 1 = 3 + (n + 1) := by ring
  rw [e, Finset.sum_range_add]
  have hz : ∑ j ∈ Finset.range 3,
      (Nat.stirlingFirst (n + 3) j : ℤ) * (5 ^ (j - 3) * (j.choose 3 : ℤ)) = 0 := by
    simp [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt]
  rw [hz, zero_add]
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_sub_cancel_left, Nat.add_comm 3 k]
  ring

theorem rec (M : ℕ) :
    (Q (M + 4)).coeff 3 + 2 * (-2 * ((M : ℤ) + 1) - 11) * (Q (M + 3)).coeff 3 +
      (6 * ((M : ℤ) + 1) ^ 2 + 60 * ((M : ℤ) + 1) + 151) * (Q (M + 2)).coeff 3 -
      (2 * ((M : ℤ) + 1) + 9) * (2 * ((M : ℤ) + 1) ^ 2 + 18 * ((M : ℤ) + 1) + 41) *
        (Q (M + 1)).coeff 3 +
      (((M : ℤ) + 1) + 4) ^ 4 * (Q M).coeff 3 = 0 := by
  have a4 := c_succ (M + 3) 2
  have a3 := c_succ (M + 2) 2
  have a2 := c_succ (M + 1) 2
  have a1 := c_succ M 2
  have b3 := c_succ (M + 2) 1
  have b2 := c_succ (M + 1) 1
  have b1 := c_succ M 1
  have d2 := c_succ (M + 1) 0
  have d1 := c_succ M 0
  have z1 := c_zero M
  push_cast at a4 a3 a2 b3 b2 d2
  simp only [Nat.reduceAdd] at a4 a3 a2 a1 b3 b2 b1 d2 d1
  rw [a4, a3, b3, a2, b2, d2, a1, b1, d1, z1]
  ring

end A001723Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a001723.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  rw [e1, e2, e3, Nat.add_sub_cancel, A001723Aux.a_eq, A001723Aux.a_eq, A001723Aux.a_eq,
    A001723Aux.a_eq, A001723Aux.a_eq]
  have h := A001723Aux.rec (m + 3)
  have f4 : m + 3 + 4 = m + 4 + 3 := by ring
  have f2 : m + 3 + 2 = m + 2 + 3 := by ring
  have f1 : m + 3 + 1 = m + 1 + 3 := by ring
  rw [f4, f2, f1] at h
  push_cast at h ⊢
  linear_combination h
