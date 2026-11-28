import OMAStatements.S_oeis_a396724
import Mathlib

/-! Following @caa1982 (#22681), use the standard product-degree bound and
factorial product formula for the same interpolation proof. -/

open OMA.S_oeis_a396724
open Polynomial

namespace P396724

/-- The explicit polynomial `1 - (1/n!) * prod_{k<n} (k + 2 - X)`. -/
noncomputable def q (n : ℕ) : ℚ[X] :=
  1 - C ((n.factorial : ℚ)⁻¹) * ∏ k ∈ Finset.range n, (C ((k : ℚ) + 2) - X)

theorem deg_prod (n : ℕ) : (∏ k ∈ Finset.range n, (C ((k : ℚ) + 2) - X)).degree ≤ (n : WithBot ℕ) := by
  have h (a : ℚ) : (C a - X).degree = 1 := by
    rw [← degree_neg, neg_sub, degree_X_sub_C]
  convert degree_prod_le (Finset.range n) (fun k => C ((k : ℚ) + 2) - X) using 1
  simp_rw [h]
  simp

theorem deg_q (n : ℕ) : (q n).degree < (Finset.Icc 1 (n + 1)).card := by
  rw [Nat.card_Icc, show n + 1 + 1 - 1 = n + 1 by omega]
  refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt degree_one_le (by exact_mod_cast Nat.succ_pos n)
  · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add degree_C_le (deg_prod n)) ?_
    rw [zero_add]; exact_mod_cast Nat.lt_succ_self n

theorem eval_prod_one (n : ℕ) :
    (∏ k ∈ Finset.range n, (C ((k : ℚ) + 2) - X)).eval (1 : ℚ) = (n.factorial : ℚ) := by
  rw [Nat.factorial_eq_prod_range_add_one]
  norm_num [eval_prod, add_sub_assoc, -Finset.prod_range_add_one_eq_factorial]

theorem eval_prod_node (n i : ℕ) (h1 : 2 ≤ i) (h2 : i ≤ n + 1) :
    (∏ k ∈ Finset.range n, (C ((k : ℚ) + 2) - X)).eval (i : ℚ) = 0 := by
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := i - 2) (Finset.mem_range.mpr (by omega))
  simp only [eval_sub, eval_C, eval_X]
  rw [Nat.cast_sub h1]; ring

theorem p_eq (n : ℕ) : p n = q n := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq
  · intro x _ y _ h; simpa using h
  · exact deg_q n
  · intro i hi
    rw [Finset.mem_Icc] at hi
    unfold q
    rcases Nat.lt_or_ge i 2 with h | h
    · obtain rfl : i = 1 := by omega
      rw [if_pos rfl, eval_sub, eval_mul, eval_C, eval_one, Nat.cast_one, eval_prod_one]
      have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp; ring
    · rw [if_neg (by omega), eval_sub, eval_mul, eval_prod_node n i h hi.2]
      simp

/-- `u n = 4^n * (1/n!) * prod_{k<n} (k + 2 - c)` at `c = -3/2`. -/
noncomputable def u (n : ℕ) : ℚ :=
  4 ^ n * (n.factorial : ℚ)⁻¹ * ∏ k ∈ Finset.range n, ((k : ℚ) + 2 - (-3 / 2))

theorem a_eq (n : ℕ) : a n = (u n - 4 ^ n) / 2 := by
  rw [a, p_eq, q, u]
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_prod, eval_X]
  ring

theorem u_succ (n : ℕ) : ((n : ℚ) + 1) * u (n + 1) = 4 * ((n : ℚ) + 2 - (-3 / 2)) * u n := by
  rw [u, u, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  ring

end P396724

theorem OMA.solution : type_of% @OMA.S_oeis_a396724.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, P396724.a_eq, P396724.a_eq,
    P396724.a_eq]
  have h1 := P396724.u_succ (m + 1)
  have h0 := P396724.u_succ m
  push_cast at h1 h0 ⊢
  rw [pow_succ, pow_succ]
  linear_combination (1 / 2 : ℚ) * h1 - (2 : ℚ) * h0
