import OMAStatements.S_oeis_a348482

/-!
Original proof: @thtsben2, PR #27732.
Proof simplification: @rgoldman73-dev. Use Mathlib's sum of iterated
polynomial derivatives to invert the operator p ↦ p - derivative p.
-/

open Finset Polynomial OMA.S_oeis_a348482

namespace OMA.A348482

private lemma t_zero_of_lt {n k : ℕ} (h : n < k) : T n k = 0 := by
  simp [T, Finset.Icc_eq_empty_of_lt h]

private lemma t_step {n k : ℕ} (h : k ≤ n) :
    T n k = 1 + (k + 1 : ℚ) * T n (k + 1) := by
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hg : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hi : Icc k n = insert k (Icc (k + 1) n) := by
    ext i
    simp only [mem_Icc, mem_insert]
    omega
  unfold T
  rw [hi, sum_insert (by simp), Nat.factorial_succ]
  push_cast
  field_simp

private lemma first_identity (n : ℕ) (_hn : 0 < n) :
    T n 1 = T n 0 - 1 ∧
        T n 0 - 1 = ∑ k ∈ range n, T n k / ((k : ℚ) + 2) := by
  have h : T n 1 = T n 0 - 1 := by
    have h0 := t_step (Nat.zero_le n)
    push_cast at h0
    linarith
  refine ⟨h, ?_⟩
  rw [← h]
  calc
    T n 1 = ∑ k ∈ range n, (T n (k + 1) - T n (k + 2)) := by
      simpa [t_zero_of_lt (Nat.lt_succ_self n)] using
        (sum_range_sub' (fun k => T n (k + 1)) n).symm
    _ = ∑ k ∈ range n, T n k / ((k : ℚ) + 2) := by
      refine sum_congr rfl fun k hk => ?_
      have hkn := mem_range.mp hk
      have h0 := t_step (n := n) (k := k) (by omega)
      have h1 := t_step (n := n) (k := k + 1) (by omega)
      push_cast at h1
      rw [eq_div_iff (by positivity)]
      linear_combination h1 - h0

private lemma coeff_row (n k : ℕ) : (p n).coeff k = T n k := by
  by_cases h : k ≤ n
  · simp [p, coeff_C_mul, coeff_X_pow, Finset.sum_ite_eq, h]
  · simp [p, coeff_C_mul, coeff_X_pow, Finset.sum_ite_eq, h, t_zero_of_lt (by omega : n < k)]

private lemma row_sub_derivative_coeff (n k : ℕ) :
    (p n - derivative (p n)).coeff k = if k ≤ n then 1 else 0 := by
  rw [coeff_sub, coeff_derivative, coeff_row, coeff_row]
  by_cases h : k ≤ n
  · rw [if_pos h, t_step h]
    ring
  · rw [if_neg h, t_zero_of_lt (by omega : n < k),
      t_zero_of_lt (by omega : n < k + 1)]
    simp

private lemma row_sub_derivative_succ (n : ℕ) :
    p (n + 1) - derivative (p (n + 1)) =
      X * (p n - derivative (p n)) + 1 := by
  ext k
  rw [row_sub_derivative_coeff, coeff_add]
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, row_sub_derivative_coeff]
    simp [coeff_one]

private lemma sub_derivative_inj {u v : ℚ[X]}
    (h : u - derivative u = v - derivative v) : u = v := by
  have h' := congrArg sumIDeriv h
  simp only [map_sub, sumIDeriv_derivative] at h'
  linear_combination h' - sumIDeriv_eq_self_add u + sumIDeriv_eq_self_add v

private lemma recurrence_succ (n : ℕ) :
    p (n + 1) = (X + 1) * p n + 1 +
      ∑ i ∈ Icc 1 n, (derivative)^[i] (p n) := by
  have hd : (p n).natDegree ≤ n :=
    natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by rw [coeff_row, t_zero_of_lt hk]
  have hsplit : range (n + 1) = insert 0 (Icc 1 n) := by
    ext i
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have hs : (∑ i ∈ range (n + 1), (derivative)^[i] (p n)) =
      p n + ∑ i ∈ Icc 1 n, (derivative)^[i] (p n) := by
    rw [hsplit, sum_insert (by simp), Function.iterate_zero_apply]
  have hr : (X + 1) * p n + 1 + (∑ i ∈ Icc 1 n, (derivative)^[i] (p n)) =
      X * p n + 1 + ∑ i ∈ range (n + 1), (derivative)^[i] (p n) := by
    rw [hs, add_mul, one_mul]
    abel
  rw [hr]
  apply sub_derivative_inj
  rw [row_sub_derivative_succ, derivative_add, derivative_add, derivative_mul,
    derivative_X, derivative_one, one_mul, mul_sub]
  have ht := sumIDeriv_eq_self_add (p n)
  rw [sumIDeriv_apply_of_le hd] at ht
  linear_combination -ht

private lemma t_top_step {n k : ℕ} (hk : k ≤ n + 1) :
    T (n + 1) k = T n k + ((n + 1).factorial : ℚ) / (k.factorial : ℚ) := by
  unfold T
  rw [sum_Icc_succ_top hk, add_div]

private lemma eval_row (n : ℕ) :
    (p n).eval (-1) = ∑ k ∈ range (n + 1), T n k * (-1 : ℚ) ^ k := by
  simp [p, eval_finsetSum]

private lemma row_eval_step (n : ℕ) :
    (p (n + 1)).eval (-1) =
      (p n).eval (-1) + (numDerangements (n + 1) : ℚ) := by
  have hsum (m : ℕ) :
      (numDerangements m : ℚ) =
        ∑ k ∈ range (m + 1), ((m.factorial : ℚ) / (k.factorial : ℚ)) * (-1 : ℚ) ^ k := by
    rw [← Int.cast_natCast, numDerangements_sum]
    push_cast
    refine sum_congr rfl fun k hk => ?_
    have hle : k ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [Nat.ascFactorial_eq_div, add_tsub_cancel_of_le hle]
    rw [Nat.cast_div_charZero (Nat.factorial_dvd_factorial hle)]
    ring
  rw [eval_row, eval_row, hsum]
  calc
    (∑ k ∈ range (n + 1 + 1), T (n + 1) k * (-1 : ℚ) ^ k) =
        ∑ k ∈ range (n + 1 + 1),
          (T n k + ((n + 1).factorial : ℚ) / (k.factorial : ℚ)) * (-1 : ℚ) ^ k := by
      refine sum_congr rfl fun k hk => ?_
      rw [t_top_step (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    _ = _ := by
      simp only [add_mul, sum_add_distrib]
      congr 1
      rw [sum_range_succ, t_zero_of_lt (Nat.lt_succ_self n), zero_mul, add_zero]

private lemma eval_alternating (n : ℕ) :
    (p n).eval (-1) = (A173184 n : ℚ) := by
  induction n with
  | zero => norm_num [eval_row, T, A173184]
  | succ n ih =>
    rw [row_eval_step, ih]
    simp only [A173184, sum_range_succ _ (n + 1), Nat.cast_add]

end OMA.A348482

open OMA.A348482 in
theorem OMA.solution : type_of% @OMA.S_oeis_a348482.main := by
  refine ⟨first_identity, ?_, eval_alternating⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using recurrence_succ m
