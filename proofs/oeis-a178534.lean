import OMAStatements.S_oeis_a178534
import Mathlib

open Finset PowerSeries OMA.S_oeis_a178534

/- The first column is Fibonacci, truncated at row one. -/
private lemma oma_fib_column_base :
    column 1 * ((1-X-X^2) * (1-X^1)) = X^1 * (1-X^2) := by
  have numerator : column 1 * (1-X-X^2) = X+X^2 := by
    have c₀ : coeff 0 (column 1) = 0 := by simp [column]
    have cs (n : ℕ) : coeff (n+1) (column 1) = (Nat.fib (n+2) : ℤ) := by
      simp [column, T]
    rw [mul_sub, mul_sub, mul_one, show column 1 * X^2 = (column 1 * X) * X by ring]
    ext n
    rcases n with _ | _ | _ | n
    · simpa using c₀
    · norm_num [coeff_succ_mul_X, coeff_X, coeff_X_pow, c₀, cs, Nat.fib]
    · norm_num [coeff_succ_mul_X, coeff_X, coeff_X_pow, c₀, cs, Nat.fib]
    · simp only [map_sub, map_add, coeff_succ_mul_X, cs, coeff_X, coeff_X_pow]
      simp only [if_neg (show n+1+1+1 ≠ 1 by omega), if_neg (show n+1+1+1 ≠ 2 by omega), add_zero]
      rw [Nat.fib_add_two (n := n+2), Nat.cast_add]
      ring
  rw [pow_one, ← mul_assoc, numerator]
  ring

/- Interpret each term of the finite recurrence as a shifted power series. -/
private lemma oma_column_coeff_pos {m k : ℕ} (hm : 0 < m) : coeff m (column k) = T m k := by
  simp only [column, coeff_mk]
  split_ifs with h
  · rfl
  · rw [T]
    simp [show k ≠ 1 by omega, show m < k by omega]

/-- Summing the triangle recurrence over rows gives one shift for each earlier row. -/
private theorem oma_column_step {k : ℕ} (hk : 2 ≤ k) :
    column k = (∑ i : Fin (k - 1), X ^ (i.val + 1)) * (column (k - 1) - column k) := by
  ext n
  rw [Finset.sum_mul, map_sum]
  simp_rw [coeff_X_pow_mul']
  by_cases hkn : k ≤ n
  · rw [oma_column_coeff_pos (by omega), T]
    simp only [if_neg (by omega : k ≠ 1), dif_neg (by omega : ¬ (k = 0 ∨ n < k))]
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    rw [if_pos (by omega : i.val + 1 ≤ n), map_sub,
      oma_column_coeff_pos (by omega), oma_column_coeff_pos (by omega)]
  · rw [show coeff n (column k) = 0 by simp [column, hkn]]
    symm
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · have hlt : n - (i.val + 1) < k - 1 := by omega
      simp only [map_sub, column, coeff_mk, if_neg hlt.not_ge,
        if_neg (show ¬ k ≤ n - (i.val + 1) by omega), sub_self]
    · rfl

/- A finite geometric sum telescopes when multiplied by 1-X, leaving an induction on columns. -/
private lemma column_induction
    (base : column 1 * ((1-X-X^2)*(1-X^1)) = X^1 * (1-X^2))
    (step : ∀ k, 2 ≤ k → column k = (∑ i : Fin (k-1), X^(i.val+1)) * (column (k-1)-column k)) :
    ∀ k, 1 ≤ k → column k * ((1-X-X^2)*(1-X^k)) = X^k*(1-X^2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    let s : PowerSeries ℤ := ∑ i : Fin n, X^(i.val+1)
    have hstep : column (n+1) = s * (column n-column (n+1)) := by
      simpa [s] using step (n+1) (by omega)
    have geom : s * (1-X) = X * (1-X^n) := by
      dsimp [s]
      simp only [pow_succ, ← Finset.sum_mul, Fin.sum_univ_eq_sum_range]
      linear_combination X * geom_sum_mul_neg (X : PowerSeries ℤ) n
    have tel : column (n+1) * (1-X^(n+1)) = X * (1-X^n) * column n := by
      rw [pow_succ]
      linear_combination (1-X)*hstep + (column n-column (n+1))*geom
    rw [pow_succ]
    linear_combination (1-X-X^2)*tel + X*ih

theorem OMA.solution : type_of% @OMA.S_oeis_a178534.main := by
  exact column_induction oma_fib_column_base (fun _ hk => oma_column_step hk)
