import OMAStatements.S_oeis_a203470
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The two divisibility conjectures of OEIS A203470, `a(n) = ∏_{2 ≤ i < j ≤ n + 1} (i + j)`.

Passing from `n` to `n + 1` multiplies `a` by the inner product for `j = n + 2`, which is the
product `(n + 4) (n + 5) ⋯ (2n + 3)` of `n` consecutive integers, hence a multiple of `n!`. This
gives `a(n) ∣ a(n + 1)` and, by induction, `∏_{k=1}^{n-1} k! ∣ a(n)`. -/

namespace OpenMath.A203470

open Finset OMA.S_oeis_a203470

/-- Passing from `a n` to `a (n + 1)` adds the inner product for `j = n + 2`. -/
private theorem a_succ (n : ℕ) :
    a203470 (n + 1) = a203470 n * ∏ i ∈ Ico 2 (n + 2), (i + (n + 2)) := by
  show (∏ j ∈ Icc 2 (n + 1 + 1), ∏ i ∈ Ico 2 j, (i + j)) =
    (∏ j ∈ Icc 2 (n + 1), ∏ i ∈ Ico 2 j, (i + j)) * ∏ i ∈ Ico 2 (n + 1 + 1), (i + (n + 1 + 1))
  exact Finset.prod_Icc_succ_top (by omega) _

/-- The added factor is the product of the `n` consecutive integers `n + 4, …, 2n + 3`. -/
private theorem factorial_dvd_step (n : ℕ) :
    n.factorial ∣ ∏ i ∈ Ico 2 (n + 2), (i + (n + 2)) := by
  have h : ∏ i ∈ Ico 2 (n + 2), (i + (n + 2)) = (n + 4).ascFactorial n := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.ascFactorial_eq_prod_range, Nat.add_sub_cancel]
    exact Finset.prod_congr rfl fun i _ => by omega
  rw [h]
  exact Nat.factorial_dvd_ascFactorial _ _

theorem main :
    (∀ n : ℕ, 1 ≤ n → a203470 n ∣ a203470 (n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n → superfactorial (n - 1) ∣ a203470 n) := by
  refine ⟨fun n _ => ?_, fun n hn => ?_⟩
  · rw [a_succ]
    exact dvd_mul_right _ _
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    clear hn
    induction m with
    | zero => simp [superfactorial]
    | succ m ih =>
      have hs : superfactorial (m + 1) = superfactorial m * (m + 1).factorial := by
        unfold superfactorial
        exact Finset.prod_Icc_succ_top (by omega) _
      rw [hs, a_succ]
      exact mul_dvd_mul ih (factorial_dvd_step (m + 1))

end OpenMath.A203470

theorem OMA.solution : type_of% @OMA.S_oeis_a203470.main := OpenMath.A203470.main
