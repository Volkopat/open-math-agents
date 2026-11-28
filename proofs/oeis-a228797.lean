import OMAStatements.S_oeis_a228797
import Mathlib

namespace A228797Aux
open OMA.S_oeis_a228797

lemma total_ext3 (v : Columns) :
    (extend (extend (extend v))).total =
      (extend (extend v)).total + 3 * (extend v).total + v.total := by
  simp only [extend, Columns.total]; ring

lemma a_rec (n : ℕ) : a (n + 4) = a (n + 3) + 3 * a (n + 2) + a (n + 1) := by
  show (state (n + 3)).total = (state (n + 2)).total + 3 * (state (n + 1)).total + (state n).total
  exact total_ext3 (state n)

lemma part1 : ∀ n : ℕ, productCoeff n = (if n = 1 then 2 else 0)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | (m + 4) => by
    have h := a_rec m
    have e : productCoeff (m + 4) = a (m + 4) - a (m + 3) - 3 * a (m + 2) - a (m + 1) := rfl
    have hne : ¬ (m + 4 = 1) := by omega
    rw [e, h, if_neg hne]; ring

lemma cf_rec (n : ℕ) :
    closedForm (n + 4) = closedForm (n + 3) + 3 * closedForm (n + 2) + closedForm (n + 1) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold closedForm
  linear_combination
    ((1 - Real.sqrt 2) ^ (n + 1) * (2 - Real.sqrt 2) +
      (1 + Real.sqrt 2) ^ (n + 1) * (2 + Real.sqrt 2)) / 2 * h2

lemma part2 : ∀ n : ℕ, (a (n + 1) : ℝ) = closedForm (n + 1) ∧
    (a (n + 2) : ℝ) = closedForm (n + 2) ∧ (a (n + 3) : ℝ) = closedForm (n + 3) := by
  intro n
  induction n with
  | zero =>
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have e1 : a 1 = 2 := by decide
    have e2 : a 2 = 2 := by decide
    have e3 : a 3 = 8 := by decide
    refine ⟨?_, ?_, ?_⟩
    · show (a 1 : ℝ) = closedForm 1
      rw [e1]; unfold closedForm; push_cast; ring
    · show (a 2 : ℝ) = closedForm 2
      rw [e2]; unfold closedForm; push_cast; linear_combination (-1 : ℝ) * h2
    · show (a 3 : ℝ) = closedForm 3
      rw [e3]; unfold closedForm; push_cast; linear_combination (-3 : ℝ) * h2
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr := a_rec k
    have hc := cf_rec k
    have e : (a (k + 4) : ℝ) = a (k + 3) + 3 * a (k + 2) + a (k + 1) := by
      rw [hr]; push_cast; ring
    show (a (k + 4) : ℝ) = closedForm (k + 4)
    rw [e, h1, h2, h3, hc]
end A228797Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a228797.main := by
  refine ⟨A228797Aux.part1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (A228797Aux.part2 m).1
