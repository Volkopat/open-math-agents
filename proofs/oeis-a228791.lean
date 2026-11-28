import OMAStatements.S_oeis_a228791
import Mathlib

namespace A228791Aux
open OMA.S_oeis_a228791

lemma total_ext3 (v : Rows) :
    (extend (extend (extend v))).total =
      5 * (extend (extend v)).total - 3 * (extend v).total := by
  simp only [extend, Rows.total]; ring

lemma a_rec (n : ℕ) : a (n + 4) = 5 * a (n + 3) - 3 * a (n + 2) := by
  show (state (n + 3)).total = 5 * (state (n + 2)).total - 3 * (state (n + 1)).total
  exact total_ext3 (state n)

lemma part1 : ∀ n : ℕ, productCoeff n = numeratorCoeff n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | (m + 4) => by
    have h := a_rec m
    have e : productCoeff (m + 4) = a (m + 4) - 5 * a (m + 3) + 3 * a (m + 2) := rfl
    have e' : numeratorCoeff (m + 4) = 0 := rfl
    rw [e, e', h]; ring

lemma cf_rec (n : ℕ) :
    closedForm (n + 2) = 5 * closedForm (n + 1) - 3 * closedForm n := by
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  unfold closedForm
  linear_combination
    (-2 / (9 * Real.sqrt 13 * 2 ^ n) / 4 *
      ((-11 + Real.sqrt 13) * (5 + Real.sqrt 13) ^ n +
        (11 + Real.sqrt 13) * (5 - Real.sqrt 13) ^ n)) * h13

lemma part2 : ∀ n : ℕ, (a (n + 2) : ℝ) = closedForm (n + 2) ∧
    (a (n + 3) : ℝ) = closedForm (n + 3) := by
  intro n
  induction n with
  | zero =>
    have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
    have hpos : (0 : ℝ) < 9 * Real.sqrt 13 := by positivity
    have e2 : a 2 = 8 := by decide
    have e3 : a 3 = 36 := by decide
    refine ⟨?_, ?_⟩
    · show (a 2 : ℝ) = closedForm 2
      rw [e2]; unfold closedForm; push_cast
      rw [eq_div_iff hpos.ne']
      linear_combination Real.sqrt 13 * h13
    · show (a 3 : ℝ) = closedForm 3
      rw [e3]; unfold closedForm; push_cast
      rw [eq_div_iff hpos.ne']
      linear_combination 2 * Real.sqrt 13 * h13
  | succ k ih =>
    obtain ⟨h2, h3⟩ := ih
    refine ⟨h3, ?_⟩
    have hr := a_rec k
    have hc := cf_rec (k + 2)
    have e : (a (k + 4) : ℝ) = 5 * a (k + 3) - 3 * a (k + 2) := by
      rw [hr]; push_cast; ring
    show (a (k + 4) : ℝ) = closedForm (k + 2 + 2)
    rw [e, h2, h3, hc]
end A228791Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a228791.main := by
  refine ⟨A228791Aux.part1, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact (A228791Aux.part2 m).1
