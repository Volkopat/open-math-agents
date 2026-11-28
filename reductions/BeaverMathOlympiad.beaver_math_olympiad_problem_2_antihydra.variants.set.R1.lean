import FormalConjectures.Other.BeaverMathOlympiad

-- Reduction BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.variants.set.R1 of the Antihydra problem, counting form
-- Credit: @marcusbuffett

/-!
# Antihydra, counting form: a kernel-checked initial range, and the open rest

With `a 0 = 8` and `a (n + 1) = ⌊3 a n / 2⌋`, the problem asks whether among `a 0, ..., a (n - 1)`
the odd terms are never more than twice as many as the even terms.

* `H1`: this holds for every `n ≤ 100000`. Checked inside the Lean kernel by running the
  recurrence.
* `H2`: it holds for every larger `n`. This is the open problem.
-/

namespace OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ (a : ℕ → ℕ), a 0 = 8 → (∀ n, a (n + 1) = (3 * a n) / 2) → ∀ n : ℕ, n ≤ 100000 →
    ((Finset.Ico 0 n).filter fun x ↦ Odd (a x)).card ≤
      2 * ((Finset.Ico 0 n).filter fun x ↦ Even (a x)).card

/-- The open part. -/
def H2 : Prop :=
  ∀ (a : ℕ → ℕ), a 0 = 8 → (∀ n, a (n + 1) = (3 * a n) / 2) → ∀ n : ℕ, 100000 < n →
    ((Finset.Ico 0 n).filter fun x ↦ Odd (a x)).card ≤
      2 * ((Finset.Ico 0 n).filter fun x ↦ Even (a x)).card

theorem main : H1 → H2 → type_of% @BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.variants.set := by
  intro h1 h2 a a_ini a_rec n
  by_cases h : n ≤ 100000
  · exact h1 a a_ini a_rec n h
  · exact h2 a a_ini a_rec n (by omega)

end OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R1
