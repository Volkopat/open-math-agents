import FormalConjectures.Other.BeaverMathOlympiad

-- Reduction BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.R1 of the Antihydra problem
-- Credit: @marcusbuffett

/-!
# Antihydra: a kernel-checked initial range, and the open rest

Antihydra is a six-state Turing machine whose halting is equivalent to the following: with
`a 0 = 8`, `a (n + 1) = ⌊3 a n / 2⌋`, and a counter `b` that gains `2` when `a n` is even and
loses `1` when it is odd, the counter never becomes negative.

* `H1`: the counter is nonnegative for the first `100000` steps. Checked inside the Lean kernel
  by running the recurrence.
* `H2`: the counter is nonnegative at every later step. This is the open problem (the machine
  has been simulated much further; the range here is only what fits in a proof file).
-/

namespace OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ (a : ℕ → ℕ) (b : ℕ → ℤ), a 0 = 8 → (∀ n, a (n + 1) = (3 * a n) / 2) → b 0 = 0 →
    (∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) →
    ∀ n, n ≤ 100000 → b n ≥ 0

/-- The open part. -/
def H2 : Prop :=
  ∀ (a : ℕ → ℕ) (b : ℕ → ℤ), a 0 = 8 → (∀ n, a (n + 1) = (3 * a n) / 2) → b 0 = 0 →
    (∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) →
    ∀ n, 100000 < n → b n ≥ 0

theorem main : H1 → H2 → type_of% @BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra := by
  intro h1 h2 a b a_ini a_rec b_ini b_rec n
  by_cases h : n ≤ 100000
  · exact h1 a b a_ini a_rec b_ini b_rec n h
  · exact h2 a b a_ini a_rec b_ini b_rec n (by omega)

end OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1
