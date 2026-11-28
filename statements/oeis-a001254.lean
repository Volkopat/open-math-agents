import Mathlib

/-!
# A001254: Squares of Lucas numbers

Source: https://oeis.org/A001254
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Peter Bala, Nov 13 2019):
Let `L(n)` be the Lucas numbers (`L(0) = 2`, `L(1) = 1`, `L(n+2) = L(n+1) + L(n)`),
`a(n) = L(n)^2`, and `F(n)` the Fibonacci numbers. Then for every `k : ℕ`:
`∑_{n ≥ 1} 1 / (a(n) - 5 * (-1)^n * F(2*k + 1)^2) = 1 / (2 * a(2*k + 1))`.
-/

namespace OMA.S_oeis_a001254

/-- Lucas numbers: `L(0) = 2`, `L(1) = 1`, `L(n+2) = L(n+1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- A001254: squares of Lucas numbers `a(n) = L(n)^2`. -/
def a (n : ℕ) : ℕ :=
  lucas n ^ 2

/-- For every `k : ℕ`, the series `∑_{n ≥ 1} 1 / (a(n) - 5 * (-1)^n * F(2k+1)^2)`
converges to `1 / (2 * a(2k+1))`. -/
theorem main :
    ∀ k : ℕ,
      HasSum
        (fun n : ℕ =>
          (1 : ℝ) / ((a (n + 1) : ℝ) - 5 * (-1 : ℝ) ^ (n + 1) * (Nat.fib (2 * k + 1) : ℝ) ^ 2))
        (1 / (2 * (a (2 * k + 1) : ℝ))) := by
  sorry

end OMA.S_oeis_a001254
