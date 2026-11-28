import Mathlib

/-!
# Is $\sum_{n=1}^\infty \frac{n!}{n^n}$ rational?

Source: MathOverflow question 277969, https://mathoverflow.net/questions/277969
Credit: @aroth01

The question asks whether $\sum_{n=1}^\infty \frac{n!}{n^n}$ is rational. It notes that
OEIS A094082 (the decimal expansion of this sum) suggests that it is not. The question has no
answer, so the problem is open.

The statement below asserts the expected answer: the series converges and its sum is irrational.
The sum runs over $n \geq 1$, written as $n + 1$ for $n : ℕ$, so that $n = 0$ (where Lean's
$0^0 = 1$ would add a spurious term $0!/0^0 = 1$) is excluded. Summability is stated explicitly
because `tsum` of a non-summable series is $0$, which is rational.
-/

namespace OMA.S_mo_277969

/-- The $n$-th term $n!/n^n$ of the series, indexed from $n = 1$. -/
noncomputable def term (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) / ((n + 1 : ℝ) ^ (n + 1))

/-- The series $\sum_{n \geq 1} n!/n^n$ converges and its sum is irrational. -/
theorem main : Summable term ∧ Irrational (∑' n : ℕ, term n) := by
  sorry

end OMA.S_mo_277969
