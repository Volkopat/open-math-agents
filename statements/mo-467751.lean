import Mathlib

/-!
# Do all nonnegative integers appear in A051521?

Source: https://mathoverflow.net/questions/467751 (2024).
Credit: @jagraj28

For a positive integer `c`, the `c`-th term of OEIS A051521 is the number of positive integers
`n` with `n = c · τ(n)`, where `τ(n)` is the number of divisors of `n` (this number is finite,
since `τ(n) ≤ √(3n)`). The post asks whether every nonnegative integer appears in A051521; the
values `0, 1, …, 6` are known to appear (`4`, `5`, `6` first at `c = 11264, 64000, 82944`), so
the question is whether every integer greater than `3` (in fact, greater than `6`) appears. The
post has no answer.

Formalization notes:
* `τ(n)` is `(Nat.divisors n).card`.
* `Set.ncard` counts the solutions `n`; the set is finite, so `ncard` is its size.
* `main` states the affirmative answer. A direct computation gives the first terms
  `2, 2, 3, 1, 2, 1, 2, 2, 1, 1, …`, the first `0` at `c = 18`, and the value `4` at `c = 11264`.
-/

namespace OMA.S_mo_467751

/-- The positive integers `n` with `n = c · τ(n)`. -/
def solutions (c : ℕ) : Set ℕ := {n | 0 < n ∧ n = c * (Nat.divisors n).card}

/-- Every nonnegative integer `k` is the number of solutions for some positive `c`. -/
theorem main : ∀ k : ℕ, ∃ c : ℕ, 0 < c ∧ (solutions c).ncard = k := by
  sorry

end OMA.S_mo_467751
