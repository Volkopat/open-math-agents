import Mathlib

/-!
# OEIS A022831: a signed sum of primes

Source: https://oeis.org/A022831
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = c(1) p(1) + ⋯ + c(n) p(n)`, where `p(i)` is the `i`-th prime, `c(i) = 1` if
`a(i-1) ≤ p(i)` and `c(i) = -1` if `a(i-1) > p(i)` (`a(0) = 0`). Conjecture (OEIS entry): every
number occurs in the sequence at most finitely many times.

Conventions:
* `p(i) = Nat.nth Nat.Prime (i - 1)` for `i ≥ 1`; values are integers.
-/

namespace OMA.S_oeis_a022831

/-- The sequence, with `a(0) = 0`. -/
noncomputable def a : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
    let p : ℤ := Nat.nth Nat.Prime n
    if a n ≤ p then a n + p else a n - p

/-- Every integer occurs only finitely often. -/
theorem main : ∀ m : ℤ, {n : ℕ | a n = m}.Finite := by
  sorry

end OMA.S_oeis_a022831
