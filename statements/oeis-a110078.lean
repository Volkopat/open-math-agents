import Mathlib

/-!
# A110078: Number of solutions of the equation sigma(x) = 10^n

Source: https://oeis.org/A110078

Conjecture (OEIS A110078):
For every `n > 2` (i.e., `n ≥ 3`), `a(n + 1) > a(n)`, where `a(n)` is the number of
positive integers `x` whose sum of divisors `σ(x)` equals `10^n`.

Conventions:
- Offset: `0`; first terms: `a(0) = 1` (`x = 1`), `a(1) = 0`, `a(2) = 0`, `a(3) = 0`,
  `a(4) = 2` (`x ∈ {8743, 9481}`), ...
- Since `σ(x) ≥ x` for all `x ≥ 1`, the solution set `{x : ℕ | 1 ≤ x ∧ sigma x = 10 ^ n}`
  is finite, so `Set.ncard` gives the exact number of solutions.
-/

namespace OMA.S_oeis_a110078

/-- Sum of positive divisors `σ(x)` of `x : ℕ`. -/
def sigma (x : ℕ) : ℕ :=
  ∑ d ∈ x.divisors, d

/-- Number of positive integers `x` such that `σ(x) = 10^n` (OEIS A110078). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ | 1 ≤ x ∧ sigma x = 10 ^ n}

/-- Conjecture: `a(n + 1) > a(n)` for all `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n → a n < a (n + 1) := by
  sorry

end OMA.S_oeis_a110078
