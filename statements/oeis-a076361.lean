import Mathlib

/-!
# OEIS A076361: Numbers k such that d(sigma(k)) = sigma(d(k)).

Source: https://oeis.org/A076361
Credit: @unserus

OEIS: "Assuming Schinzel's hypothesis is true, the sequence is infinite."
The open statement is that the sequence is infinite. `d` is the number of divisors and
`sigma` the sum of divisors; the terms are positive integers (first terms `1, 3, 44, 49`).
-/

namespace OMA.S_oeis_a076361

/-- The number of divisors `d(n)`. -/
abbrev d (n : ℕ) : ℕ := ArithmeticFunction.sigma 0 n

/-- The sum of divisors `σ(n)`. -/
abbrev sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- The terms of A076361: positive `k` with `d(σ(k)) = σ(d(k))`. -/
def a076361Set : Set ℕ := {k : ℕ | 0 < k ∧ d (sigma k) = sigma (d k)}

/-- A076361 is infinite. -/
theorem main : a076361Set.Infinite := by
  sorry

end OMA.S_oeis_a076361
