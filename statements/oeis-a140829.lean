import Mathlib

/-!
# A140829: a(0) = 1, a(n) = ceiling(Fibonacci(n)/a(n-1))

Source: https://oeis.org/A140829
Credit: @jagong-cmu

Formalizes Colin Barker's OEIS A140829 conjecture (Mar 08 2019), offset 0:
`a(n) = -a(n-1) + a(n-2) + a(n-3) + a(n-4) + a(n-5) for n>12.`

Barker also gives the g.f. `(1 + x + x^3)*(1 + x - x^9) / ((1 + x)*(1 - x^2 - x^4))`.
That g.f. is the same claim as the recurrence for `n > 12`, together with the terms
a(0), ..., a(12), so only the recurrence is stated.

Conventions:
* The sequence follows the OEIS definition `a(0) = 1` and
  `a(n) = ceiling(Fibonacci(n)/a(n-1))` for `n >= 1`. The quotient is taken in `ℚ`,
  and the ceiling is `Nat.ceil` (all terms are positive). `Nat.fib` is Fibonacci,
  with `Nat.fib 0 = 0` and `Nat.fib 1 = 1`.
* The recurrence is stated in `ℤ` (to avoid ℕ subtraction) for every `n >= 13`.
-/

namespace OMA.S_oeis_a140829

/-- `a(0) = 1`, `a(n) = ceiling(Fibonacci(n)/a(n-1))` for `n >= 1`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ⌈(Nat.fib (n + 1) : ℚ) / (a n : ℚ)⌉₊

/-- For all `n > 12`: `a(n) = -a(n-1) + a(n-2) + a(n-3) + a(n-4) + a(n-5)`. -/
theorem main : ∀ n : ℕ, 13 ≤ n →
    (a n : ℤ) = -a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a140829
