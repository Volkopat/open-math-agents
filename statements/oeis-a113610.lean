import Mathlib

/-!
# A113610: Sum of digits of all composite numbers between prime(n) and prime(n+1).

Source: https://oeis.org/A113610
Credit: @divmxnd0x

Conjecture (stated in A113610): for `n > 9`, if `a(n) > a(n+1) < a(n+2)` then `prime(n)` and
`prime(n+1)` form a twin prime pair.

Formalization notes:
* `prime n` is the `n`-th prime (`prime 1 = 2`); all integers strictly between two consecutive
  primes are composite, so `a n` is the sum of the decimal digit sums of the integers `m` with
  `prime n < m < prime (n+1)` (data `0, 4, 6, 18, 3, 18, 9, 9, 40, 3, 35, 27, 6, ...`).
* "`prime(n)` and `prime(n+1)` form a twin prime pair" means `prime (n+1) = prime n + 2`.
* The statement is formalized literally as written in the entry.
-/

namespace OMA.S_oeis_a113610

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A113610(n): the sum of the digits of all numbers strictly between `prime n` and
`prime (n+1)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Ioo (prime n) (prime (n + 1)), (Nat.digits 10 m).sum

/-- For `n > 9`, a strict local minimum at `a (n+1)` forces `prime n`, `prime (n+1)` to be twin
primes. -/
theorem main : ∀ n : ℕ, 9 < n → a (n + 1) < a n → a (n + 1) < a (n + 2) →
    prime (n + 1) = prime n + 2 := by
  sorry

end OMA.S_oeis_a113610
