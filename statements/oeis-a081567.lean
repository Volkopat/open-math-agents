import Mathlib

/-!
# A081567: second binomial transform of the Fibonacci numbers and A039717

Source: https://oeis.org/A081567
Credit: @sntntHb

`a(n)` (offset 0) is the second binomial transform of `F(n+1)`:
  `a(n) = Sum_{k=0..n} binomial(n,k) * 2^(n-k) * F(k+1)`,
with `F` the Fibonacci numbers (A000045); the first terms are `1, 3, 10, 35, 125, 450, ...`.
The entry records the conjecture
  `a(n) = 2*a(n-1) + A039717(n)`.

A039717 (offset 1, terms `1, 4, 15, 55, 200, ...`) is the binomial transform of `F(2n+2)`
(Paul Barry, in A039717), i.e.
  `A039717(n) = Sum_{k=0..n-1} binomial(n-1,k) * F(2k+2)`.
The conjecture is stated for `n ≥ 1`, where `A039717(n)` is defined.
-/

namespace OMA.S_oeis_a081567

/-- `a n = Sum_{k=0..n} C(n,k) 2^(n-k) F(k+1)` (OEIS A081567). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ (n - k) * Nat.fib (k + 1)

/-- `b n = Sum_{k=0..n-1} C(n-1,k) F(2k+2)`, OEIS A039717 (for `n ≥ 1`). -/
def b (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k * Nat.fib (2 * k + 2)

/-- The conjecture in OEIS A081567: `a(n) = 2 a(n-1) + A039717(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * a (n - 1) + b n := by
  sorry

end OMA.S_oeis_a081567
