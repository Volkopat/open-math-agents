import Mathlib

/-!
# A262965: Least number k such that k mod s = prime(n) where s is the sum of the distinct primes dividing k

Source: https://oeis.org/A262965
Credit: @xor2k

Formalizes the OEIS A262965 conjecture: a(n) exists for all n > 0.
That is, for every `n > 0` there is a positive integer `k` with `k mod s = prime(n)`, where `s` is the
sum of the distinct primes dividing `k` (then the least such `k` exists automatically).

Conventions:
* Offset 1: `prime(n)` is the `n`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`
  (`Nat.nth` is 0-indexed).
* `sopf k` is the sum over `Nat.primeFactors k` (the distinct primes dividing `k`).
* `%` is `Nat` remainder. The degenerate values `k = 0, 1` have `sopf k = 0` and `k % 0 = k`,
  which is never a prime, so they cannot serve as witnesses anyway; `k` is required to be positive.
-/

namespace OMA.S_oeis_a262965

/-- Sum of the distinct primes dividing `k` (A008472). -/
def sopf (k : ℕ) : ℕ :=
  ∑ q ∈ k.primeFactors, q

/-- For every `n > 0` there is a positive `k` with `k mod sopf(k) = prime(n)`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k % sopf k = Nat.nth Nat.Prime (n - 1) := by
  sorry

end OMA.S_oeis_a262965
