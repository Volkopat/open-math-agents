import Mathlib

/-!
# A237712: k*n + pi(k*n) is prime for some 0 < k < n

Source: https://oeis.org/A237712
Credit: @coleman415

The sequence (Zhi-Wei Sun) is `a(n) = |{0 < k < n: k*n + pi(k*n) is prime}|`, where `pi(x)` is
the number of primes not exceeding `x` (OEIS A000720).
The entry records: *Conjecture: a(n) > 0 for all n > 5.*

So the conjecture says: for every `n > 5` there is `0 < k < n` with `k*n + pi(k*n)` prime.

Conventions:
- `Nat.primeCounting x` is Mathlib's `pi(x)`, the number of primes `≤ x`. Example from the
  entry: `2*6 + pi(2*6) = 12 + 5 = 17`.
-/

namespace OMA.S_oeis_a237712

/-- The conjecture of OEIS A237712. -/
theorem main :
    ∀ n : ℕ, 5 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (k * n + Nat.primeCounting (k * n)).Prime := by
  sorry

end OMA.S_oeis_a237712
