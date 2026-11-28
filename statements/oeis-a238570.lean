import Mathlib

/-!
# A238570: pi((k+1)^2) - pi(k^2) and pi(n^2) - pi(k^2) both prime

Source: https://oeis.org/A238570
Credit: @coleman415

The sequence (Zhi-Wei Sun) is
`a(n) = |{0 < k < n: pi((k+1)^2) - pi(k^2) and pi(n^2) - pi(k^2) are both prime}|`,
where `pi(x)` denotes the number of primes not exceeding `x`.
The entry records: *Conjecture: (i) a(n) > 0 for all n > 1.*

`main` is part (i), the statement listed for this problem: for every `n > 1` there is
`0 < k < n` such that `pi((k+1)^2) - pi(k^2)` and `pi(n^2) - pi(k^2)` are both prime.
Parts (ii) and (iii) of the entry are different claims and are not stated here.

Conventions:
- `Nat.primeCounting x` is Mathlib's `pi(x)`, the number of primes `≤ x`. Since `pi` is
  monotone and `k < n`, the natural-number subtractions are the integer differences.
  Example from the entry: `pi(8^2) - pi(7^2) = 18 - 15 = 3`.
-/

namespace OMA.S_oeis_a238570

/-- Part (i) of the conjecture of OEIS A238570. -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
      (Nat.primeCounting ((k + 1) ^ 2) - Nat.primeCounting (k ^ 2)).Prime ∧
      (Nat.primeCounting (n ^ 2) - Nat.primeCounting (k ^ 2)).Prime := by
  sorry

end OMA.S_oeis_a238570
