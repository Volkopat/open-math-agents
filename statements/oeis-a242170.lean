import Mathlib

/-!
# A242170: primitive prime divisors of central trinomial coefficients

Source: https://oeis.org/A242170
Credit: @coleman415

The sequence (Zhi-Wei Sun) is: `a(n)` = least prime divisor of `T(n)` which does not divide any
`T(k)` with `k < n`, or `1` if such a primitive prime divisor of `T(n)` does not exist, where
`T(n)` is the `n`-th central trinomial coefficient (OEIS A002426). The sequence has offset 1.
The entry records: *Conjecture: (i) a(n) > 1 for all n > 1.*

`main` is part (i), the statement listed for this problem: for every `n > 1`, `T(n)` has a prime
divisor that divides no `T(k)` with `0 < k < n`. Part (ii) of the entry (Motzkin numbers) is a
different claim and is not stated here.

Conventions:
- `T(n)` is the coefficient of `x^n` in `(1 + x + x^2)^n`, that is
  `T(n) = sum_{k=0..floor(n/2)} binomial(n,2k) * binomial(2k,k)`: 1, 1, 3, 7, 19, 51, ...
  (the entry's example: `T(2) = 3`, `T(5) = 51`, `T(11) = 3*17*503`).
- `k` ranges over `0 < k < n`, the indices of the sequence. (`T(0) = 1` has no prime divisor,
  so allowing `k = 0` changes nothing.)
-/

namespace OMA.S_oeis_a242170

/-- The `n`-th central trinomial coefficient (OEIS A002426). -/
def centralTrinomial (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * (2 * k).choose k

/-- Part (i) of the conjecture of OEIS A242170. -/
theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ p : ℕ, p.Prime ∧ p ∣ centralTrinomial n ∧
        ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ centralTrinomial k := by
  sorry

end OMA.S_oeis_a242170
