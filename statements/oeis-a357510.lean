import Mathlib

/-!
# A357510: a(n) = Sum_{k = 0..n} k * binomial(n,k)^2 * binomial(n+k,k)^2

Source: https://oeis.org/A357510

`a(n) = Sum_{k = 0..n} k * binomial(n,k)^2 * binomial(n+k,k)^2`, offset 0; the first terms are
`0, 4, 108, 3144, 95000, 2935020, ...`.

The entry (Peter Bala, Oct 01 2022) makes one conjectural statement, stated here:

  Conjecture: `a(p-1) == 0 (mod p^4)` for all primes `p >= 5` (checked up to `p = 499`).

The other formula lines are not part of the target: the supercongruence `A(p-1) == 1 (mod p^3)` for
the Apery numbers A005259 is quoted as a known fact (Straub), and the recurrence and the asymptotic
formula are given without the word conjecture.

Formalized: `a n` is an integer, defined by the sum exactly as in the name line, with `k` running over
`Finset.range (n + 1)`, that is `0 <= k <= n`, and with `Nat.choose` for the binomial coefficients.
The index `p - 1` is a natural-number subtraction, harmless because a prime is at least 2. The
congruence `a(p-1) == 0 (mod p^4)` is written as divisibility of `a (p - 1)` by `p ^ 4` in the
integers. The range is every prime `p` with `5 <= p`; the claim is false for `p = 2` and `p = 3`
(`a(1) = 4`, `a(2) = 108 = 2^2 * 3^3`), which is why the entry starts at 5.
-/

namespace OMA.S_oeis_a357510

/-- A357510: `a(n) = Sum_{k=0..n} k * C(n,k)^2 * C(n+k,k)^2`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (k : ℤ) * (n.choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ) ^ 2

/-- Bala's conjecture: `a(p-1) == 0 (mod p^4)` for every prime `p >= 5`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 4) ∣ a (p - 1) := by
  sorry

end OMA.S_oeis_a357510
