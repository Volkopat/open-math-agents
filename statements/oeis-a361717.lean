import Mathlib

/-!
# A361717: a(n) = Sum_{k = 0..n-1} binomial(n-1,k)^2*binomial(n+k,k)

Source: https://oeis.org/A361717

`a(n) = Sum_{k = 0..n-1} binomial(n-1,k)^2 * binomial(n+k,k)`, offset 0:
`0, 1, 4, 27, 216, 1875, 17088, 160867, ...` (the sum is empty for `n = 0`).

The entry (Peter Bala, Mar 26 2023) makes two conjectures, stated together here in the order of the
entry:

1. Conjecture 1: the supercongruence `a(p) == 0 (mod p^4)` holds for all primes `p >= 5`
   (checked up to `p = 199`);
2. Conjecture 2: the supercongruence `a(p-1) == 1 - 2*p - p^2 (mod p^3)` holds for all primes
   except `p = 3` (checked up to `p = 199`).

The entry does not say that either conjecture has been proved.

Formalized: `a(n)` is an integer, the sum runs over `Finset.range n` (that is `k = 0..n-1`) and the
binomial coefficients are `Nat.choose`; the truncated subtraction `n - 1` only occurs for `n >= 1`
(for `n = 0` the range is empty). A congruence `x == y (mod N)` between integers is written as
`N ∣ x - y`, and `a(p) == 0 (mod p^4)` as `p^4 ∣ a p`. In Conjecture 2 the prime `p = 2` is
included, as in the entry (`a(1) = 1` and `1 - 4 - 4 = -7`), and only `p = 3` is excluded; `p - 1`
is a natural number subtraction with `p >= 2`.
-/

namespace OMA.S_oeis_a361717

/-- A361717: `a(n) = Sum_{k = 0..n-1} binomial(n-1,k)^2 * binomial(n+k,k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, ((n - 1).choose k : ℤ) ^ 2 * ((n + k).choose k : ℤ)

/-- Bala's two conjectured supercongruences: `a(p) == 0 (mod p^4)` for all primes `p >= 5`, and
`a(p-1) == 1 - 2*p - p^2 (mod p^3)` for all primes `p` other than `3`. -/
theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 4) ∣ a p) ∧
    (∀ p : ℕ, p.Prime → p ≠ 3 →
      ((p : ℤ) ^ 3) ∣ (a (p - 1) - (1 - 2 * (p : ℤ) - (p : ℤ) ^ 2))) := by
  sorry

end OMA.S_oeis_a361717
