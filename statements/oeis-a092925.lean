import Mathlib

/-!
# A092925: a prime one less than a falling product

Source: https://oeis.org/A092925
Credit: @R-Dson

`a(n)` is the smallest prime of the form `n * (n - 1) * ... * (n - k) - 1`, or `0` if no such
prime exists. Conjecture: no term is zero.

Conventions.
- The products are those with `0 ≤ k ≤ n - 2`, so they end with the factor `2`. The data of the
  entry start with `a(3) = 2 = 3 - 1`, `a(4) = 3 = 4 - 1` and `a(5) = 19 = 5 * 4 - 1`, so `k = 0`
  (the product is `n` alone) is included; its example is `a(13) = 13 * 12 * 11 * 10 - 1`.
- `a(n)` is the smallest of those numbers that is prime (not the one with the smallest `k`), and
  it is the infimum in `ℕ` of the set of such primes, so it is `0` exactly when the set is empty.
- The offset of the entry is `3`.
-/

namespace OMA.S_oeis_a092925

/-- `p + 1` is a product `n * (n - 1) * ... * (n - k)` with `0 ≤ k ≤ n - 2`. -/
def IsOfForm (n p : ℕ) : Prop :=
  ∃ k ∈ Finset.range (n - 1), p + 1 = ∏ i ∈ Finset.range (k + 1), (n - i)

/-- Smallest prime of the form `n * (n - 1) * ... * (n - k) - 1`, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ IsOfForm n p}

theorem main : ∀ n : ℕ, 3 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a092925
