import Mathlib

/-!
# A377014: a(n) is the number of primes p such that p - 6, p + 6 and 2*n - p are also primes.

Source: https://oeis.org/A377014
Credit: @ceejcake

Conjecture (Lei Zhou, Oct 12 2024, OEIS A377014):
`a(n) = 0 only when n = 1, 2, 3, 4, 5, 6, 19, 31, 331, 499.`

Note for reviewers: the entry's own data gives `a(79) = 0`, and `79` is not in the list
above. The statement below follows the conjecture exactly as the entry words it.

Formalization notes:
* The sequence has offset `1`, so the conjecture is stated for `n ≥ 1`.
* `only when` is read literally: for `n ≥ 1`, `a n = 0` implies that `n` is one of the
  listed values.
* `a n` counts the primes `p` with `p - 6`, `p + 6` and `2 * n - p` all prime. Searching
  `p < 2 * n` is lossless: if `p ≥ 2 * n` then the natural-number difference `2 * n - p`
  is `0`, which is not prime. For `p < 8` the truncated difference `p - 6` is at most `1`,
  which is not prime, so truncated subtraction never creates a spurious solution.
* Initial values for `n = 1, 2, ..., 20`:
  `0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 3, 2, 3, 4, 1, 3, 3, 0, 4`.
-/

namespace OMA.S_oeis_a377014

/-- `a n` is the number of primes `p` such that `p - 6`, `p + 6` and `2 * n - p` are
also primes. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter fun p =>
    p.Prime ∧ (p - 6).Prime ∧ (p + 6).Prime ∧ (2 * n - p).Prime).card

/-- OEIS A377014 conjecture (Lei Zhou): `a n = 0` only when
`n ∈ {1, 2, 3, 4, 5, 6, 19, 31, 331, 499}`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 →
    n ∈ ({1, 2, 3, 4, 5, 6, 19, 31, 331, 499} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a377014
