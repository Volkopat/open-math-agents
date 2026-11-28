import Mathlib

/-!
# A361889: a(n) = S(5,2*n-1)/S(1,2*n-1), where S(r,n) = Sum_{k = 0..floor(n/2)} ( binomial(n,k) - binomial(n,k-1) )^r.

Source: https://oeis.org/A361889
Credit: @ceejcake

OEIS A361889 (offset 1) is `a(n) = S(5, 2n - 1) / S(1, 2n - 1)`, where
`S(r, m) = ∑_{k = 0}^{⌊m / 2⌋} (C(m, k) - C(m, k - 1))^r` with `C(m, -1) = 0`.

Conjecture (Peter Bala, OEIS A361889): the supercongruence
`a(n * p^r) ≡ a(n * p^(r - 1)) (mod p^(3 * r))` holds for all positive integers `n` and `r`
and all primes `p ≥ 5`.

Formalization notes:
* `S r m` is computed in `ℤ`, and the term `C(m, k - 1)` is written as
  `if k = 0 then 0 else C(m, k - 1)`, which implements the convention `C(m, -1) = 0`
  and avoids natural-number subtraction in the index. The difference `C(m, k) - C(m, k - 1)`
  is taken in `ℤ` (it is in fact `≥ 0` for `k ≤ m / 2`).
* `a n` is defined as the exact rational quotient `S 5 (2n - 1) / S 1 (2n - 1)` in `ℚ`, so no
  integer division is involved. The sum `S 1 m` telescopes to `C(m, ⌊m / 2⌋) > 0`, and the
  quotient is an integer for every term checked (all 420 terms of the OEIS b-file and
  `n ≤ 600`), but the statement does not rely on this.
* The congruence is stated as: `a(n * p^r) - a(n * p^(r - 1)) = p^(3 * r) * c` for some
  integer `c`. When both values are integers (as they are, see above) this is exactly the
  integer congruence `a(n * p^r) ≡ a(n * p^(r - 1)) (mod p^(3 * r))`.
* For `n ≥ 1`, `2 * n - 1` is exact; since `0 < r`, `r - 1` is exact, and `n * p^(r - 1) ≥ 1`.
* Initial values `a(1)..a(6) = 1, 11, 415, 30955, 3173626, 386672861`.
-/

namespace OMA.S_oeis_a361889

/-- `S r m = ∑_{k = 0}^{⌊m / 2⌋} (C(m, k) - C(m, k - 1))^r`, with `C(m, -1) = 0`,
computed in `ℤ`. -/
def S (r m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m / 2 + 1),
    ((m.choose k : ℤ) - (if k = 0 then 0 else (m.choose (k - 1) : ℤ))) ^ r

/-- The sequence OEIS A361889 (offset 1): `a n = S 5 (2n - 1) / S 1 (2n - 1)`,
as an exact rational quotient. -/
def a (n : ℕ) : ℚ := (S 5 (2 * n - 1) : ℚ) / (S 1 (2 * n - 1) : ℚ)

/-- Supercongruence conjecture for OEIS A361889 (Peter Bala): for all primes `p ≥ 5` and
positive integers `n` and `r`, `a(n * p^r) ≡ a(n * p^(r - 1)) (mod p^(3 * r))`, i.e. the
difference is `p^(3 * r)` times an integer. -/
theorem main :
    ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
      ∃ c : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * c := by
  sorry

end OMA.S_oeis_a361889
