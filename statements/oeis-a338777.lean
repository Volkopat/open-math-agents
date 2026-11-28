import Mathlib

/-!
# A338777: a(n) = Product_{k in GB(2*n)} k, where GB(n) is the set of primes which are Goldbach-associated with n.

Source: https://oeis.org/A338777
Credit: @ceejcake

Definition (OEIS A338777, Peter Luschny, Nov 08 2020): a prime `p` is gb-associated with an
integer `m ≥ 0` if `sqrt(m) < p ≤ m/2` and no prime `q ≤ sqrt(m)` divides `p*(p - m)`.
`GB(m)` is the set of primes gb-associated with `m`, and `a(n) = Product_{k in GB(2*n)} k`.

Claim (OEIS A338777, Peter Luschny): If `a(n) != 1` for `n >= 3` then Goldbach's conjecture
is true. In this case `m = max(GB(2*n))` exists and `P = (2*n - m, m)` is a Goldbach partition
of `2*n`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* For natural numbers `p, q` and `m`, the real-number conditions `sqrt(m) < p` and `q ≤ sqrt(m)`
  are equivalent to `Nat.sqrt m < p` and `q ≤ Nat.sqrt m`, so `Nat.sqrt` is used (as in the
  entry's SageMath program, which uses `isqrt`). Likewise `p ≤ m/2` is equivalent to
  `p ≤ m / 2` with natural-number division.
* `p - m` may be negative, so the divisibility `q ∣ p*(p - m)` is stated in `ℤ`.
* `GB m` is a `Finset`; an empty product is `1`, so `a n = 1` exactly when `GB (2 * n)` is empty.
* The statement has two parts, matching the two sentences of the claim:
  1. for every `n ≥ 3` with `a n ≠ 1`, the maximum `m` of `GB (2 * n)` exists and
     `(2 * n - m, m)` is a Goldbach partition of `2 * n` (both parts prime, sum `2 * n`);
  2. if `a n ≠ 1` for all `n ≥ 3`, then every even number `≥ 4` is a sum of two primes
     (Goldbach's conjecture; `4 = 2 + 2` is not covered by the hypothesis, since `2 * n ≥ 6`).
* The definition is computable. Initial values for `n = 0, 1, ..., 12`:
  `a(n) = 1, 1, 1, 3, 3, 5, 5, 7, 5, 35, 7, 55, 385`.
-/

namespace OMA.S_oeis_a338777

/-- `GB m` is the set of primes `p` with `sqrt(m) < p ≤ m/2` such that no prime `q ≤ sqrt(m)`
divides `p * (p - m)`. -/
def GB (m : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.sqrt m + 1) (m / 2)).filter fun p =>
    p.Prime ∧ ∀ q ∈ Finset.range (Nat.sqrt m + 1), q.Prime →
      ¬ ((q : ℤ) ∣ (p : ℤ) * ((p : ℤ) - (m : ℤ)))

/-- `a n` is the product of the elements of `GB (2 * n)`. -/
def a (n : ℕ) : ℕ :=
  ∏ k ∈ GB (2 * n), k

/-- OEIS A338777 claim: if `a n ≠ 1` (for `n ≥ 3`), then `m = max GB(2n)` exists and
`(2n - m, m)` is a Goldbach partition of `2n`; hence, if `a n ≠ 1` for all `n ≥ 3`,
Goldbach's conjecture holds. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n ≠ 1 →
      ∃ m ∈ GB (2 * n), (∀ p ∈ GB (2 * n), p ≤ m) ∧
        (2 * n - m).Prime ∧ m.Prime ∧ (2 * n - m) + m = 2 * n) ∧
    ((∀ n : ℕ, 3 ≤ n → a n ≠ 1) →
      ∀ m : ℕ, 4 ≤ m → Even m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m) := by
  sorry

end OMA.S_oeis_a338777
