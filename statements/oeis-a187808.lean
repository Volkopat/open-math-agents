import Mathlib

/-!
# A187808: k < n with 2k+3, n(n-k)-1 and n(n+k)-1 all prime

Source: https://oeis.org/A187808

A187808 (offset 1): `a(n) = |{0 ≤ k < n : 2k+3, n(n-k)-1, n(n+k)-1 are all prime}|`:
0, 1, 1, 2, 1, 3, 1, 2, 1, 3, …

Conjecture (Zhi-Wei Sun, Jan 07 2013): `a(n) > 0` for all `n > 1`. Moreover, if `n > 5` is
different from 9, 191, 329, 641, 711, 979, then `2k-3`, `2k+3`, `n(n-k)-1`, `n(n+k)-1` are all
prime for some `0 < k < n`.

Both sentences of the conjecture are stated, as a conjunction. The two further conjectures that
the entry lists afterwards (on `k*n - 1` being a Sophie Germain prime, and on `k*n - 1`, `k*n + 1`
being twin primes) are separate claims and are not part of this statement.

Conventions:
- `a` is indexed as in the OEIS (offset 1) and counts `k` in `Finset.range n`, i.e. `0 ≤ k < n`.
- Everything is in `ℕ`. For `k < n` and `n ≥ 1` we have `n*(n-k) ≥ 1` and `n*(n+k) ≥ 1`, so the
  subtractions of `1` are exact. In the second part `2*k - 3` is a truncated subtraction: for
  `k = 1` the integer `2k-3 = -1` is not prime, and the truncated value `0` is not prime either,
  so the two readings agree.
-/

namespace OMA.S_oeis_a187808

/-- A187808: the number of `0 ≤ k < n` with `2k+3`, `n(n-k)-1` and `n(n+k)-1` all prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter
    (fun k => Nat.Prime (2 * k + 3) ∧ Nat.Prime (n * (n - k) - 1) ∧ Nat.Prime (n * (n + k) - 1))).card

theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, 5 < n → n ∉ ({9, 191, 329, 641, 711, 979} : Finset ℕ) →
      ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (2 * k - 3) ∧ Nat.Prime (2 * k + 3) ∧
        Nat.Prime (n * (n - k) - 1) ∧ Nat.Prime (n * (n + k) - 1)) := by
  sorry

end OMA.S_oeis_a187808
