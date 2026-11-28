import Mathlib

/-!
# OEIS A359842: prime-power congruences for Sum_k C(nk, n+k)

Source: https://oeis.org/A359842
Credit: @sntntHb

A359842 (offset 0): `a(n) = Sum_{k=0..n} binomial(n*k, n+k)` (data: 1, 0, 1, 90, 13690, ...).

Conjectures (Peter Bala, Jan 19 2023): `a(2^k) == 0 (mod 2^(k-1))` and
`a(3^k) == 0 (mod 3^(k+2))` for `k >= 2`; `a(p^k) == 0 (mod p^(k+1))` for all primes `p >= 5`.

Formalized: `a n` is the displayed sum in `ℕ`. `main` is the conjunction of the three
congruences, the first two for `k >= 2` as in the entry and the third for every `k >= 1`
(checked numerically for small cases; for `k = 1` the second one fails, `a(3) = 90`).
-/

namespace OMA.S_oeis_a359842

/-- `a(n) = Sum_{k=0..n} binomial(n*k, n+k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n * k).choose (n + k)

theorem main :
    (∀ k : ℕ, 2 ≤ k → a (2 ^ k) ≡ 0 [MOD 2 ^ (k - 1)]) ∧
    (∀ k : ℕ, 2 ≤ k → a (3 ^ k) ≡ 0 [MOD 3 ^ (k + 2)]) ∧
    (∀ p k : ℕ, p.Prime → 5 ≤ p → 1 ≤ k → a (p ^ k) ≡ 0 [MOD p ^ (k + 1)]) := by
  sorry

end OMA.S_oeis_a359842
