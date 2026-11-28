import Mathlib

/-!
# OEIS A099237: prime-power congruences for Sum_k C(n(n-k), k)

Source: https://oeis.org/A099237
Credit: @sntntHb

A099237 (offset 0): `a(n) = Sum_{k=0..n} binomial(n*(n-k), k)` (data: 1, 1, 3, 10, 45, 251, ...).

Conjectures (Peter Bala, Jan 19 2023): `a(2^k) == 1 (mod 2^k)` and `a(3^k) == 1 (mod 3^(k+1))`;
`a(p^k) == 1 (mod p^(k+1))` for all primes `p >= 5`.

Formalized: `a n` is the displayed sum in `ℕ` (`n - k` never truncates for `k <= n`), and `main`
is the conjunction of the three congruences for every `k >= 1` (checked numerically for small
cases).
-/

namespace OMA.S_oeis_a099237

/-- `a(n) = Sum_{k=0..n} binomial(n*(n-k), k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n * (n - k)).choose k

theorem main :
    (∀ k : ℕ, 1 ≤ k → a (2 ^ k) ≡ 1 [MOD 2 ^ k]) ∧
    (∀ k : ℕ, 1 ≤ k → a (3 ^ k) ≡ 1 [MOD 3 ^ (k + 1)]) ∧
    (∀ p k : ℕ, p.Prime → 5 ≤ p → 1 ≤ k → a (p ^ k) ≡ 1 [MOD p ^ (k + 1)]) := by
  sorry

end OMA.S_oeis_a099237
