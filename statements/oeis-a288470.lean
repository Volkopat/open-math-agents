import Mathlib

/-!
# OEIS A288470: supercongruences for Sum_k C(n,k)*C(2n,2k)

Source: https://oeis.org/A288470
Credit: @sntntHb

A288470 (offset 0): `a(n) = Sum_{k=0..n} binomial(n,k)*binomial(2*n,2*k)`
(data: 1, 2, 14, 92, 646, 4652, ...).

The entry notes that the Gauss congruences `a(n*p^k) == a(n*p^(k-1)) (mod p^k)` hold for all
primes `p`, and records the conjecture (Peter Bala, Aug 30 2025): the supercongruences
`a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` hold for primes `p >= 5` and positive integers `n`
and `k`.

Formalized: `a n` is the displayed sum in `ℕ`, and `main` states the congruence modulo
`p^(2*k)` for every prime `p >= 5` and all `n, k >= 1`. (Checked numerically for small cases.)
-/

namespace OMA.S_oeis_a288470

/-- `a(n) = Sum_{k=0..n} binomial(n,k)*binomial(2*n,2*k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (2 * n).choose (2 * k)

theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (2 * k)] := by
  sorry

end OMA.S_oeis_a288470
