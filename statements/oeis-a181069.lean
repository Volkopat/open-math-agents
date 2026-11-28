import Mathlib

/-!
# OEIS A181069: a supercongruence for the l.g.f. Sum_{n>=1} [Sum_{k>=0} C(n+k-1,k)^4 x^k] x^n/n

Source: https://oeis.org/A181069
Credit: @sntntHb

A181069: expansion of the logarithmic generating function
`Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^4 * x^k ] * x^n/n`, i.e. this series equals
`Sum_{N>=1} a(N) x^N / N`.

Peter Bala (Aug 04 2026) conjectures: the supercongruence `a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))`
holds for all primes `p >= 5` and positive integers `n` and `k`.

Formalized: comparing coefficients of `x^N` gives
`a(N) = N * Sum_{n=1..N} C(N-1,n-1)^4 / n = Sum_{n=1..N} C(N-1,n-1)^3 * C(N,n)`, using
`N * C(N-1,n-1) = n * C(N,n)`; this is the formula `a(n) = Sum_{k=0..n-1} binomial(n-1,k)^3 *
binomial(n,k)` listed in the entry, taken here as the definition (over `ℕ`). `main` states that
for every prime `p >= 5` and all `n, k >= 1`, `a (n * p^k)` and `a (n * p^(k-1))` are congruent
modulo `p^(3*k)`.
-/

namespace OMA.S_oeis_a181069

/-- `a(n) = Sum_{k=0..n-1} binomial(n-1,k)^3 * binomial(n,k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k ^ 3 * n.choose k

theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a181069
