import Mathlib

/-!
# OEIS A307091: supercongruences for Sum_k (-1)^k*C(n,2k)^2

Source: https://oeis.org/A307091
Credit: @sntntHb

A307091 (offset 0): `a(n) = Sum_{k=0..floor(n/2)} (-1)^k * binomial(n,2*k)^2`
(data: 1, 1, 0, -8, -34, -74, 0, 736, ...).

Conjecture (Peter Bala, Mar 17 2023): the supercongruence `a(n*p^r) == a(n*p^(r-1))
(mod p^(2*r))` holds for positive integers `n` and `r` and all primes `p >= 3`.

Formalized: `a n` is the displayed sum in `ℤ`, and `main` states the congruence modulo
`p^(2*r)` for every prime `p >= 3` and all `n, r >= 1`. (Checked numerically for small cases;
it fails for `p = 2`, which the conjecture excludes.)
-/

namespace OMA.S_oeis_a307091

/-- `a(n) = Sum_{k=0..floor(n/2)} (-1)^k * binomial(n,2*k)^2`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), (-1) ^ k * ((n.choose (2 * k) : ℤ)) ^ 2

theorem main :
    ∀ p n r : ℕ, p.Prime → 3 ≤ p → 0 < n → 0 < r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (2 * r)] := by
  sorry

end OMA.S_oeis_a307091
