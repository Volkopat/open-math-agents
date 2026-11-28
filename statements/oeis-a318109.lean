import Mathlib

/-!
# OEIS A318109: supercongruences for Sum_k (3n-2k)!/((n-k)!^3*k!)*(-2)^k

Source: https://oeis.org/A318109
Credit: @sntntHb

A318109 (offset 0): `a(n) = Sum_{k=0..n} (3*n-2*k)!/((n-k)!^3*k!)*(-2)^k`.

Conjecture (Peter Bala, Mar 16 2023): the supercongruence `a(n*p^r) == a(n*p^(r-1))
(mod p^(2*r))` holds for positive integers `n` and `r` and all primes `p >= 5`.

Formalized: the quotient `(3*n-2*k)!/((n-k)!^3*k!)` is the multinomial coefficient of
`3*n-2*k = (n-k) + (n-k) + (n-k) + k`, so the natural-number division in `a` is exact.
`main` states the congruence in `ℤ` modulo `p^(2*r)` for every prime `p >= 5` and all
`n, r >= 1` (checked numerically for small cases).
-/

namespace OMA.S_oeis_a318109

/-- `a(n) = Sum_{k=0..n} (3*n-2*k)!/((n-k)!^3*k!)*(-2)^k`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (((3 * n - 2 * k).factorial / ((n - k).factorial ^ 3 * k.factorial) : ℕ) : ℤ) * (-2) ^ k

theorem main :
    ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (2 * r)] := by
  sorry

end OMA.S_oeis_a318109
