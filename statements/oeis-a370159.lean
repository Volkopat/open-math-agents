import Mathlib

/-!
# A370159: Coefficient of x^n in the expansion of ( (1+x) * (1+x+x^2)^2 )^n

Source: https://oeis.org/A370159

`a(n) = [x^n] ((1 + x) * (1 + x + x^2)^2)^n`, offset 0:
1, 3, 19, 132, 963, 7228, 55264, 428067, 3347843, 26378079, ...

Formula section of the entry, Peter Bala, Oct 07 2026:

* `a(n) = Sum_{k = 0..n} binomial(2*n-k,k)*binomial(2*n, n+k)`.
* The Gauss congruences hold; that is, `a(n*p^r) == a(n*p^(r-1)) (mod p^r)` for all primes `p` and
  positive integers `n` and `r`.
* Conjecture: the stronger supercongruences `a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r))` hold for all
  primes `p >= 5` and positive integers `n` and `r`.

The first two items are given by the entry as facts; they are not part of the target. This file
states the one conjectural claim, the supercongruence modulo `p^(2*r)`.

Formalized: `a n` is the coefficient of `x^n` of the `n`-th power of the polynomial
`(1 + x) * (1 + x + x^2)^2` in `ℤ[x]` (the name line of the entry, taken literally; `a 0 = 1`).
`main` quantifies over all natural numbers `p, n, r` with `p` prime, `5 ≤ p`, `0 < n`, `0 < r`,
so `r - 1` is an ordinary subtraction, and states the congruence between integers as
`Int.ModEq` modulo `(p : ℤ)^(2*r)`.
-/

namespace OMA.S_oeis_a370159

/-- A370159: `a(n) = [x^n] ((1 + x) * (1 + x + x^2)^2)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (((1 + Polynomial.X) * (1 + Polynomial.X + Polynomial.X ^ 2) ^ 2 : Polynomial ℤ) ^ n).coeff n

/-- Bala's conjectured supercongruence: `a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r))` for every prime
`p >= 5` and all positive integers `n` and `r`. -/
theorem main :
    ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (2 * r)] := by
  sorry

end OMA.S_oeis_a370159
