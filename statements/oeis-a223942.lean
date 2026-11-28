import Mathlib

/-!
# A223942: least prime q such that (x^p - 1)/(x - 1) is irreducible modulo q

Source: https://oeis.org/A223942

A223942 (offset 1): `a(n)` is the least prime `q` such that `(x^{p_n} - 1)/(x - 1)` is
irreducible modulo `q`, where `p_n` is the `n`-th prime: 2, 2, 2, 3, 2, 2, 3, 2, 5, 2, …  For
example `a(9) = 5` since `(x^23 - 1)/(x - 1)` is irreducible modulo 5 but reducible modulo 2
and 3. (The entry notes that for an odd prime `p` this polynomial is irreducible modulo `q`
exactly when `q` is a primitive root modulo `p`.)

Conjecture (Zhi-Wei Sun, Mar 29 2013): `a(n) ≤ sqrt(7*p_n)` for all `n > 0`.

Since `a(n)` is the least prime `q` with `(x^p - 1)/(x - 1)` irreducible modulo `q`, the bound
`a(n) ≤ sqrt(7*p)` holds exactly when some such prime `q` satisfies `q^2 ≤ 7*p`, and the
conjecture is stated in that form. Quantifying over all `n > 0` is the same as quantifying over
all primes `p = p_n`.

Conventions: for a prime `p`, `(x^p - 1)/(x - 1) = 1 + x + … + x^(p-1)` is the `p`-th cyclotomic
polynomial, and its reduction modulo `q` is `Polynomial.cyclotomic p (ZMod q)`. Irreducibility
modulo `q` is `Irreducible` in the polynomial ring over `ZMod q`.
-/

namespace OMA.S_oeis_a223942

theorem main :
    ∀ p : ℕ, Nat.Prime p →
      ∃ q : ℕ, Nat.Prime q ∧ Irreducible (Polynomial.cyclotomic p (ZMod q)) ∧
        q ^ 2 ≤ 7 * p := by
  sorry

end OMA.S_oeis_a223942
