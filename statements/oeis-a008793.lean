import Mathlib

/-!
# OEIS A008793: a supercongruence for the number of plane partitions in an n x n x n box

Source: https://oeis.org/A008793
Credit: @sntntHb

A008793 (the problem of the calissons): number of ways to tile a hexagon of edge `n` with
diamonds of side 1; also the number of plane partitions whose Young diagrams fit inside an
`n X n X n` box. By MacMahon's formula (listed in the entry),
`a(n) = Product_{i=1..n} Product_{j=1..n} (n+i+j-1)/(i+j-1)`.

Peter Bala (Apr 07 2022) conjectures: the supercongruences
`a(n*p^r) == a(n*p^(r-1))^p (mod p^(4*r))` hold for all primes `p` and positive integers `n`
and `r`.

Formalized: `a n` is MacMahon's product, computed in `ℚ` (it is an integer). The congruence of
the integers `a (n*p^r)` and `a (n*p^(r-1))^p` modulo `p^(4*r)` is expressed as: their difference
is `p^(4*r)` times an integer. `main` states this for every prime `p` and all `n, r >= 1`.
-/

namespace OMA.S_oeis_a008793

/-- MacMahon's formula: `Product_{i=1..n} Product_{j=1..n} (n+i+j-1)/(i+j-1)`. -/
def a (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n, ((n + i + j - 1 : ℕ) : ℚ) / ((i + j - 1 : ℕ) : ℚ)

theorem main :
    ∀ p n r : ℕ, p.Prime → 0 < n → 0 < r →
      ∃ m : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) ^ p = (p : ℚ) ^ (4 * r) * m := by
  sorry

end OMA.S_oeis_a008793
