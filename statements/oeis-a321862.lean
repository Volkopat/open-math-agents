import Mathlib

/-!
# A321862: a(n) = A321857(prime(n))

Source: https://oeis.org/A321862

Conjecture (OEIS A321862):
Let `a(n) = -∑_{i=1}^n (5 / prime(i))` be the Chebyshev bias at the `n`-th prime for
quadratic nonresidues versus residues modulo `5` (i.e., the number of primes `≤ prime(n)`
congruent to `2` or `3 (mod 5)` minus those congruent to `1` or `4 (mod 5)`).
Although the first `10000` terms are positive, it is conjectured that infinitely many
terms are negative.

Conventions:
- Offset: `1` (`n ≥ 1`).
- First terms: `1, 2, 2, 3, 2, 3, 4, 3, 4, 3, 2, 3, 2, 3, 4, ...`.
- `chi5Neg p` equals `+1` for `p ≡ 2, 3 (mod 5)`, `-1` for `p ≡ 1, 4 (mod 5)`, and `0`
  for `p = 5`.
-/

namespace OMA.S_oeis_a321862

/-- Negated Kronecker symbol `-(5 / p)` for prime `p`. -/
def chi5Neg (p : ℕ) : ℤ :=
  if p % 5 = 2 ∨ p % 5 = 3 then 1
  else if p % 5 = 1 ∨ p % 5 = 4 then -1
  else 0

/-- `a(n) = A321857(prime(n))` for `n ≥ 1` (OEIS A321862). -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, chi5Neg (Nat.nth Nat.Prime i)

/-- Conjecture: infinitely many terms of A321862 are negative. -/
theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a n < 0} := by
  sorry

end OMA.S_oeis_a321862
