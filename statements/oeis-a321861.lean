import Mathlib

/-!
# A321861: a(n) = A071838(prime(n))

Source: https://oeis.org/A321861

Conjecture (OEIS A321861):
Let `a(n) = -∑_{i=1}^n (2 / prime(i))` be the Chebyshev bias at the `n`-th prime for
quadratic nonresidues versus residues of `2` (i.e., the number of odd primes `≤ prime(n)`
congruent to `3` or `5 (mod 8)` minus those congruent to `1` or `7 (mod 8)`).
Although `a(n) > 0` for `2 ≤ n ≤ 10000`, it is conjectured that infinitely many terms
are negative.

Conventions:
- Offset: `1` (`n ≥ 1`).
- First terms: `0, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, ...`.
- `chi8Neg p` equals `+1` for `p ≡ 3, 5 (mod 8)`, `-1` for `p ≡ 1, 7 (mod 8)`, and `0`
  for `p = 2`.
-/

namespace OMA.S_oeis_a321861

/-- Negated Kronecker symbol `-(2 / p)` for prime `p`. -/
def chi8Neg (p : ℕ) : ℤ :=
  if p % 8 = 3 ∨ p % 8 = 5 then 1
  else if p % 8 = 1 ∨ p % 8 = 7 then -1
  else 0

/-- `a(n) = A071838(prime(n))` for `n ≥ 1` (OEIS A321861). -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, chi8Neg (Nat.nth Nat.Prime i)

/-- Conjecture: infinitely many terms of A321861 are negative. -/
theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a n < 0} := by
  sorry

end OMA.S_oeis_a321861
