import Mathlib

/-!
# A246826: Numbers n such that there is no prime of a prime twin pair between n^2 + n and n^2 + 3*n + 2.

Source: https://oeis.org/A246826
Credit: @luciusacarr

Data: 0, 10, 26, 30, 36, 136, 156, 433. No more values for n = 434 to 45140.

Conjecture (from the entry): the sequence is finite and given in full.

Reading of the source:
* "Between" is strict: the entry's example for n = 0 says only 1 lies between 0 and 2, and for
  n = 1 that 3 lies between 2 and 6. So the interval is `n^2 + n < p < n^2 + 3n + 2`.
* "A prime of a prime twin pair" is a prime `p` such that `p - 2` or `p + 2` is also prime; the
  partner need not lie in the interval (n = 10: the interval (110, 132) contains the primes 113,
  127, 131, none of which has a twin).
* With this reading the terms below 990 are exactly the eight listed (checked numerically).
* "Finite and given in full" is stated as the equality of the set of terms with the listed set.
-/

namespace OMA.S_oeis_a246826

/-- `p` is a member of a pair of twin primes. -/
def IsTwinPrimeMember (p : ℕ) : Prop := p.Prime ∧ ((p + 2).Prime ∨ (2 ≤ p ∧ (p - 2).Prime))

/-- The terms of A246826: no member of a twin prime pair lies strictly between `n^2 + n` and
`n^2 + 3n + 2`. -/
def S : Set ℕ := {n | ∀ p : ℕ, n ^ 2 + n < p → p < n ^ 2 + 3 * n + 2 → ¬ IsTwinPrimeMember p}

theorem main :
    -- The sequence is finite and given in full.
    S = {0, 10, 26, 30, 36, 136, 156, 433} := by
  sorry

end OMA.S_oeis_a246826
