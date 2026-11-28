import Mathlib

/-!
# A240886: Primes p equal to the sum in base-3 of the digits of all primes < p.

Source: https://oeis.org/A240886
Credit: @luciusacarr

Data: 23, 31, 47, 59, 695689, 698471, 883517, 992609, 992737, 993037, 1314239, 1324361, 1324571,
1326511, 1327289, 1766291, 3174029.

Conjecture (Robert G. Wilson v, Jul 27 2014): this sequence is finite and all terms are shown.
`main` states it.

Reading of the source:
* For a prime `p`, the quantity compared with `p` is the sum, over all primes `q < p`, of the sum
  of the base-3 digits of `q` (example: 23 = s(2) + s(10) + s(12) + s(21) + s(102) + s(111) +
  s(122) + s(201), digits in base 3).
* With this reading the terms below 3.2 * 10^6 are exactly the seventeen listed (checked
  numerically).
* "Finite and all terms are shown" is stated as the equality of the set of terms with the listed
  set.
-/

namespace OMA.S_oeis_a240886

/-- The sum of the base-3 digits of all primes less than `p`. -/
def digitSumPrimesBelow (p : ℕ) : ℕ :=
  ∑ q ∈ (Finset.range p).filter Nat.Prime, (Nat.digits 3 q).sum

/-- The terms of A240886. -/
def S : Set ℕ := {p | p.Prime ∧ p = digitSumPrimesBelow p}

theorem main :
    -- The sequence is finite and all terms are shown.
    S = {23, 31, 47, 59, 695689, 698471, 883517, 992609, 992737, 993037, 1314239, 1324361,
      1324571, 1326511, 1327289, 1766291, 3174029} := by
  sorry

end OMA.S_oeis_a240886
