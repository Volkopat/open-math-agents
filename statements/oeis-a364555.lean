import Mathlib

/-!
# A364555: numbers m such that no triangular number is m times a prime

Source: https://oeis.org/A364555
Credit: @xor2k

Formalizes the OEIS A364555 conjecture (offset 1):
Conjecture: Numbers m such that there is no prime number in the union of all sets
{(2*r -+ 1)/d; (r -+ 1)/(2*d)}, where d is some divisor of m and r = m/d.

Conventions:
* The sequence lists positive integers `m`; `InSeq m` says `0 < m` and there are no `k p : ℕ`
  with `p` prime and `k * (k + 1) / 2 = m * p` (triangular numbers `T(k) = k (k + 1) / 2`,
  `k ≥ 0`; the division is exact since `k (k + 1)` is even).
* The conjecture is read as a characterization of the terms: for every `m > 0`, `m` is a term iff
  for every divisor `d` of `m` (Mathlib `Nat.divisors`), with `r = m / d`, none of the four
  rationals `(2r - 1)/d`, `(2r + 1)/d`, `(r - 1)/(2d)`, `(r + 1)/(2d)` is a prime.
* A rational `x / y` (with `y > 0`) equals a prime `q` iff `x = q * y`; this is how the four
  conditions are written. Since `r ≥ 1`, the natural subtractions `2 * r - 1` and `r - 1` are exact.
-/

namespace OMA.S_oeis_a364555

/-- Membership in A364555: `m > 0` and no triangular number equals `m` times a prime. -/
def InSeq (m : ℕ) : Prop :=
  0 < m ∧ ¬ ∃ k p : ℕ, p.Prime ∧ k * (k + 1) / 2 = m * p

/-- For every `m > 0`: `m` is in A364555 iff no prime equals `(2r ∓ 1)/d` or `(r ∓ 1)/(2d)` for a
divisor `d` of `m` and `r = m / d`. -/
theorem main :
    ∀ m : ℕ, 0 < m →
      (InSeq m ↔
        ∀ d ∈ m.divisors, ∀ q : ℕ, q.Prime →
          2 * (m / d) - 1 ≠ q * d ∧ 2 * (m / d) + 1 ≠ q * d ∧
          m / d - 1 ≠ q * (2 * d) ∧ m / d + 1 ≠ q * (2 * d)) := by
  sorry

end OMA.S_oeis_a364555
