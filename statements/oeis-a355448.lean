import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# OEIS A355448 and the absolute value of A307424

A355448 tests whether the divisor count of a square is coprime to six.
For A307424 we use the multiplicative formula at prime powers given in
that entry by Amiram Eldar. R. J. Mathar recorded the argument for the
identity in A355448 on 7 February 2023.

Sources: https://oeis.org/A355448 and https://oeis.org/A307424
(OEIS Foundation, CC BY-SA 4.0). Credit: @Solitude1312
-/

namespace OMA.S_oeis_a355448

/-- Coefficient at a prime power with exponent e in the series ζ(3s)/ζ(2s). -/
def primePowerValue (e : ℕ) : ℤ :=
  if e % 3 = 0 then 1 else if e % 3 = 1 then 0 else -1

def a307424 (n : ℕ) : ℤ :=
  ∏ p ∈ n.primeFactors, primePowerValue (n.factorization p)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (if (n ^ 2).divisors.card.Coprime 6 then 1 else 0) = (a307424 n).natAbs := by
  sorry

end OMA.S_oeis_a355448
