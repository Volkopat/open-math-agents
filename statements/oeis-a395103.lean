import Mathlib

/-!
# A395103: Numbers with as many prime factors as primes in a decimal concatenation

Source: https://oeis.org/A395103
Credit: @gblacher2
-/

namespace OMA.S_oeis_a395103

/-- Concatenate the decimal representations from left to right. -/
def concatPrimes (ps : List ℕ) : ℕ :=
  ps.foldl (fun acc p => acc * 10 ^ (Nat.digits 10 p).length + p) 0

/-- Infinitely many numbers are concatenations of `k > 1` primes and have exactly `k`
prime factors counted with multiplicity. The primes in the concatenation may repeat. -/
theorem main :
    {n : ℕ | ∃ ps : List ℕ, 1 < ps.length ∧ ps.length = n.primeFactorsList.length ∧
      (∀ p ∈ ps, p.Prime) ∧ n = concatPrimes ps}.Infinite := by
  sorry

end OMA.S_oeis_a395103
