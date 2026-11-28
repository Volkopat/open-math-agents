import Mathlib

/-!
# A275598: Primes p such that the number of odd divisors of p-1 is a prime q which is equal to the number of odd divisors of p+1.

Source: https://oeis.org/A275598
Credit: @luciusacarr

Data: 11, 13, 23, 47, 193, 383, 577. Any further terms are greater than 2 * 10^12 (Dana
Jacobsen).

Conjecture (from the entry): this sequence is finite. `main` states it.

Reading of the source:
* The number of odd divisors of `m` is the number of odd `d` with `d ∣ m`
  (`((Nat.divisors m).filter Odd).card`).
* With this reading the terms below 10^6 are exactly the seven listed (checked numerically).
-/

namespace OMA.S_oeis_a275598

/-- The number of odd divisors of `m` (A001227). -/
def oddDivCount (m : ℕ) : ℕ := ((Nat.divisors m).filter Odd).card

/-- The terms of A275598. -/
def S : Set ℕ :=
  {p | p.Prime ∧ (oddDivCount (p - 1)).Prime ∧ oddDivCount (p - 1) = oddDivCount (p + 1)}

theorem main :
    -- The sequence is finite.
    S.Finite := by
  sorry

end OMA.S_oeis_a275598
