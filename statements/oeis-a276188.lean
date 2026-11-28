import Mathlib

/-!
# A276188: Numbers k > 1 such that the number of odd divisors of k-1 is odd and is equal to the number of odd divisors of k+1.

Source: https://oeis.org/A276188
Credit: @luciusacarr

Data: 3, 99, 577, 3363. Any further terms are greater than 10^10 (Charles R Greathouse IV).

Conjecture (from the entry): this sequence is finite. `main` states it.

Reading of the source:
* The number of odd divisors of `m` is the number of odd `d` with `d ∣ m`
  (`((Nat.divisors m).filter Odd).card`).
* With this reading the terms below 10^6 are exactly the four listed (checked numerically).
-/

namespace OMA.S_oeis_a276188

/-- The number of odd divisors of `m` (A001227). -/
def oddDivCount (m : ℕ) : ℕ := ((Nat.divisors m).filter Odd).card

/-- The terms of A276188. -/
def S : Set ℕ :=
  {k | 1 < k ∧ Odd (oddDivCount (k - 1)) ∧ oddDivCount (k - 1) = oddDivCount (k + 1)}

theorem main :
    -- The sequence is finite.
    S.Finite := by
  sorry

end OMA.S_oeis_a276188
