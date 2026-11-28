import Mathlib

/-!
# A230223: Primes p such that 3*p-4, 3*p-10, and 3*p-14 are all prime.

Source: https://oeis.org/A230223
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): any even number greater than 35 can be written as a sum of four terms of this sequence.

Formalization notes:
* Terms may repeat in the sum. Subtractions in ℕ only truncate for p ≤ 4, where the value 0 or 2 makes
  the conditions fail as in ℤ (p = 2: 3p - 4 = 2 is prime but 3p - 10 < 0 is not).
* Controls (computed): the terms begin 7, 11, 17, 19, 31, 37, 47, 59; every even n with 35 < n < 8000
  is a sum of four terms.
-/

namespace OMA.S_oeis_a230223

/-- `p` is a term. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ (3 * p - 4).Prime ∧ (3 * p - 10).Prime ∧ (3 * p - 14).Prime

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 35 < n → Even n → ∃ a b c d : ℕ, IsTerm a ∧ IsTerm b ∧ IsTerm c ∧ IsTerm d ∧ a + b + c + d = n := by
  sorry

end OMA.S_oeis_a230223
