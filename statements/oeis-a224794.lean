import Mathlib

/-!
# A224794: Smallest prime p such that 2n+1 = 2p - q^3 for some odd prime q, or 0 if no such prime exists.

Source: https://oeis.org/A224794
Credit: @prasledi

Conjecture (in the COMMENTS of A224794): the odd numbers different from a cube are of the form
m = 2p - q^3 where p and q are prime numbers.

Formalization notes:
* The odd numbers of the sequence are 2n+1 with n >= 1, i.e. the odd natural numbers m >= 3;
  m = 1 is a cube, so stating the conjecture for every odd natural number m that is not a cube
  is the same.
* "Different from a cube" means m is not c^3 for any natural number c.
* m = 2p - q^3 is written without subtraction as 2 * p = m + q ^ 3, which is equivalent for
  natural numbers. For odd m this forces q to be odd (q = 2 would make m + q^3 odd), matching
  the odd prime q of the name.
* A brute-force search confirms the conjecture for all odd non-cubes m < 2000 (with q < 3000),
  and reproduces the first terms of the data.
-/

namespace OMA.S_oeis_a224794

/-- The conjecture of A224794: every odd natural number that is not a cube is `2p - q^3` with
`p`, `q` prime. -/
theorem main :
    ∀ m : ℕ, Odd m → (¬ ∃ c : ℕ, m = c ^ 3) →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * p = m + q ^ 3 := by
  sorry

end OMA.S_oeis_a224794
