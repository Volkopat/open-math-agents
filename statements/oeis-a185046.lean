import Mathlib

/-!
# A185046: Smallest prime p such that 2n+1 = p^3 - 2q for some odd prime q, or 0 if no such prime exists.

Source: https://oeis.org/A185046
Credit: @prasledi

Conjecture (in the COMMENTS of A185046): the odd numbers different from a cube are of the form
m = p^3 - 2q where p and q are prime numbers.

Formalization notes:
* The odd numbers of the sequence are 2n+1 with n >= 1, i.e. the odd natural numbers m >= 3;
  m = 1 is a cube, so stating the conjecture for every odd natural number m that is not a cube
  is the same.
* "Different from a cube" means m is not c^3 for any natural number c.
* The conjecture is stated as written in the comment: p and q are arbitrary primes. The name
  says odd prime q, but the data uses q = 2 (a(11) = 3 because 2*11 + 1 = 23 = 3^3 - 2*2).
* m = p^3 - 2q is written without subtraction as m + 2 * q = p ^ 3, which is equivalent for
  natural numbers.
* A brute-force search confirms the conjecture for all odd non-cubes m < 3000, and reproduces
  the first terms of the data.
-/

namespace OMA.S_oeis_a185046

/-- The conjecture of A185046: every odd natural number that is not a cube is `p^3 - 2q` with
`p`, `q` prime. -/
theorem main :
    ∀ m : ℕ, Odd m → (¬ ∃ c : ℕ, m = c ^ 3) →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m + 2 * q = p ^ 3 := by
  sorry

end OMA.S_oeis_a185046
