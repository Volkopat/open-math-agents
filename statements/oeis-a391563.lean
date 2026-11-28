import Mathlib

/-!
# A391563: a(n) is the number of ways to write n = p + q where p is prime and q is the reverse of a prime.

Source: https://oeis.org/A391563
Credit: @azmiozgen

Conjecture (from the entry): a(n) >= 1 for n >= 12.

Formalization notes:
* The reverse of r is the number whose decimal digits are those of r in reverse order
  (`Nat.ofDigits 10 (Nat.digits 10 r).reverse`). a(n) ≥ 1 is the existence of a representation.
* Controls (computed): a(1..30) = 0, 0, 0, 1, 2, 1, 2, 2, 2, 3, 0, 2, 2, 3, 2, 5, 1, 5, 4, 4, 3, 4, 1, 5,
  2, 3, 2, 3, 1, 4, as in the entry; every n with 12 ≤ n < 20000 is represented.
-/

namespace OMA.S_oeis_a391563



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 12 ≤ n → ∃ p r : ℕ, p.Prime ∧ r.Prime ∧
      p + Nat.ofDigits 10 (Nat.digits 10 r).reverse = n := by
  sorry

end OMA.S_oeis_a391563
