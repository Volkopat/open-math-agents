import Mathlib

/-!
# A270969: Number of ways to write n as w^4 + x^2 + y^2 + z^2, where w, x, y and z are nonnegative integers with x <= y <= z.

Source: https://oeis.org/A270969
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): for each triple (a,b,c) = (1,2,11), (1,2,12), (1,2,13),
(2,3,5), any natural number can be written as w^4 + a*x^2 + b*y^2 + c*z^2 with w, x, y, z integers.

Formalization notes:
* All exponents are even, so integers and natural numbers give the same values; ℕ is used.
* Controls (computed): for each of the four triples every n < 6000 is represented.
-/

namespace OMA.S_oeis_a270969



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ a b c : ℕ, (a, b, c) ∈ ({(1, 2, 11), (1, 2, 12), (1, 2, 13), (2, 3, 5)} : Finset (ℕ × ℕ × ℕ)) →
      ∀ n : ℕ, ∃ w x y z : ℕ, w ^ 4 + a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n := by
  sorry

end OMA.S_oeis_a270969
