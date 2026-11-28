import Mathlib

/-!
# A282545: Number of ways to write n as x^4 + y^2 + z^2 + w^2 with y^2 + 64*z^2 + 1024*y*z a square, where x,y,z,w are nonnegative integers with y > 0.

Source: https://oeis.org/A282545
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0.
(ii) Any nonnegative integer can be written as x^4 + y^2 + z^2 + w^2 with x, y, z, w nonnegative
integers such that a*y^2 + b*y*z + c*z^2 is a square, whenever (a,b,c) is among the ordered triples
(1,484,44), (1,666,9), (16,1336,169), (25,900,36).

Formalization notes:
* a(n) > 0 is stated as the existence of a representation.
* Controls (computed): both parts hold for n < 1500 (each triple in (ii)).
-/

namespace OMA.S_oeis_a282545

/-- The conjecture of the entry. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < y ∧ x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (y ^ 2 + 64 * z ^ 2 + 1024 * y * z)) ∧
      ∀ a b c : ℕ, (a, b, c) ∈ ({(1, 484, 44), (1, 666, 9), (16, 1336, 169), (25, 900, 36)} :
          Finset (ℕ × ℕ × ℕ)) →
        ∀ n : ℕ, ∃ x y z w : ℕ, x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
          IsSquare (a * y ^ 2 + b * y * z + c * z ^ 2) := by
  sorry

end OMA.S_oeis_a282545
