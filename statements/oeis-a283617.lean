import Mathlib

/-!
# A283617: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w integers and 0 <= z <= w such that x^3 + 2*y^3 is a square.

Source: https://oeis.org/A283617
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) Let a and b >= a be positive integers with gcd(a,b) squarefree. Then every n = 0, 1, 2, ... can be
written as x^2 + y^2 + z^2 + w^2 with x, y, z, w integers such that a*x^3 + b*y^3 is a square, if and
only if (a,b) is among the ordered pairs (1,2), (1,8), (2,16), (4,23), (4,31), (5,9), (8,9), (8,225),
(9,47), (25,88), (50,54).
(ii) Each n = 0, 1, 2, ... can be written as x^2 + y^2 + z^2 + w^2 with x a nonnegative integer and
y, z, w integers such that a*x^3 + b*y^3 is a square, whenever (a,b) is among the ordered pairs (1,8),
(2,16), (8,1), (9,8), (88,25), (225,8).
(iii) Any positive integer can be written as x^2 + y^2 + z^2 + w^2 with x, y, z integers and w a
positive integer such that x^3 + 19*y^3 + 19*z^3 is an integer cube.

Formalization notes:
* Variables are integers with the stated sign conditions; "a square" is `IsSquare` in ℤ, "an integer
  cube" is s^3 for an integer s.
* Controls (computed): (ii) holds for n < 800 for each listed pair; (iii) holds for 1 ≤ n < 500.
  The "only if" direction of (i) is part of the conjecture and was not tested.
-/

namespace OMA.S_oeis_a283617

/-- Every `n` is `x² + y² + z² + w²` with `a x³ + b y³` a square. -/
def Good (a b : ℤ) : Prop :=
  ∀ n : ℕ, ∃ x y z w : ℤ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ IsSquare (a * x ^ 3 + b * y ^ 3)

/-- The three parts of the conjecture. -/
theorem main :
    (∀ a b : ℕ, 0 < a → a ≤ b → Squarefree (Nat.gcd a b) →
      (Good a b ↔ (a, b) ∈ ({(1, 2), (1, 8), (2, 16), (4, 23), (4, 31), (5, 9), (8, 9), (8, 225),
        (9, 47), (25, 88), (50, 54)} : Finset (ℕ × ℕ)))) ∧
      (∀ a b : ℕ, (a, b) ∈ ({(1, 8), (2, 16), (8, 1), (9, 8), (88, 25), (225, 8)} : Finset (ℕ × ℕ)) →
        ∀ n : ℕ, ∃ x y z w : ℤ, 0 ≤ x ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
          IsSquare ((a : ℤ) * x ^ 3 + b * y ^ 3)) ∧
      ∀ n : ℕ, 0 < n → ∃ x y z w s : ℤ, 0 < w ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        x ^ 3 + 19 * y ^ 3 + 19 * z ^ 3 = s ^ 3 := by
  sorry

end OMA.S_oeis_a283617
