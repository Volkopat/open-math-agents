import Mathlib

/-!
# A091259: numerator of sigma_3(n)/sigma(n)

Source: https://oeis.org/A091259 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A091259, offset 1: numerator of sigma_3(n)/sigma(n). Data
1, 3, 7, 73, 21, 21, 43, 39, 757, 63, 111, 73, 157, 129, 147, 151, 273, 2271, 343, 219, ...
Entry A353816, offset 0: a(n) = 1 if n is a number of the form x^2 + xy + y^2, otherwise 0. Data
1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, ...

Formula section of A091259:
Conjecture: a(n) (mod 3) = A353816(n). - Michel Marcus, Aug 11 2024

Formalization notes.
* `a n` is the numerator (`Rat.num`, lowest terms, positive denominator) of the rational number
  sigma_3(n)/sigma(n), where sigma_k is `ArithmeticFunction.sigma k`.
* `c n` is A353816(n): 1 if n = x^2 + x*y + y^2 for some natural numbers x, y, and 0 otherwise.
  (The set of these numbers is the same with integers x, y.)
* `main` says, for each n >= 1 (the offset of A091259): the remainder of a(n) modulo 3 is c(n).
-/

namespace OMA.S_oeis_a091259

/-- A091259(n): the numerator of sigma_3(n)/sigma(n). -/
def a (n : ℕ) : ℤ :=
  ((ArithmeticFunction.sigma 3 n : ℚ) / (ArithmeticFunction.sigma 1 n : ℚ)).num

open Classical in
/-- A353816(n): 1 if n is of the form x^2 + xy + y^2, and 0 otherwise. -/
noncomputable def c (n : ℕ) : ℤ :=
  if ∃ x y : ℕ, n = x ^ 2 + x * y + y ^ 2 then 1 else 0

/-- a(n) mod 3 = A353816(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n % 3 = c n := by
  sorry

end OMA.S_oeis_a091259
