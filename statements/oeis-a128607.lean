import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# A128607: Further higher powers among perfect powers and their divisor sums

Source: https://oeis.org/A128607
Related sequence: https://oeis.org/A128608

For an integer greater than one, the gcd of its prime-factorization exponents
is at least three exactly when it is a power with an exponent at least three.
The first question asks for an input-side example besides 81 and 343. The second
asks for another term whose divisor sum has exponent gcd greater than two,
excluding the known input 1857437604 whose divisor sum is 5168743489.
The two questions are expressed using these explicit exceptions.
-/

namespace OMA.S_oeis_a128607

open scoped ArithmeticFunction.sigma

/-- A power of base greater than one and exponent at least `k`. -/
def IsPowerAtLeast (n k : ℕ) : Prop :=
  ∃ b e : ℕ, 1 < b ∧ k ≤ e ∧ b ^ e = n

/-- Both the input-side and output-side questions have affirmative answers. -/
theorem main :
    (∃ n : ℕ, n ≠ 81 ∧ n ≠ 343 ∧ IsPowerAtLeast n 3 ∧ IsPowerAtLeast (σ 1 n) 2) ∧
    (∃ n : ℕ, n ≠ 1857437604 ∧ IsPowerAtLeast n 2 ∧ IsPowerAtLeast (σ 1 n) 3) := by
  sorry

end OMA.S_oeis_a128607
