import Mathlib

/-!
# Two rational squares versus two integral squares

Source: https://math.stackexchange.com/questions/3767162
Credit: @Andyi955

The question asks (verbatim):

  "Has it been proven that if `n` can be represented as a sum of squares of two rational numbers,
  then it can also be represented as a sum of squares of two integers?"

## Encoding

* `n` is a natural number. The question leaves the domain of `n` implicit; for an arbitrary
  integer the two formulations agree, because a sum of two rational squares is nonnegative, so a
  negative `n` satisfies the hypothesis for no pair. The natural-number reading is the intended
  one, so that is what is stated.
* "`n` is a sum of squares of two rational numbers" is `∃ a b : ℚ, (n : ℚ) = a ^ 2 + b ^ 2`, and
  "`n` is a sum of squares of two integers" is `∃ c d : ℤ, (n : ℤ) = c ^ 2 + d ^ 2`.
-/

namespace OMA.S_mse_3767162

theorem main :
    ∀ n : ℕ, (∃ a b : ℚ, (n : ℚ) = a ^ 2 + b ^ 2) →
      ∃ c d : ℤ, (n : ℤ) = c ^ 2 + d ^ 2 := by
  sorry

end OMA.S_mse_3767162
