import Mathlib

/-!
# Even numbers as `a + b` with `(a ^ 2 + b ^ 2) / 2` prime

Source: https://math.stackexchange.com/questions/2410720
Credit: @Andyi955

The question asks (verbatim):

  "Conjecture: All even numbers `n > 2` can be written `n = a + b` where `a, b ∈ ℕ⁺` and
  `(a ^ 2 + b ^ 2) / 2 ∈ ℙ`. Is tested for `n < 10,000,000`."

## Encoding

* `n` is a natural number with `2 < n` and `n` even, exactly as in the source.
* `a, b ∈ ℕ⁺` is `0 < a` and `0 < b`.
* `(a ^ 2 + b ^ 2) / 2 ∈ ℙ`: for the quotient to be a positive prime integer the numerator must
  be even, so the hypothesis `2 ∣ a ^ 2 + b ^ 2` is recorded explicitly and the conclusion is
  `((a ^ 2 + b ^ 2) / 2).Prime`. (With `2 ∣ a ^ 2 + b ^ 2`, the natural-number division
  `(a ^ 2 + b ^ 2) / 2` is the honest half of `a ^ 2 + b ^ 2`.)
-/

namespace OMA.S_mse_2410720

theorem main :
    ∀ n : ℕ, 2 < n → Even n →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a + b ∧ 2 ∣ a ^ 2 + b ^ 2 ∧
        ((a ^ 2 + b ^ 2) / 2).Prime := by
  sorry

end OMA.S_mse_2410720
