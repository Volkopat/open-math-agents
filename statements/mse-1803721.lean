import Mathlib

/-!
# A Diophantine conjecture: `n ^ 2 ∣ 3 ^ n + 2 ^ n + 1` only for `n = 3`

Source: https://math.stackexchange.com/questions/1803721
Credit: @Andyi955

The question asks (verbatim):

  "Prove that `n = 3` is the only positive integer greater than `1`, for which
  `n ^ 2 | 3 ^ n + 2 ^ n + 1`. This is a conjecture."

## Encoding

* `n` is a natural number with `1 < n`, exactly as in the source ("positive integer greater than
  1").
* `n ^ 2` divides `3 ^ n + 2 ^ n + 1` is `n ^ 2 ∣ 3 ^ n + 2 ^ n + 1`; the conclusion is `n = 3`.
-/

namespace OMA.S_mse_1803721

theorem main : ∀ n : ℕ, 1 < n → n ^ 2 ∣ 3 ^ n + 2 ^ n + 1 → n = 3 := by
  sorry

end OMA.S_mse_1803721
