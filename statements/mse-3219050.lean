import Mathlib

/-!
# `2 ^ n - n` and `2 ^ n + n` simultaneously prime

Source: https://math.stackexchange.com/questions/3219050
Credit: @Andyi955

The question asks (verbatim):

  "Are `3`, `9` the only natural numbers `n` for which both `2 ^ n - n` and `2 ^ n + n` are
  prime?"

## Encoding

* `n` ranges over the natural numbers, exactly as in the source.
* "Both `2 ^ n - n` and `2 ^ n + n` are prime" is the conjunction of `(2 ^ n - n).Prime` and
  `(2 ^ n + n).Prime`. The subtraction is natural-number subtraction; it is only truncated when
  `2 ^ n < n`, which happens only at `n = 0`, where `2 ^ n - n = 1` is not prime anyway, so no
  case of the question is affected.
* The answer asserted by the source is that `3` and `9` are the only ones, i.e. `n = 3 ∨ n = 9`.
-/

namespace OMA.S_mse_3219050

theorem main :
    ∀ n : ℕ, (2 ^ n - n).Prime → (2 ^ n + n).Prime → n = 3 ∨ n = 9 := by
  sorry

end OMA.S_mse_3219050
