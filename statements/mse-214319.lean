import Mathlib

/-!
# When is `⌊7ⁿ / 2ⁿ⌋ mod 2ⁿ ≠ 0`?

Source: https://math.stackexchange.com/questions/214319
Credit: @jagraj28

The question asks whether `⌊7ⁿ / 2ⁿ⌋ mod 2ⁿ ≠ 0` for all `n ≥ 3`. Equivalently, the binary digits
of `7ⁿ` in positions `n, …, 2n - 1` are not all zero. The answers give reformulations and partial
analysis; one reports a computer search from `n = 3` to `n = 2^17` with no counterexample. No
answer settles the question.

`main` states the claim. The bound `n ≥ 3` is needed: for `n = 2`, `⌊49 / 4⌋ = 12 ≡ 0 (mod 4)`.
A search for `n < 20000` finds no other `n ≥ 1` with `⌊7ⁿ / 2ⁿ⌋ ≡ 0 (mod 2ⁿ)`.

Conventions.
* `⌊7ⁿ / 2ⁿ⌋` is natural-number division `7 ^ n / 2 ^ n`, which rounds down.
* `mod 2ⁿ` is `% 2 ^ n`.
-/

namespace OMA.S_mse_214319

/-- For every `n ≥ 3`, `⌊7ⁿ / 2ⁿ⌋` is not divisible by `2ⁿ`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → 7 ^ n / 2 ^ n % 2 ^ n ≠ 0 := by
  sorry

end OMA.S_mse_214319
