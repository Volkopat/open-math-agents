import Mathlib

/-!
# OEIS A303432: two hexagonal numbers and two powers of 2

Source: https://oeis.org/A303432
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A303432(n) is the number of ways to write `n` as `a(2a-1) + b(2b-1) + 2^c + 2^d`, where
`a, b, c, d` are nonnegative integers with `a ≤ b` and `c ≤ d`.

Conjecture 1: `a(n) > 0` for all `n > 1`. In other words, any integer `n > 1` can be written as
the sum of two hexagonal numbers and two powers of 2.
Conjecture 2: any integer `n > 1` can be written as `a(2a+1) + b(2b+1) + 2^c + 2^d` with
`a, b, c, d` nonnegative integers.
Conjecture 3: each integer `n > 1` can be written as `a(2a-1) + b(2b+1) + 2^c + 2^d` with
`a, b, c, d` nonnegative integers.

Formalization notes:
* `main` is the conjunction of the three conjectures of the entry.
* Hexagonal numbers `a(2a-1)` with `a ≥ 0` (`2a - 1` is never truncated: for `a = 0` the product
  is `0` either way); powers `2^c` with `c ≥ 0`, so `1` counts. The orderings `a ≤ b`, `c ≤ d` of
  the counting function only avoid double counting.
-/

namespace OMA.S_oeis_a303432

theorem main :
    (∀ n : ℕ, 1 < n → ∃ a b c d : ℕ,
      n = a * (2 * a - 1) + b * (2 * b - 1) + 2 ^ c + 2 ^ d) ∧
    (∀ n : ℕ, 1 < n → ∃ a b c d : ℕ,
      n = a * (2 * a + 1) + b * (2 * b + 1) + 2 ^ c + 2 ^ d) ∧
    (∀ n : ℕ, 1 < n → ∃ a b c d : ℕ,
      n = a * (2 * a - 1) + b * (2 * b + 1) + 2 ^ c + 2 ^ d) := by
  sorry

end OMA.S_oeis_a303432
