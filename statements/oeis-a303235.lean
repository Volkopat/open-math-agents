import Mathlib

/-!
# A303235: Number of ordered pairs (x, y) with 0 <= x <= y such that n - 2^x - 2^y can be written as the sum of two triangular numbers.

Source: https://oeis.org/A303235
Credit: @keiichisince1986-bot

A303235 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- A triangular number is `a (a + 1) / 2` with `a : ℕ` (`0` is triangular); `a (a + 1)` is even,
  so the division in `ℕ` is exact.
- `a(n) > 0` means that there are `0 ≤ x ≤ y` such that `n - 2^x - 2^y` is a sum of two triangular
  numbers. We state this without subtraction: `n = 2^x + 2^y + a (a + 1) / 2 + b (b + 1) / 2` for
  some `x ≤ y` and `a, b`, which is equivalent (it forces `2^x + 2^y ≤ n`).
-/

namespace OMA.S_oeis_a303235

theorem main :
    ∀ n : ℕ, 1 < n → ∃ x y a b : ℕ, x ≤ y ∧
        n = 2 ^ x + 2 ^ y + a * (a + 1) / 2 + b * (b + 1) / 2 := by
  sorry

end OMA.S_oeis_a303235
