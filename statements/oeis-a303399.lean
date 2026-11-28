import Mathlib

/-!
# A303399: Number of ordered pairs (a, b) with 0 <= a <= b such that n - 5^a - 5^b can be written as the sum of two triangular numbers.

Source: https://oeis.org/A303399
Credit: @keiichisince1986-bot

A303399 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- A triangular number is `c (c + 1) / 2` with `c : ℕ` (`0` is triangular); `c (c + 1)` is even,
  so the division in `ℕ` is exact.
- `a(n) > 0` means that there are `0 ≤ a ≤ b` such that `n - 5^a - 5^b` is a sum of two triangular
  numbers. We state this without subtraction: `n = 5^a + 5^b + c (c + 1) / 2 + d (d + 1) / 2` for
  some `a ≤ b` and `c, d`, which is equivalent (it forces `5^a + 5^b ≤ n`).
-/

namespace OMA.S_oeis_a303399

theorem main :
    ∀ n : ℕ, 1 < n → ∃ a b c d : ℕ, a ≤ b ∧
        n = 5 ^ a + 5 ^ b + c * (c + 1) / 2 + d * (d + 1) / 2 := by
  sorry

end OMA.S_oeis_a303399
