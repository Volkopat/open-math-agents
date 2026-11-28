import Mathlib

/-!
# A308662: Number of ways to write n as (2^a*5^b)^2 + c*(3c+1) + d*(3d+2), where a and b are nonnegative integers, and c and d are integers.

Source: https://oeis.org/A308662
Credit: @keiichisince1986-bot

A308662 is the sequence `a(n)` named in the title. The entry states:
Conjecture 1: a(n) > 0 for all n > 0. [Conjecture 2 is not formalized here.]

Conventions:
- `a, b` are natural numbers and `c, d` are integers; the identity is stated in `ℤ`.
-/

namespace OMA.S_oeis_a308662

theorem main :
    ∀ n : ℕ, 0 < n → ∃ a b : ℕ, ∃ c d : ℤ, (n : ℤ) = ((2 ^ a * 5 ^ b) ^ 2 : ℕ) + c * (3 * c + 1) + d * (3 * d + 2) := by
  sorry

end OMA.S_oeis_a308662
