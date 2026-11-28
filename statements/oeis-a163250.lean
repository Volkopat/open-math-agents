import Mathlib

/-!
# A163250: a(n) = A000045(n+6) - (n^2 + 4*n + 8).

Source: https://oeis.org/A163250
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a163250

def a (n : ℕ) : ℕ :=
  Nat.fib (n + 6) - (n ^ 2 + 4 * n + 8)

theorem main : ∀ n : ℕ, n > 2 → a n = (n - 1) ^ 2 + a (n - 1) + a (n - 2) := by
  sorry

end OMA.S_oeis_a163250

