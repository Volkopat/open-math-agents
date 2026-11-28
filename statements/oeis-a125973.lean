import Mathlib

/-!
# A125973: Smallest k such that k^n + k^(n-1) - 1 is prime.

Source: https://oeis.org/A125973
Credit: @keiichisince1986-bot

A125973 is the sequence `a(n)` named in the title. The entry states:
The polynomial x^n + x^(n-1) - 1 is irreducible over the rationals (see Ljunggren link), so the
Bunyakovsky conjecture implies that a(n) always exists. - Robert Israel, Nov 16 2016 (The statement
below is the claim that a(n) always exists, unconditionally.)

Conventions:
- The offset is `1`, so `n ≥ 1`, and `k^n + k^(n-1) ≥ 1` for `k ≥ 1`, so the subtraction is exact there;
  for `k = 0` the truncated value `0` is not prime.
-/

namespace OMA.S_oeis_a125973

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, (k ^ n + k ^ (n - 1) - 1).Prime := by
  sorry

end OMA.S_oeis_a125973
