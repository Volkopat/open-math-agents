import Mathlib

/-!
# OEIS A060318: smallest prime factors of odd Catalan numbers

Source: https://oeis.org/A060318
The odd Catalan numbers are `Catalan(2^n - 1)`. Conjecture (checked up to `Catalan(2^2048 - 1)`):
all odd Catalan numbers have smallest prime factor `3`, except `Catalan(3)` (smallest prime
factor `5`) and `Catalan(31)`, `Catalan(255)` (smallest prime factor `7`).

Conventions. `n ≥ 2` (for `n = 1`, `Catalan(1) = 1` has no prime factor); the exceptions are
`n = 2, 5, 8`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a060318

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (catalan (2 ^ n - 1)).minFac =
        if n = 2 then 5 else if n = 5 ∨ n = 8 then 7 else 3 := by
  sorry

end OMA.S_oeis_a060318
