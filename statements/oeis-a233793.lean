import Mathlib

/-!
# A233793: Least odd prime p such that 2*n - p = sigma(k) for some k > 0, or 0 if such an odd prime p does not exist, where sigma(k) is the sum of all (positive) divisors of k.

Source: https://oeis.org/A233793
Credit: @keiichisince1986-bot

A233793 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1. [The entry adds a stronger claim with sigma(m^2) for n > 180; it is
not formalized here.]

Conventions:
- `sigma(k)` is `ArithmeticFunction.sigma 1 k`.
- `a(n) > 0` means that `2n = p + sigma(k)` for some odd prime `p` and some `k > 0`.
-/

namespace OMA.S_oeis_a233793

theorem main :
    ∀ n : ℕ, 1 < n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < k ∧ p + ArithmeticFunction.sigma 1 k = 2 * n := by
  sorry

end OMA.S_oeis_a233793
