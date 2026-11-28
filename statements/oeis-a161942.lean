import Mathlib

/-!
# A161942: Odd part of sum of divisors of n.

Source: https://oeis.org/A161942
Credit: @eltociear

`a(n)` (offset 1) is the odd part of `σ(n)` (`ArithmeticFunction.sigma 1 n`), the sum of the divisors of `n`: `σ(n)` with every
factor `2` removed (`a(1) = 1`, `a(2) = 3`, `a(3) = 1`, `a(4) = 7`). The entry conjectures:

  iteration of this function will always reach 1.

`main` states that for every `n ≥ 1` (the entry's range), some iterate of `a` starting at `n`
equals `1`. The odd part of `m` is written `m / 2 ^ m.factorization 2`, where
`m.factorization 2` is the exponent of `2` in `m`.
-/

namespace OMA.S_oeis_a161942

/-- OEIS A161942: the odd part of `σ(n)`. -/
def a (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n / 2 ^ (ArithmeticFunction.sigma 1 n).factorization 2

/-- The conjecture in OEIS A161942: iterating `a` from any `n ≥ 1` eventually reaches `1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, a^[k] n = 1 := by
  sorry

end OMA.S_oeis_a161942
-- ci: re-run check-proof
