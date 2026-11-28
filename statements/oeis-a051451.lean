import Mathlib

/-!
# A051451: twin primes shifted by `lcm(1, …, x)`

Source: https://oeis.org/A051451
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A051451): for every `n > 2` there exists a twin prime pair `[p, p+2]` with
`p < a(n)` such that `[a(n)+p, a(n)+p+2]` is also a twin prime pair, where
`a(n) = lcm{1, 2, …, x}` and `x` is the `n`-th prime power (A000961).

Conventions:
* A000961 lists the prime powers including `1`, offset 1: `1, 2, 3, 4, 5, 7, 8, 9, …`; so
  `x(1) = 1`, `x(n+1)` is the `n`-th prime power `> 1` (`Nat.nth IsPrimePow (n-1)`, zero-indexed).
-/

namespace OMA.S_oeis_a051451

/-- The `n`-th term of A000961 (offset 1). -/
noncomputable def x (n : ℕ) : ℕ := if n ≤ 1 then 1 else Nat.nth IsPrimePow (n - 2)

/-- `a(n) = lcm(1, …, x(n))`. -/
noncomputable def a (n : ℕ) : ℕ := (Finset.Icc 1 (x n)).lcm id

theorem main :
    ∀ n : ℕ, 2 < n → ∃ p : ℕ, p < a n ∧ p.Prime ∧ (p + 2).Prime ∧
      (a n + p).Prime ∧ (a n + p + 2).Prime := by
  sorry

end OMA.S_oeis_a051451
