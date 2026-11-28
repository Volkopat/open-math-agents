import Mathlib

/-!
# OEIS A024677: least prime factors of averages of consecutive odd primes

Source: https://oeis.org/A024677
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest prime divisor of the `n`-th term of A024675, the averages
`(prime(n+1) + prime(n+2))/2` of two consecutive odd primes. The entry notes that Dickson's
conjecture implies that every prime occurs infinitely many times in the sequence; `main` states
this.

Conventions:
* `prime(i) = Nat.nth Nat.Prime (i - 1)` (`prime(1) = 2`), so the `n`-th average (`n ≥ 1`) is
  `(nth Prime n + nth Prime (n + 1))/2`; least prime divisor is `Nat.minFac`.
-/

namespace OMA.S_oeis_a024677

/-- `a(n)`: least prime factor of the `n`-th average of consecutive odd primes. -/
noncomputable def a (n : ℕ) : ℕ := Nat.minFac ((Nat.nth Nat.Prime n + Nat.nth Nat.Prime (n + 1)) / 2)

/-- Every prime occurs infinitely often. -/
theorem main : ∀ p : ℕ, p.Prime → {n : ℕ | 1 ≤ n ∧ a n = p}.Infinite := by
  sorry

end OMA.S_oeis_a024677
