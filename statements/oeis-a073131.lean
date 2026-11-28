import Mathlib

/-!
# A073131: First differences of prime-indexed primes prime(prime(n))

Source: https://oeis.org/A073131
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = prime(prime(n+1)) - prime(prime(n)).
Conjecture: a(n) < (log(prime(prime(n))))^3 for sufficiently large n.
-/

namespace OMA.S_oeis_a073131

/-- The `n`-th prime (1-indexed: `prime1 1 = 2`, `prime1 2 = 3`, ...). -/
noncomputable def prime1 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The `n`-th prime-indexed prime `prime(prime(n))` (1-indexed). -/
noncomputable def pprime (n : ℕ) : ℕ :=
  prime1 (prime1 n)

/-- First differences `a(n) = prime(prime(n+1)) - prime(prime(n))`. -/
noncomputable def a (n : ℕ) : ℕ :=
  pprime (n + 1) - pprime n

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (a n : ℝ) < (Real.log (pprime n : ℝ)) ^ 3 := by
  sorry

end OMA.S_oeis_a073131
