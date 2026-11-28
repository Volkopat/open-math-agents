import Mathlib

/-!
# A073681: Smallest of three consecutive primes whose sum is a prime

Source: https://oeis.org/A073681
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Smallest of three consecutive primes whose sum is a prime.
Conjecture: for n -> infinity, a(n) ~ prime(n) * (log(prime(n)))^C, where C = 8 / Pi^2.
-/

namespace OMA.S_oeis_a073681

open Filter Topology

/-- Predicate that `p` is the smallest of three consecutive primes whose sum is prime. -/
def isTerm (p : ℕ) : Prop :=
  ∃ k : ℕ, p = Nat.nth Nat.Prime k ∧
    Nat.Prime (Nat.nth Nat.Prime k + Nat.nth Nat.Prime (k + 1) + Nat.nth Nat.Prime (k + 2))

/-- The `n`-th term of A073681 (0-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isTerm n

theorem main :
    Tendsto
      (fun n : ℕ =>
        (a n : ℝ) /
          ((Nat.nth Nat.Prime n : ℝ) *
            (Real.log (Nat.nth Nat.Prime n : ℝ)) ^ ((8 : ℝ) / Real.pi ^ 2)))
      atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a073681
