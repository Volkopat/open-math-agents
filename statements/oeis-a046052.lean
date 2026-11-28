import Mathlib

/-!
# A046052: Number of prime factors of Fermat number F(n)

Source: https://oeis.org/A046052
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (John Selfridge):
The sequence a(n) = number of prime factors of the Fermat number F(n) = 2^(2^n) + 1
is not monotonic, so at some point a(n+1) < a(n).

Conventions:
We count prime factors with multiplicity via `Nat.primeFactorsList` length (Ω(F_n)),
matching OEIS A046052.
-/

namespace OMA.S_oeis_a046052

/-- The n-th Fermat number F(n) = 2^(2^n) + 1. -/
def fermat (n : ℕ) : ℕ :=
  2 ^ (2 ^ n) + 1

/-- Number of prime factors of F(n) counted with multiplicity. -/
def a (n : ℕ) : ℕ :=
  (fermat n).primeFactorsList.length

/-- Selfridge's conjecture: a(n) is not monotonically nondecreasing. -/
theorem main : ∃ n : ℕ, a (n + 1) < a n := by
  sorry

end OMA.S_oeis_a046052
