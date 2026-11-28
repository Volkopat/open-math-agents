import Mathlib

/-!
# A089339: Number of primes of the form concat(n, p) for primes p < n

Source: https://oeis.org/A089339
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Number of primes beginning with n and of the form n concatenated with p where p
takes all the prime values less than n.
Conjecture: There are finitely many zeros in this sequence.
-/

namespace OMA.S_oeis_a089339

/-- Base-10 concatenation of two natural numbers. -/
def concat (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- Number of primes p < n such that concat n p is prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => Nat.Prime p ∧ Nat.Prime (concat n p))).card

theorem main :
    Set.Finite {n : ℕ | 0 < n ∧ a n = 0} := by
  sorry

end OMA.S_oeis_a089339
