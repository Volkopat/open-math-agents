import Mathlib

/-!
# A069941: Lower bounds on the number of primes in [n!, n! + n^2]

Source: https://oeis.org/A069941
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A069941: Number of primes p such that n! <= p <= n! + n^2.

Statement:
Conjecture: if n >= 2 there are at least 3 primes p such that n! <= p <= n! + n^2
(and stronger: for n > 1, a(n) > log(n)).
-/

namespace OMA.S_oeis_a069941

/-- `A069941(n)`: number of primes `p` in `[n!, n! + n^2]`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc n.factorial (n.factorial + n ^ 2)).filter Nat.Prime).card

theorem main :
    ∀ n : ℕ, 2 ≤ n → 3 ≤ a n ∧ Real.log (n : ℝ) < (a n : ℝ) := by
  sorry

end OMA.S_oeis_a069941
