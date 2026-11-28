import Mathlib

/-!
# A097083: Positive k with a unique permutation p of {1..k} such that i + p(i) is Fibonacci

Source: https://oeis.org/A097083
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Positive values of k such that there is exactly one permutation p of (1, 2, ..., k)
such that i + p(i) is a Fibonacci number for 1 <= i <= k.
Conjecture: a(n) = floor(F(n+3)/sqrt(5)), where F(n) = A000045(n) are Fibonacci numbers.
-/

namespace OMA.S_oeis_a097083

def IsFib (m : ℕ) : Prop :=
  ∃ r : ℕ, Nat.fib r = m

def HasUniqueFibPerm (k : ℕ) : Prop :=
  ∃! p : Equiv.Perm (Fin k), ∀ i : Fin k, IsFib ((i.val + 1) + ((p i).val + 1))

theorem main :
    {k : ℕ | 0 < k ∧ HasUniqueFibPerm k} =
      Set.range (fun n : ℕ => Nat.floor ((Nat.fib (n + 4) : ℝ) / Real.sqrt 5)) := by
  sorry

end OMA.S_oeis_a097083
