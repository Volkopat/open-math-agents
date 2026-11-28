import Mathlib

/-!
# A077395: Lesser of two successive squarefree numbers whose product is not squarefree.

Source: https://oeis.org/A077395
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: lim_{n->oo} n / a(n) > 0. - Thomas Ordowski and Robert Israel, Aug 18 2015
-/

namespace OMA.S_oeis_a077395

/-- The smallest squarefree number strictly greater than `k`. -/
noncomputable def nextSquarefree (k : ℕ) : ℕ :=
  sInf { m : ℕ | k < m ∧ Squarefree m }

/-- The set of terms of A077395. -/
def termSet : Set ℕ :=
  { k : ℕ | Squarefree k ∧ ¬ Squarefree (k * nextSquarefree k) }

/-- The `n`-th term of A077395 (0-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (· ∈ termSet) n

theorem main :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ) / (a n : ℝ))) Filter.atTop (nhds L) := by sorry

end OMA.S_oeis_a077395
