import Mathlib

/-!
# A006234: a(n) = n * 3^(n-4)

Source: https://oeis.org/A006234
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (proved by Doslic, 2013):
For `n ≥ 4`, `a(n) = n * 3^(n-4)` is the number of spanning trees in the book graph
`S_{n-2} □ P_2`, the Cartesian product of the star graph `S_{n-2}` on `n - 2` vertices
and the path graph `P_2` on 2 vertices.
-/

namespace OMA.S_oeis_a006234

/-- The star graph on `k` vertices, with center `0`. -/
def starGraph (k : ℕ) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel (fun u v : Fin k => u.1 = 0 ∧ v.1 ≠ 0)

/-- The book graph `S_k □ P_2`, Cartesian product of `starGraph k` and `P_2`. -/
def bookGraph (k : ℕ) : SimpleGraph (Fin k × Bool) :=
  SimpleGraph.fromRel (fun p q : Fin k × Bool =>
    (p.2 = q.2 ∧ (starGraph k).Adj p.1 q.1) ∨ (p.1 = q.1 ∧ p.2 ≠ q.2))

/-- For every `n ≥ 4`, the number of spanning trees of `S_{n-2} □ P_2` is `n * 3^(n-4)`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      Nat.card { T : (bookGraph (n - 2)).Subgraph // T.IsSpanning ∧ T.coe.IsTree } =
        n * 3 ^ (n - 4) := by
  sorry

end OMA.S_oeis_a006234
