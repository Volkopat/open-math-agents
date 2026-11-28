import Mathlib

/-!
# A047212: Arboricity of the n x n queen graph

Source: https://oeis.org/A047212
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A047212: Numbers that are congruent to {0, 2, 4} mod 5.

Statement:
Except for a(1) and a(4), also the arboricity of the n X n queen graph (conjectured).

Conventions:
- The `n x n` queen graph has vertex set `Fin n × Fin n`, with distinct squares adjacent iff
  they share a row, column, or diagonal.
- The arboricity of a graph `G` is the minimum `k` such that `G` can be covered by `k`
  acyclic subgraphs (forests).
- `a(n)` is 1-indexed (`a(1) = 0, a(2) = 2, a(3) = 4, a(4) = 5, a(5) = 7, ...`).
-/

namespace OMA.S_oeis_a047212

/-- The `n x n` queen graph on `Fin n × Fin n`. -/
def queenGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.fromRel fun u v =>
    u.1 = v.1 ∨ u.2 = v.2 ∨
      ((u.1 : ℤ) - (v.1 : ℤ)).natAbs = ((u.2 : ℤ) - (v.2 : ℤ)).natAbs

/-- Arboricity of a simple graph: minimum number of forests covering all its edges. -/
noncomputable def arboricity {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ F : Fin k → SimpleGraph V,
    (∀ i, (F i).IsAcyclic) ∧ (∀ u v, G.Adj u v → ∃ i, (F i).Adj u v)}

/-- The 1-indexed sequence `A047212`: numbers congruent to 0, 2, or 4 mod 5. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m => m % 5 = 0 ∨ m % 5 = 2 ∨ m % 5 = 4) (n - 1)

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 1 → n ≠ 4 → arboricity (queenGraph n) = a n := by
  sorry

end OMA.S_oeis_a047212
