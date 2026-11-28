import Mathlib

/-!
# A054726: Equinumerosity of non-crossing and non-nesting graphs on n vertices

Source: https://oeis.org/A054726
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A054726: Number of graphs with n nodes on a circle without crossing edges.

Statement:
From Gus Wiseman, Jun 22 2019: Conjecture: Also the number of simple graphs with vertices
{1..n} not containing any pair of nesting edges. Two edges {a,b}, {c,d} where a < b and c < d
are nesting if a < c and b > d or a > c and b < d.
-/

namespace OMA.S_oeis_a054726

/-- `G` has no pair of crossing edges when vertices `Fin n` are placed in order on a circle. -/
def NonCrossing {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → c < d → G.Adj a b → G.Adj c d →
    ¬ ((a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b))

/-- `G` has no pair of nesting edges on `Fin n`. -/
def NonNesting {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → c < d → G.Adj a b → G.Adj c d →
    ¬ ((a < c ∧ d < b) ∨ (c < a ∧ b < d))

theorem main :
    ∀ n : ℕ,
      {G : SimpleGraph (Fin n) | NonCrossing G}.ncard =
      {G : SimpleGraph (Fin n) | NonNesting G}.ncard := by
  sorry

end OMA.S_oeis_a054726
