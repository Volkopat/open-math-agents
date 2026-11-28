import Mathlib

/-!
# A054727: Linear recurrence for non-crossing rooted forests on a circle

Source: https://oeis.org/A054727
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A054727: Number of forests of rooted trees with n nodes on a circle without crossing edges.

Statement:
Conjecture: -2*(37*n-80)*(n-1)*(2*n-1)*a(n) + 2*(592*n^3-3056*n^2+5045*n-2665)*a(n-1)
+ 2*(148*n^3-986*n^2+2021*n-1255)*a(n-2) - 5*(n-5)*(n-2)*(37*n-43)*a(n-3) = 0.

Conventions:
- The entry counts non-crossing forests on `n` points of a circle: its data 1, 2, 7, 33, 181, ...
  (offset 1) is the number of acyclic non-crossing simple graphs on `Fin n` (for n = 2: the empty
  graph and the single edge). A root choice per component would give 3 for n = 2, so no roots are
  chosen; the recurrence was checked by hand at n = 4 with these values.
- The recurrence is stated for `n >= 4` in `ℤ`.
-/

namespace OMA.S_oeis_a054727

/-- `G` has no pair of crossing edges when vertices `Fin n` are arranged in order on a circle. -/
def NonCrossing {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → c < d → G.Adj a b → G.Adj c d →
    ¬ ((a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b))

/-- `A054727(n)`: number of non-crossing forests on `n` nodes on a circle. -/
noncomputable def a (n : ℕ) : ℤ :=
  ({G : SimpleGraph (Fin n) | G.IsAcyclic ∧ NonCrossing G}.ncard : ℤ)

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      -2 * (37 * (n : ℤ) - 80) * ((n : ℤ) - 1) * (2 * (n : ℤ) - 1) * a n +
      2 * (592 * (n : ℤ) ^ 3 - 3056 * (n : ℤ) ^ 2 + 5045 * (n : ℤ) - 2665) * a (n - 1) +
      2 * (148 * (n : ℤ) ^ 3 - 986 * (n : ℤ) ^ 2 + 2021 * (n : ℤ) - 1255) * a (n - 2) -
      5 * ((n : ℤ) - 5) * ((n : ℤ) - 2) * (37 * (n : ℤ) - 43) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a054727
