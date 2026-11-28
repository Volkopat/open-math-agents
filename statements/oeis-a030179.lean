import Mathlib

/-!
# A030179: Zarankiewicz's conjecture for the rectilinear crossing number of K_{n,n}

Source: https://oeis.org/A030179
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `a(n) = (⌊n / 2⌋ * ⌊(n - 1) / 2⌋)^2` be the squared quarter-squares (A030179).

Zarankiewicz's conjecture (rectilinear version): For every `n : ℕ`, the rectilinear crossing
number of the complete bipartite graph `K_{n,n}` — the minimum number of pairs of
vertex-disjoint straight-line edges whose open segments intersect, over all straight-line
drawings of `K_{n,n}` in `ℝ²` with distinct vertices and no vertex lying on the open segment
of any edge — is equal to `(⌊n / 2⌋ * ⌊(n - 1) / 2⌋)^2`.
-/

namespace OMA.S_oeis_a030179

/-- A valid straight-line drawing of `K_{n,n}` in `ℝ²`: all `2n` vertices are distinct and
no vertex lies on the open segment of any edge. -/
def validDrawing {n : ℕ} (u v : Fin n → ℝ × ℝ) : Prop :=
  Function.Injective u ∧
  Function.Injective v ∧
  (∀ i j : Fin n, u i ≠ v j) ∧
  (∀ i j k : Fin n, u k ∉ openSegment ℝ (u i) (v j) ∧ v k ∉ openSegment ℝ (u i) (v j))

/-- Number of crossing pairs of vertex-disjoint edges in a straight-line drawing of `K_{n,n}`. -/
noncomputable def crossings {n : ℕ} (u v : Fin n → ℝ × ℝ) : ℕ :=
  Nat.card
    { e : (Fin n × Fin n) × (Fin n × Fin n) //
      e.1.1 < e.2.1 ∧
      e.1.2 ≠ e.2.2 ∧
      (openSegment ℝ (u e.1.1) (v e.1.2) ∩ openSegment ℝ (u e.2.1) (v e.2.2)).Nonempty }

/-- The rectilinear crossing number of `K_{n,n}`. -/
noncomputable def rectilinearCrossingNumber (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ u v : Fin n → ℝ × ℝ, validDrawing u v ∧ crossings u v = k }

theorem main :
    ∀ n : ℕ, rectilinearCrossingNumber n = (n / 2 * ((n - 1) / 2)) ^ 2 := by
  sorry

end OMA.S_oeis_a030179
