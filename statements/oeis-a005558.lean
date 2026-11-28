import Mathlib

/-!
# A005558: Number of n-step walks on square lattice in the first octant 0 <= y <= x

Source: https://oeis.org/A005558
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `a(n)` be the number of `n`-step walks on the integer square lattice `ℤ²` starting at
`(0, 0)` with unit steps `(±1, 0), (0, ±1)` such that every visited point `(x, y)` satisfies
`0 ≤ y ≤ x`.

Conjecture: For all `n ≥ 2`,
`(2*n + 1)*(n + 3)*(n + 2)*a(n) - 4*(2*n^2 + 4*n + 3)*a(n - 1) - 16*n*(2*n + 3)*(n - 1)*a(n - 2) = 0`.
-/

namespace OMA.S_oeis_a005558

/-- The four unit lattice steps on `ℤ × ℤ`. -/
def stepDir : Fin 4 → ℤ × ℤ
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (-1, 0)
  | ⟨2, _⟩ => (0, 1)
  | ⟨3, _⟩ => (0, -1)

/-- Position after the first `k` steps of a walk `w : Fin n → Fin 4` starting at `(0, 0)`. -/
def walkPos {n : ℕ} (w : Fin n → Fin 4) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | k + 1 =>
    let p := walkPos w k
    if h : k < n then
      let d := stepDir (w ⟨k, h⟩)
      (p.1 + d.1, p.2 + d.2)
    else
      p

/-- A walk stays in the first octant `0 ≤ y ≤ x` at every step. -/
def isOctantWalk {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ k : ℕ, k ≤ n → 0 ≤ (walkPos w k).2 ∧ (walkPos w k).2 ≤ (walkPos w k).1

/-- Number of `n`-step walks starting at `(0, 0)` staying in `0 ≤ y ≤ x`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card { w : Fin n → Fin 4 // isOctantWalk w }

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (2 * (n : ℤ) + 1) * ((n : ℤ) + 3) * ((n : ℤ) + 2) * (a n : ℤ)
        - 4 * (2 * (n : ℤ) ^ 2 + 4 * (n : ℤ) + 3) * (a (n - 1) : ℤ)
        - 16 * (n : ℤ) * (2 * (n : ℤ) + 3) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a005558
