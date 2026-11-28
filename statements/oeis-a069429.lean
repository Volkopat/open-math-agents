import Mathlib

/-!
# A069429: 3 x n binary arrays without monochromatic top-to-bottom path

Source: https://oeis.org/A069429
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069429: Half the number of 3 X n binary arrays with no path of adjacent 1's or
adjacent 0's from top row to bottom row.

Statement:
a(n) = 2^(n-1) * Fibonacci(2*n+2) (for n >= 1).

Conventions:
- Cells of a `3 x n` binary array are `(r, c) : Fin 3 × Fin n`.
- Two cells are orthogonally adjacent if their Manhattan distance is `1`.
- A monochromatic top-to-bottom path is a list of cells starting in row `0`, ending in row `2`,
  all having the same boolean value, with consecutive cells orthogonally adjacent.
-/

namespace OMA.S_oeis_a069429

/-- Orthogonal adjacency in the `3 x n` grid. -/
def GridAdj {n : ℕ} (u v : Fin 3 × Fin n) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
  (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))

/-- `A` contains a monochromatic orthogonal path of color `b` from row `0` to row `2`. -/
def HasMonoPath {n : ℕ} (A : Fin 3 × Fin n → Bool) (b : Bool) : Prop :=
  ∃ L : List (Fin 3 × Fin n),
    ∃ (h0 : 0 < L.length),
      (L[0]'h0).1 = 0 ∧
      (L[L.length - 1]'(Nat.sub_lt h0 Nat.one_pos)).1 = 2 ∧
      (∀ u ∈ L, A u = b) ∧
      L.Chain' GridAdj

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      {A : Fin 3 × Fin n → Bool | ¬ HasMonoPath A true ∧ ¬ HasMonoPath A false}.ncard =
        2 ^ n * Nat.fib (2 * n + 2) := by
  sorry

end OMA.S_oeis_a069429
