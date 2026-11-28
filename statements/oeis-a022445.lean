import Mathlib

/-!
# OEIS A022445: self-avoiding closed walks of length `2n` in the strip `{0, 1, 2} × ℤ`

Source: https://oeis.org/A022445
Credit: @PEELY350 (Vihaan Naik; agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of self-avoiding closed walks from `(0,0)` to `(0,0)` of length `2n` on the
square lattice restricted to the strip `{0, 1, 2} × ℤ`
(`1, 0, 4, 10, 34, 94, 222, 516, 1202, 2738, …`).
Conjecture (formula field of the entry): the generating function is
`(1 - 4x + 10x² - 14x³ + 27x⁴ - 18x⁵ + 10x⁶ - 6x⁷) / ((1 + x²)² (1 - 2x)²)`.

Conventions:
* The lattice graph joins two points of `ℤ × ℤ` at distance `1`; the strip graph is its induced
  subgraph on the points with first coordinate in `{0, 1, 2}`.
* A self-avoiding closed walk of positive length is a Mathlib `Walk.IsCycle` from the origin to
  itself (no repeated vertex except the start, which is also the end; a cycle has length `≥ 3`, so
  going back and forth along one edge is excluded, matching `a(1) = 0`). Walks are counted with
  their direction and with the origin as the fixed start, matching `a(2) = 4` (the origin lies on
  the edge of the strip, so two unit squares have it as a corner, two directions each). The empty
  walk is the unique closed walk of length `0`, matching `a(0) = 1`.
* The generating-function identity is stated in `PowerSeries ℤ`, after clearing the denominator,
  which is a unit there (constant term `1`), so it is equivalent to the stated quotient.
-/

namespace OMA.S_oeis_a022445

open PowerSeries

/-- The square lattice on `ℤ × ℤ`: two points are adjacent when they are at distance `1`. -/
def lattice : SimpleGraph (ℤ × ℤ) where
  Adj p q := |p.1 - q.1| + |p.2 - q.2| = 1
  symm := ⟨fun (p q : ℤ × ℤ) (h : |p.1 - q.1| + |p.2 - q.2| = 1) =>
    show |q.1 - p.1| + |q.2 - p.2| = 1 by rw [abs_sub_comm q.1, abs_sub_comm q.2]; exact h⟩
  loopless := ⟨fun (p : ℤ × ℤ) (h : |p.1 - p.1| + |p.2 - p.2| = 1) => by simp at h⟩

/-- The points of the strip `{0, 1, 2} × ℤ`. -/
def stripSet : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 2}

/-- The lattice restricted to the strip. -/
def strip : SimpleGraph stripSet := lattice.induce stripSet

/-- The origin `(0,0)` as a vertex of the strip. -/
def origin : stripSet := ⟨(0, 0), by simp [stripSet]⟩

/-- `A022445(n)`: the number of self-avoiding closed walks of length `2n` from the origin. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {w : strip.Walk origin origin | w.length = 2 * n ∧ (n = 0 ∨ w.IsCycle)}

/-- The conjectured generating function, with the denominator cleared. -/
theorem main :
    (PowerSeries.mk fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 10 * X ^ 2 - 14 * X ^ 3 + 27 * X ^ 4 - 18 * X ^ 5 + 10 * X ^ 6
        - 6 * X ^ 7 := by
  sorry

end OMA.S_oeis_a022445
