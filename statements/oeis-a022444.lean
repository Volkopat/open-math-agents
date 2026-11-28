import Mathlib

/-!
# OEIS A022444: self-avoiding closed walks of length `2n` in the strip `{-1, 0, 1} × ℤ`

Source: https://oeis.org/A022444
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of self-avoiding closed walks from `(0,0)` to `(0,0)` of length `2n` on the
square lattice restricted to the strip `{-1, 0, 1} × ℤ`
(`1, 0, 8, 16, 44, 112, 252, 564, 1276, 2840, …`, offset 0).
Conjecture (formula field of the entry): the generating function is
`(-12x⁷ + 16x⁶ - 36x⁵ + 37x⁴ - 24x³ + 14x² - 4x + 1) / ((1 + x²)² (1 - 2x)²)`.

Conventions (the same as the merged statement of the sibling entry A022445):
* The lattice graph joins two points of `ℤ × ℤ` at distance `1`; the strip graph is its induced
  subgraph on the points with first coordinate in `{-1, 0, 1}`.
* A self-avoiding closed walk of positive length is a Mathlib `Walk.IsCycle` from the origin to
  itself (no repeated vertex except the start, which is also the end; a cycle has length `≥ 3`, so
  going back and forth along one edge is excluded, matching `a(1) = 0`). Walks are counted with
  their direction and with the origin as the fixed start, matching `a(2) = 8` (the origin lies in
  the middle column, so four unit squares have it as a corner, two directions each). The empty
  walk is the unique closed walk of length `0`, matching `a(0) = 1`.
* A brute-force count with these conventions reproduces the first ten terms of the entry, and the
  conjectured generating function reproduces its first fifteen terms.
* The generating-function identity is stated in `PowerSeries ℤ`, after clearing the denominator,
  which is a unit there (constant term `1`), so it is equivalent to the stated quotient.
-/

namespace OMA.S_oeis_a022444

open PowerSeries

/-- The square lattice on `ℤ × ℤ`: two points are adjacent when they are at distance `1`. -/
def lattice : SimpleGraph (ℤ × ℤ) where
  Adj p q := |p.1 - q.1| + |p.2 - q.2| = 1
  symm := ⟨fun (p q : ℤ × ℤ) (h : |p.1 - q.1| + |p.2 - q.2| = 1) =>
    show |q.1 - p.1| + |q.2 - p.2| = 1 by rw [abs_sub_comm q.1, abs_sub_comm q.2]; exact h⟩
  loopless := ⟨fun (p : ℤ × ℤ) (h : |p.1 - p.1| + |p.2 - p.2| = 1) => by simp at h⟩

/-- The points of the strip `{-1, 0, 1} × ℤ`. -/
def stripSet : Set (ℤ × ℤ) := {p | -1 ≤ p.1 ∧ p.1 ≤ 1}

/-- The lattice restricted to the strip. -/
def strip : SimpleGraph stripSet := lattice.induce stripSet

/-- The origin `(0,0)` as a vertex of the strip. -/
def origin : stripSet := ⟨(0, 0), by simp [stripSet]⟩

/-- `A022444(n)`: the number of self-avoiding closed walks of length `2n` from the origin. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {w : strip.Walk origin origin | w.length = 2 * n ∧ (n = 0 ∨ w.IsCycle)}

/-- The conjectured generating function, with the denominator cleared. -/
theorem main :
    (PowerSeries.mk fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 14 * X ^ 2 - 24 * X ^ 3 + 37 * X ^ 4 - 36 * X ^ 5 + 16 * X ^ 6
        - 12 * X ^ 7 := by
  sorry

end OMA.S_oeis_a022444
