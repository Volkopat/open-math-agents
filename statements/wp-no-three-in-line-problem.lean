import Mathlib

/-!
# No-three-in-line problem

Source: https://en.wikipedia.org/wiki/No-three-in-line_problem
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The source asks how many points can be placed in an `n × n` grid so that no three of them lie on
a line. At most `2n` points can be placed (pigeonhole on rows), and `2n` is attained for every
`n ≤ 70`, but the source states: it is conjectured that fewer than `2n` points can be placed in
grids of large size (Guy–Kelly 1968, who conjectured more precisely an upper bound of
`c n + o(n)`; Guy later refined the constant to `π / √3`). The source states no exact formula,
so `main` is the headline conjecture: for all sufficiently large `n`, no `2n` points of the
`n × n` grid are free of three collinear points.

Conventions:
* the `n × n` grid is `Fin n × Fin n`, a point `(i, j)` having integer coordinates `(i, j)`;
* three points `p, q, r` are collinear iff the cross product
  `(q.1 - p.1) (r.2 - p.2) - (q.2 - p.2) (r.1 - p.1)` vanishes (computed in `ℤ`), the usual
  criterion for lying on one (not necessarily axis-parallel) line;
* no three in line means no three pairwise distinct points of the set are collinear;
* placing at least `2n` points is the same as placing exactly `2n`, since a subset of a
  no-three-in-line set is again one; we write `2 * n ≤ S.card`.
-/

namespace OMA.S_wp_no_three_in_line_problem

/-- Three grid points lie on a common line (cross product zero, in `ℤ`). -/
def Collinear3 {n : ℕ} (p q r : Fin n × Fin n) : Prop :=
  (((q.1 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)) * (((r.2 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ)) =
    (((q.2 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ)) * (((r.1 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ))

/-- No three pairwise distinct points of `S` lie on a line. -/
def NoThreeInLine {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r → ¬ Collinear3 p q r

theorem main : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset (Fin n × Fin n), NoThreeInLine S → S.card < 2 * n := by
  sorry

end OMA.S_wp_no_three_in_line_problem
