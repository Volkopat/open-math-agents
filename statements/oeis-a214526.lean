import Mathlib

/-!
# A214526: Manhattan distances between n and 1 in a square spiral with positive integers and 1 at the center.

Source: https://oeis.org/A214526
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

## The conjecture

OEIS A214526 (Alex Ratushnyak, Aug 08 2012), offset 1, FORMULA line:

> For n > 1, a(n) = layer(n) + abs(((n-1) mod (2*layer(n)) - layer(n))) (conjectured)
> where layer(n) = ceiling(0.5*sqrt(n) - 0.5). - Karl R. Stephan, Jan 26 2018

## Modelling choices

* The square spiral is the one drawn in the entry's COMMENTS: 1 at the center, 2 directly
  above 1, 3 to the right of 2, and so on clockwise
  (`1 → 2` up, `2 → 3` right, `3 → 5` down, `5 → 7` left, `7 → 10` up, `10 → 13` right, ...).
  As a walk on `ℤ × ℤ` starting from the cell of 1 at the origin, this is the walk made of
  runs `j = 0, 1, 2, ...` in the directions up, right, down, left (cyclically, `j % 4`) of
  lengths `1, 1, 2, 2, 3, 3, ...` (`j / 2 + 1`). The cell of `n` is the sum of the first
  `n - 1` unit steps (`pos n`); `steps n` lists the steps of the first `n` runs, which is
  more than `n - 1` steps.
* `a n` is the Manhattan distance `|x| + |y|` from the cell of `n` to the cell of 1 (the
  origin). This definition reproduces the whole DATA line of the entry.
* `layer n = ⌈0.5 * sqrt n - 0.5⌉` is computed in `ℝ` with `Real.sqrt` and `Int.ceil`.
* `(n-1) mod (2*layer(n))` is `Int.emod`; for `n > 1` we have `layer n ≥ 1`, so the
  modulus is positive and `Int.emod` is the usual nonnegative remainder. The identity is
  stated in `ℤ`, for every `n > 1` as in the source.
-/

namespace OMA.S_oeis_a214526

/-- Direction of run `j` of the spiral: up, right, down, left according to `j % 4`. -/
def dir (j : ℕ) : ℤ × ℤ :=
  if j % 4 = 0 then (0, 1)
  else if j % 4 = 1 then (1, 0)
  else if j % 4 = 2 then (0, -1)
  else (-1, 0)

/-- The unit steps of the first `r` runs; run `j` has length `j / 2 + 1`. -/
def steps (r : ℕ) : List (ℤ × ℤ) :=
  (List.range r).flatMap fun j => List.replicate (j / 2 + 1) (dir j)

/-- The cell of `n` in the spiral (the cell of `1` is the origin). -/
def pos (n : ℕ) : ℤ × ℤ :=
  ((steps n).take (n - 1)).sum

/-- A214526: the Manhattan distance between `n` and `1` in the square spiral. -/
def a (n : ℕ) : ℕ :=
  (pos n).1.natAbs + (pos n).2.natAbs

/-- `layer(n) = ceiling(0.5*sqrt(n) - 0.5)`. -/
noncomputable def layer (n : ℕ) : ℤ :=
  ⌈(0.5 : ℝ) * Real.sqrt n - 0.5⌉

/-- Karl R. Stephan's conjectured formula (Jan 26 2018), for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n →
    (a n : ℤ) = layer n + |((n : ℤ) - 1) % (2 * layer n) - layer n| := by
  sorry

end OMA.S_oeis_a214526
