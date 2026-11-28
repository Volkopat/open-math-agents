import Mathlib

/-!
# Limiting ratio of ones to zeros in the binary look-and-say sequence (A001387)

Source: https://oeis.org/A001387
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Start from `1`; each term describes the previous one, writing for each maximal run its length
in binary followed by the repeated digit (`1, 11, 101, 111011, …`). Joseph L. Pe conjectured
that the ratio `r(n)` of the number of 1s to the number of 0s converges to about `5/3`;
Johnston gave the exact limit
`((101 - 10√93) a² + (139 - 13√93) a - 76) / 108` with `a = (116 + 12√93)^(1/3)`
(`≈ 1.66572722`). `main` states convergence to this value.

Conventions: words are `List Bool` (`true` = 1); run lengths are written in binary, most
significant digit first; `r(n)` is a real quotient (the term `a(1) = 1` has no zeros and the
quotient is then `0` by Lean convention, which does not affect the limit).
-/

namespace OMA.S_oeis_a001387

open Filter

/-- Maximal runs of a word, as (length, digit). -/
def runs : List Bool → List (ℕ × Bool)
  | [] => []
  | b :: l =>
    match runs l with
    | (k, c) :: r => if c = b then (k + 1, c) :: r else (1, b) :: (k, c) :: r
    | [] => [(1, b)]

/-- Binary digits of `k`, most significant first. -/
def bin (k : ℕ) : List Bool := (Nat.digits 2 k).reverse.map fun d => decide (d = 1)

/-- One look-and-say step. -/
def step (w : List Bool) : List Bool := (runs w).flatMap fun p => bin p.1 ++ [p.2]

/-- `a(n+1)` as a word. -/
def term (n : ℕ) : List Bool := step^[n] [true]

/-- Ratio of 1s to 0s in `a(n+1)`. -/
noncomputable def ratio (n : ℕ) : ℝ :=
  ((term n).count true : ℝ) / ((term n).count false : ℝ)

/-- Johnston's limit. -/
noncomputable def limitValue : ℝ :=
  let s := Real.sqrt 93
  let a := (116 + 12 * s) ^ ((1 : ℝ) / 3)
  ((101 - 10 * s) * a ^ 2 + (139 - 13 * s) * a - 76) / 108

theorem main : Tendsto ratio atTop (nhds limitValue) := by
  sorry

end OMA.S_oeis_a001387
