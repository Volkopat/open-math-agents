import Mathlib

/-!
# OEIS A205186: `(n+1) × (n+1)` 0..1 arrays whose 2 × 2 subblocks have clockwise-increase counts
# differing from each horizontal or vertical neighbor

Source: https://oeis.org/A205186
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `(n+1) × (n+1)` 0..1 arrays with the number of clockwise edge increases in
every `2 × 2` subblock differing from each horizontal or vertical neighbor, offset 1
(`16, 40, 124, 256, 736, 1408, …`).

The entry (Colin Barker, Jan 17 2018) states as conjectures:
* the g.f. is `4x (4 + 10x - x² - 16x³) / ((1 - 2x)² (1 + 2x)²)`;
* `a(n) = 8 a(n-2) - 16 a(n-4)` for `n > 3`.
This file states both.

Conventions:
* An array is `M : Fin (n+1) → Fin (n+1) → Fin 2`; `v M i j` reads entry `(i, j)` as a natural
  number (it is only used inside the array).
* The `2 × 2` subblock with top-left corner `(i, j)` (`i, j < n`) has corners `a = (i, j)`,
  `b = (i, j+1)`, `d = (i+1, j+1)`, `c = (i+1, j)`; going clockwise `a → b → d → c → a`, its count is
  the number of these four edges along which the value increases. Two subblocks are horizontal
  neighbors when their corners are `(i, j)` and `(i, j+1)`, vertical neighbors when they are
  `(i, j)` and `(i+1, j)`; the condition is that neighbors have different counts.
  A transfer-matrix count with these conventions reproduces the first ten terms of the entry
  (e.g. `a(1) = 16`: a single subblock has no neighbor).
* The offset is 1. The g.f. is `Σ_{n ≥ 1} a(n) xⁿ` in `PowerSeries ℤ`, with the denominator
  cleared (a unit there). The recurrence is stated for `n ≥ 5`: at `n = 4` it would involve `a(0)`,
  which is not a term of the sequence (the g.f. gives coefficient `0` there, and
  `8 a(2) - 16·0 = 320 ≠ a(4) = 256`), so "n > 3" is read as starting where every term involved is
  defined. An exact computation confirms the g.f. and the recurrence (for `n ≥ 5`) on all
  twenty-five terms of the entry's data.
-/

namespace OMA.S_oeis_a205186

open PowerSeries

/-- Entry `(i, j)` of the array as a natural number (`0` outside the array, never used). -/
def v {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < n + 1 ∧ j < n + 1 then (M ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- Number of clockwise edge increases in the `2 × 2` subblock with top-left corner `(i, j)`. -/
def cw {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → Fin 2) (i j : ℕ) : ℕ :=
  (if v M i j < v M i (j + 1) then 1 else 0) +
  (if v M i (j + 1) < v M (i + 1) (j + 1) then 1 else 0) +
  (if v M (i + 1) (j + 1) < v M (i + 1) j then 1 else 0) +
  (if v M (i + 1) j < v M i j then 1 else 0)

/-- `A205186(n)`: arrays whose neighboring `2 × 2` subblocks have different clockwise counts. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {M : Fin (n + 1) → Fin (n + 1) → Fin 2 |
    (∀ i j, i < n → j + 1 < n → cw M i j ≠ cw M i (j + 1)) ∧
      (∀ i j, i + 1 < n → j < n → cw M i j ≠ cw M (i + 1) j)}

/-- Barker's conjectured g.f. and recurrence. -/
theorem main :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 + 2 * X) ^ 2) =
      4 * X * (4 + 10 * X - X ^ 2 - 16 * X ^ 3) ∧
    ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 8 * a (n - 2) - 16 * a (n - 4) := by
  sorry

end OMA.S_oeis_a205186
