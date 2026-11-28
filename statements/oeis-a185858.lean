import Mathlib

/-!
# OEIS A185858: Barker's generating function and closed form

Source: https://oeis.org/A185858 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: 1/128 the number of (n+2) X 3 binary arrays with no 3 X 3
subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.
Data: 4, 22, 124, 694, 3892, 21814, 122284, ...
Formula section: Conjectures from Colin Barker, Apr 17 2018:
G.f.: 2*x*(2 + 3*x) / (1 - 4*x - 9*x^2).
a(n) = ((2 - sqrt(13))^n*(-4+sqrt(13)) + (2+sqrt(13))^n*(4+sqrt(13))) / (3*sqrt(13)).

Formalization notes:
* An array is a function `A : Fin (n + 2) → Fin 3 → Fin 2` (row, then column); `entry A i j`
  is its entry in row `i` and column `j` as a natural number (0 outside the array).
* The 3 X 3 subblocks are given by their top-left corners `(i, j)` with `i : Fin n`, `j : Fin 1`
  (so that rows `i .. i + 2` and columns `j .. j + 2` lie in the array). The trace of a
  subblock is the sum of its three main-diagonal entries. Two subblocks are horizontal
  neighbors when their corners are in the same row and in adjacent columns, and vertical
  neighbors when their corners are in the same column and in adjacent rows.
  This reading reproduces all 20 data terms of the entry.
* `a n` is the number of valid arrays divided by 128 (natural number division; the count is a
  multiple of 128).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a185858

open PowerSeries

/-- The entry of the array `A` in row `i` and column `j`, as a natural number (0 outside). -/
def entry {n : ℕ} (A : Fin (n + 2) → Fin 3 → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < n + 2 ∧ j < 3 then (A ⟨i, h.1⟩ ⟨j, h.2⟩).val else 0

/-- The trace of the `3 × 3` subblock of `A` with top-left corner `(i, j)`. -/
def trace {n : ℕ} (A : Fin (n + 2) → Fin 3 → Fin 2) (i j : ℕ) : ℕ :=
  entry A i j + entry A (i + 1) (j + 1) + entry A (i + 2) (j + 2)

/-- An `(n + 2) × 3` binary array is valid when no `3 × 3` subblock has the same trace as a
horizontal or vertical neighbor `3 × 3` subblock. -/
def valid (n : ℕ) (A : Fin (n + 2) → Fin 3 → Fin 2) : Prop :=
  ∀ (i : Fin n) (j : Fin 1) (i' : Fin n) (j' : Fin 1),
    ((i.val = i'.val ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val)) ∨
      (j.val = j'.val ∧ (i.val + 1 = i'.val ∨ i'.val + 1 = i.val))) →
      trace A i j ≠ trace A i' j'

instance (n : ℕ) : DecidablePred (valid n) := fun A => by
  unfold valid; infer_instance

/-- A185858(n): 1/128 of the number of valid `(n + 2) × 3` binary arrays. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card / 128

/-- Barker's conjectures for A185858 (offset 1): the generating function
2x(2 + 3x) / (1 - 4x - 9x^2), and the closed form for n >= 1. -/
theorem main :
    (1 - 4 * X - 9 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X * (2 + 3 * X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((2 - Real.sqrt 13) ^ n * (-4 + Real.sqrt 13) + (2 + Real.sqrt 13) ^ n * (4 + Real.sqrt 13)) /
        (3 * Real.sqrt 13) := by
  sorry

end OMA.S_oeis_a185858
