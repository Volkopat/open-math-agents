import Mathlib

/-!
# A183682: Number of (n+1) X 3 binary arrays with every 2 X 2 subblock nonsingular.

Source: https://oeis.org/A183682 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (R. H. Hardin, Jan 06 2011), offset 1: a(n) is the number of (n+1) X 3 binary arrays
in which every 2 X 2 subblock is nonsingular. Terms: 12, 32, 80, 208, 528, 1360, 3472, ...
The formula section reads:

  Empirical: a(n) = a(n-1) + 4*a(n-2).
  Conjectures from Colin Barker, Feb 27 2018: (Start)
  G.f.: 4*x*(3 + 5*x) / (1 - x - 4*x^2).
  a(n) = (2^(-1-n)*((1-sqrt(17))^n*(-19+5*sqrt(17)) + (1+sqrt(17))^n*(19+5*sqrt(17)))) / sqrt(17).
  (End)

The empirical recurrence is in R. H. Hardin's entry (undated); the generating function and the
closed form are Colin Barker's. All three are stated here, as a conjunction.

Formalization notes:
* An array is a function `Fin (n + 1) → Fin 3 → Fin 2` (row, column ↦ entry 0 or 1).
  The 2 X 2 subblocks are the contiguous blocks on rows i, i+1 (i < n) and columns j, j+1
  (j < 2). "Nonsingular" means nonzero determinant; `IsValid` asks, for every such block
  [[x, y], [z, w]], that x*w - y*z ≠ 0, computed in ℤ.
* `a n` is the number of valid arrays for n ≥ 1, in ℤ. The entry has offset 1, so the
  generating function has no constant term; accordingly `a 0 := 0` (used only in the
  generating-function clause, where it is the constant coefficient 0).
* The recurrence mentions a(n-2), so it is stated for n ≥ 3, where all terms belong to the
  sequence. The generating function is stated with its denominator cleared in `PowerSeries ℤ`:
  (∑ a(n) x^n) * (1 - x - 4x^2) = 4x(3 + 5x); the denominator has constant term 1, so this is
  equivalent to the quotient form. The closed form is stated in ℝ for every n ≥ 1, with
  2^(-1-n) written as `(2 : ℝ) ^ (-1 - (n : ℤ))` (an integer power).
* Controls: the definition gives a(1..4) = 12, 32, 80, 208, as in the entry.
-/

namespace OMA.S_oeis_a183682

/-- An (n+1) X 3 binary array. -/
abbrev Grid (n : ℕ) := Fin (n + 1) → Fin 3 → Fin 2

/-- Every 2 X 2 subblock (rows i, i+1 and columns j, j+1) has nonzero determinant. -/
def IsValid {n : ℕ} (g : Grid n) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 2,
    ((g i.castSucc j.castSucc).val : ℤ) * (g i.succ j.succ).val -
      ((g i.castSucc j.succ).val : ℤ) * (g i.succ j.castSucc).val ≠ 0

instance {n : ℕ} (g : Grid n) : Decidable (IsValid g) := by
  unfold IsValid
  infer_instance

/-- A183682, offset 1; `a 0 = 0` is the constant coefficient of the generating function. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((Finset.univ.filter (fun g : Grid (n + 1) => IsValid g)).card : ℤ)

open PowerSeries

/-- Hardin's empirical recurrence (n ≥ 3), Barker's generating function with its denominator
cleared, and Barker's closed form (n ≥ 1). -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = a (n - 1) + 4 * a (n - 2)) ∧
    (PowerSeries.mk a * (1 - X - 4 * X ^ 2) = 4 * X * (3 + 5 * X)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (2 : ℝ) ^ (-1 - (n : ℤ)) *
        ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
          (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17)) / Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a183682
