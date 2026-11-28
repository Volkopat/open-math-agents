import Mathlib

/-!
# A207106: Number of n X 3 0..1 arrays avoiding 0 0 0 and 0 1 1 horizontally and 0 0 1 and 1 1 0 vertically.

Source: https://oeis.org/A207106
Credit: @sntntHb

A207106 (offset 1): 6, 36, 98, 200, 350, 556, 826, …  An array has n rows and 3 columns; no row
contains the consecutive pattern `0 0 0` or `0 1 1` (read left to right), and no column contains the
consecutive pattern `0 0 1` or `1 1 0` (read top to bottom).

The entry records two conjectures (Colin Barker, Feb 20 2018):
- G.f.: `2*x*(3 + 6*x - 5*x^2) / (1 - x)^4`;
- `a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4)` for `n > 4`.

Formalization: `a n` counts the arrays `A : Fin n → Fin 3 → Bool` (`A i j` is the entry in row `i`,
column `j`, `false` = 0, `true` = 1).  The generating function is stated for the sequence with
offset 1, i.e. with the coefficient of `x^0` set to `0` (`a 0 = 1` counts the empty array and is not
a term of the sequence).
-/

namespace OMA.S_oeis_a207106

/-- `x y z` (in this order) is none of the forbidden patterns. -/
def Avoids (forbidden : List (Bool × Bool × Bool)) (x y z : Bool) : Prop :=
  (x, y, z) ∉ forbidden

/-- The conditions of A207106 on an `n X 3` array. -/
def IsCounted (n : ℕ) (A : Fin n → Fin 3 → Bool) : Prop :=
  (∀ i : Fin n, ∀ j : ℕ, ∀ h : j + 2 < 3,
    Avoids [(false, false, false), (false, true, true)]
      (A i ⟨j, by omega⟩) (A i ⟨j + 1, by omega⟩) (A i ⟨j + 2, h⟩)) ∧
  (∀ i : ℕ, ∀ h : i + 2 < n, ∀ j : Fin 3,
    Avoids [(false, false, true), (true, true, false)]
      (A ⟨i, by omega⟩ j) (A ⟨i + 1, by omega⟩ j) (A ⟨i + 2, h⟩ j))

/-- `a(n)`: the number of such `n X 3` arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin n → Fin 3 → Bool // IsCounted n A}

/-- Barker's conjectured recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
      2 * PowerSeries.X * (3 + 6 * PowerSeries.X - 5 * PowerSeries.X ^ 2)) := by
  sorry

end OMA.S_oeis_a207106
