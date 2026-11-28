import Mathlib

/-!
# A207656: Number of n X 3 0..1 arrays avoiding 0 0 0 and 1 1 1 horizontally and 0 0 1 and 1 0 0 vertically.

Source: https://oeis.org/A207656
Credit: @sntntHb

A207656 (offset 1): 6, 36, 84, 198, 474, 1140, 2748, …  An array has n rows and 3 columns; no row
contains the consecutive pattern `0 0 0` or `1 1 1`, and no column contains the consecutive pattern
`0 0 1` or `1 0 0`.

The entry records two conjectures (Colin Barker, Jun 25 2018):
- G.f.: `6*x*(1 + 3*x - 3*x^2 - 2*x^3) / ((1 - x)*(1 - 2*x - x^2))`;
- `a(n) = (3/2)*(2 + (1-2*sqrt(2))*(1-sqrt(2))^n + (1+sqrt(2))^n*(1+2*sqrt(2)))` for `n > 1`.

Formalization: `a n` counts the arrays `A : Fin n → Fin 3 → Bool` (`A i j` is the entry in row `i`, column `j`, `false` = 0, `true` = 1);
a row pattern `x y z` means three horizontally consecutive entries read left to right, a column
pattern three vertically consecutive entries read top to bottom.  Generating functions are stated
for the sequence with offset 1, i.e. with the coefficient of `x^0` set to `0` (`a 0 = 1` counts the
empty array and is not a term of the sequence).
-/

namespace OMA.S_oeis_a207656

/-- `x y z` (in this order) is none of the forbidden patterns. -/
def Avoids (forbidden : List (Bool × Bool × Bool)) (x y z : Bool) : Prop :=
  (x, y, z) ∉ forbidden

/-- The conditions of A207656 on an `n X 3` array. -/
def IsCounted (n : ℕ) (A : Fin n → Fin 3 → Bool) : Prop :=
  (∀ i : Fin n, ∀ j : ℕ, ∀ h : j + 2 < 3,
    Avoids [(false, false, false), (true, true, true)]
      (A i ⟨j, by omega⟩) (A i ⟨j + 1, by omega⟩) (A i ⟨j + 2, h⟩)) ∧
  (∀ i : ℕ, ∀ h : i + 2 < n, ∀ j : Fin 3,
    Avoids [(false, false, true), (true, false, false)]
      (A ⟨i, by omega⟩ j) (A ⟨i + 1, by omega⟩ j) (A ⟨i + 2, h⟩ j))

/-- `a(n)`: the number of such `n X 3` arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin n → Fin 3 → Bool // IsCounted n A}

/-- The conjectures of the entry. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) =
      6 * PowerSeries.X * (1 + 3 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℝ) = 3 / 2 * (2 + (1 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ n +
      (1 + Real.sqrt 2) ^ n * (1 + 2 * Real.sqrt 2))) := by
  sorry

end OMA.S_oeis_a207656
