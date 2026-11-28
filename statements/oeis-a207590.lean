import Mathlib

/-!
# A207590: Number of 3 X n 0..1 arrays avoiding 0 0 0 and 0 0 1 horizontally and 0 0 1 and 1 1 1 vertically.

Source: https://oeis.org/A207590
Credit: @sntntHb

A207590 (offset 1): 6, 36, 60, 144, 324, 756, 1728, …  An array has 3 rows and n columns; no row
contains the consecutive pattern `0 0 0` or `0 0 1`, and no column contains the consecutive pattern
`0 0 1` or `1 1 1`.

The entry records two conjectures (Colin Barker, Mar 05 2018):
- G.f.: `6*x*(1 + 5*x + x^2 - 4*x^3) / (1 - x - 3*x^2)`;
- `a(n) = (2^(1-n)*((1-sqrt(13))^n*(-35+13*sqrt(13)) + (1+sqrt(13))^n*(35+13*sqrt(13)))) / (9*sqrt(13))`
  for `n > 2`.

Formalization: `a n` counts the arrays `A : Fin 3 → Fin n → Bool` (`A i j` is the entry in row `i`, column `j`, `false` = 0, `true` = 1);
a row pattern `x y z` means three horizontally consecutive entries read left to right, a column
pattern three vertically consecutive entries read top to bottom.  Generating functions are stated
for the sequence with offset 1, i.e. with the coefficient of `x^0` set to `0` (`a 0 = 1` counts the
empty array and is not a term of the sequence).
-/

namespace OMA.S_oeis_a207590

/-- `x y z` (in this order) is none of the forbidden patterns. -/
def Avoids (forbidden : List (Bool × Bool × Bool)) (x y z : Bool) : Prop :=
  (x, y, z) ∉ forbidden

/-- The conditions of A207590 on an `3 X n` array. -/
def IsCounted (n : ℕ) (A : Fin 3 → Fin n → Bool) : Prop :=
  (∀ i : Fin 3, ∀ j : ℕ, ∀ h : j + 2 < n,
    Avoids [(false, false, false), (false, false, true)]
      (A i ⟨j, by omega⟩) (A i ⟨j + 1, by omega⟩) (A i ⟨j + 2, h⟩)) ∧
  (∀ i : ℕ, ∀ h : i + 2 < 3, ∀ j : Fin n,
    Avoids [(false, false, true), (true, true, true)]
      (A ⟨i, by omega⟩ j) (A ⟨i + 1, by omega⟩ j) (A ⟨i + 2, h⟩ j))

/-- `a(n)`: the number of such `3 X n` arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin 3 → Fin n → Bool // IsCounted n A}

/-- The conjectures of the entry. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2) =
      6 * PowerSeries.X * (1 + 5 * PowerSeries.X + PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℝ) = (2 : ℝ) ^ (1 - (n : ℤ)) * ((1 - Real.sqrt 13) ^ n * (-35 + 13 * Real.sqrt 13) +
      (1 + Real.sqrt 13) ^ n * (35 + 13 * Real.sqrt 13)) / (9 * Real.sqrt 13)) := by
  sorry

end OMA.S_oeis_a207590
