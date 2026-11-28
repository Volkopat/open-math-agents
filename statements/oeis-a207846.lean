import Mathlib

/-!
# A207846: Number of 3 X n 0..1 arrays avoiding 0 0 0 and 0 0 1 horizontally and 0 0 0 and 1 1 1 vertically.

Source: https://oeis.org/A207846
Credit: @sntntHb

A207846 (offset 1): 6, 36, 72, 180, 432, 1044, 2520, …  An array has 3 rows and n columns; no row
contains the consecutive pattern `0 0 0` or `0 0 1`, and no column contains the consecutive pattern
`0 0 0` or `1 1 1`.

The entry records two conjectures (Colin Barker, Jun 25 2018):
- G.f.: `6*x*(1 + 4*x - x^2) / (1 - 2*x - x^2)`;
- `a(n) = 9*(sqrt(2)*((1-sqrt(2))^n*(1+sqrt(2)) + (-1+sqrt(2))*(1+sqrt(2))^n))` for `n > 2`.

Formalization: `a n` counts the arrays `A : Fin 3 → Fin n → Bool` (`A i j` is the entry in row `i`, column `j`, `false` = 0, `true` = 1);
a row pattern `x y z` means three horizontally consecutive entries read left to right, a column
pattern three vertically consecutive entries read top to bottom.  Generating functions are stated
for the sequence with offset 1, i.e. with the coefficient of `x^0` set to `0` (`a 0 = 1` counts the
empty array and is not a term of the sequence).
-/

namespace OMA.S_oeis_a207846

/-- `x y z` (in this order) is none of the forbidden patterns. -/
def Avoids (forbidden : List (Bool × Bool × Bool)) (x y z : Bool) : Prop :=
  (x, y, z) ∉ forbidden

/-- The conditions of A207846 on an `3 X n` array. -/
def IsCounted (n : ℕ) (A : Fin 3 → Fin n → Bool) : Prop :=
  (∀ i : Fin 3, ∀ j : ℕ, ∀ h : j + 2 < n,
    Avoids [(false, false, false), (false, false, true)]
      (A i ⟨j, by omega⟩) (A i ⟨j + 1, by omega⟩) (A i ⟨j + 2, h⟩)) ∧
  (∀ i : ℕ, ∀ h : i + 2 < 3, ∀ j : Fin n,
    Avoids [(false, false, false), (true, true, true)]
      (A ⟨i, by omega⟩ j) (A ⟨i + 1, by omega⟩ j) (A ⟨i + 2, h⟩ j))

/-- `a(n)`: the number of such `3 X n` arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin 3 → Fin n → Bool // IsCounted n A}

/-- The conjectures of the entry. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) =
      6 * PowerSeries.X * (1 + 4 * PowerSeries.X - PowerSeries.X ^ 2)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℝ) = 9 * (Real.sqrt 2 * ((1 - Real.sqrt 2) ^ n * (1 + Real.sqrt 2) +
      (-1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ n))) := by
  sorry

end OMA.S_oeis_a207846
