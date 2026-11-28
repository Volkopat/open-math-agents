import Mathlib

/-!
# A207935: Number of n X 5 0..1 arrays avoiding 0 0 1 and 1 0 0 horizontally and 0 0 1 and 1 1 0 vertically.

Source: https://oeis.org/A207935
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(7 + 56*x - 61*x^2 + 9*x^3 + 6*x^4 - x^5) / (1 - x)^6.
* a(n) = (30 - 149*n + 10*n^2 + 250*n^3 + 65*n^4 + 4*n^5) / 15.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with n rows and 5 columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 1 or 1 0 0 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 1 1 0.
An independent transfer-matrix count reproduces the first 25 listed terms, and each formula was checked against every listed term (n up to 30).
-/

namespace OMA.S_oeis_a207935

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 0, 0)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 1, 0)))

/-- The number of n × 5 arrays with entries in `0..1` (`n` rows, `5` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 5 → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = 2 * X * (7 + 56 * X - 61 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - X ^ 5)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (30 - 149 * (n : ℚ) + 10 * (n : ℚ) ^ 2 + 250 * (n : ℚ) ^ 3 + 65 * (n : ℚ) ^ 4 + 4 * (n : ℚ) ^ 5) / 15) := by
  sorry

end OMA.S_oeis_a207935
