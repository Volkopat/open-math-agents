import Mathlib

/-!
# A208065: Number of n X 4 0..1 arrays avoiding 0 0 0 and 1 1 1 horizontally and 0 0 1 and 0 1 1 vertically.

Source: https://oeis.org/A208065
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(5 + 40*x + 10*x^2 - 22*x^3 - 12*x^4 - 12*x^5 + 10*x^6 + 10*x^7 - 5*x^8) / ((1 - x)^5*(1 + x)^3).
* a(n) = n^2*(n + 8)^2/4 for n>1 and even.
* a(n) = (n - 1)*(n + 1)*(n + 7)*(n + 9)/4 for n>1 and odd.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with n rows and 4 columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 0 or 1 1 1 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 0 1 1.
An independent transfer-matrix count reproduces the first 25 listed terms, and each formula was checked against every listed term (n up to 35).
-/

namespace OMA.S_oeis_a208065

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 1, 1)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 1, 1)))

/-- The number of n × 4 arrays with entries in `0..1` (`n` rows, `4` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 4 → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = 2 * X * (5 + 40 * X + 10 * X ^ 2 - 22 * X ^ 3 - 12 * X ^ 4 - 12 * X ^ 5 + 10 * X ^ 6 + 10 * X ^ 7 - 5 * X ^ 8)) ∧
    (∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = (n : ℚ) ^ 2 * ((n : ℚ) + 8) ^ 2 / 4) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = ((n : ℚ) - 1) * ((n : ℚ) + 1) * ((n : ℚ) + 7) * ((n : ℚ) + 9) / 4) := by
  sorry

end OMA.S_oeis_a208065
