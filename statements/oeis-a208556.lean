import Mathlib

/-!
# A208556: Number of 4 X n 0..1 arrays avoiding 0 0 0 and 0 0 1 horizontally and 0 0 1 and 0 1 1 vertically.

Source: https://oeis.org/A208556
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 9*x*(1 + 6*x - 8*x^2) / ((1 - x)*(1 + 2*x)*(1 - 4*x)).
* a(n) = (2^(n+1) + 1)^2 for n even.
* a(n) = (2^(n+1) - 1)^2 for n odd.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with 4 rows and n columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 0 or 0 0 1 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 0 1 1.
An independent transfer-matrix count reproduces the first 22 listed terms, and each formula was checked against every listed term (n up to 22).
-/

namespace OMA.S_oeis_a208556

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 1, 1)))

/-- The number of 4 × n arrays with entries in `0..1` (`4` rows, `n` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 4 → Fin n → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) * (1 + 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = 9 * X * (1 + 6 * X - 8 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((2 : ℚ) ^ (n + 1) + 1) ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = ((2 : ℚ) ^ (n + 1) - 1) ^ 2) := by
  sorry

end OMA.S_oeis_a208556
