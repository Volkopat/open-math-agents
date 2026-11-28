import Mathlib

/-!
# A207363: Number of n X 3 0..1 arrays avoiding 0 0 0 and 0 1 1 horizontally and 0 0 1 and 0 1 1 vertically.

Source: https://oeis.org/A207363
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(6 + 24*x + 6*x^2 + 9*x^3 + 6*x^4 - 2*x^5 - 2*x^6 + x^7)/ ((1 - x)^5*(1 + x)^3).
* a(n) = (n^4 + 6*n^3 + 13*n^2 + 12*n + 4) / 4 for n even.
* a(n) = (n^4 + 6*n^3 + 11*n^2 + 6*n) / 4 for n odd.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with n rows and 3 columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 0 or 0 1 1 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 0 1 1.
An independent transfer-matrix count reproduces the first 25 listed terms, and each formula was checked against every listed term (n up to 36).
-/

namespace OMA.S_oeis_a207363

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 1, 1)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 1, 1)))

/-- The number of n × 3 arrays with entries in `0..1` (`n` rows, `3` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 3 → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (6 + 24 * X + 6 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 + 13 * (n : ℚ) ^ 2 + 12 * (n : ℚ) + 4) / 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 + 11 * (n : ℚ) ^ 2 + 6 * (n : ℚ)) / 4) := by
  sorry

end OMA.S_oeis_a207363
