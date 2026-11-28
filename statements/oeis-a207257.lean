import Mathlib

/-!
# A207257: Number of 6 X n 0..1 arrays avoiding 0 0 1 and 1 0 1 horizontally and 0 1 0 and 1 0 1 vertically.

Source: https://oeis.org/A207257
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 26*x*(1 + 19*x + 2*x^2 - 28*x^3 + 7*x^4 + x^5) / (1 - x)^7.
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with 6 rows and n columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 1 or 1 0 1 and no three consecutive entries of a column (top to bottom) form 0 1 0 or 1 0 1.
An independent transfer-matrix count reproduces the first 25 listed terms, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a207257

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 0, 1)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 1, 0) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 0, 1)))

/-- The number of 6 × n arrays with entries in `0..1` (`6` rows, `n` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin n → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) = 26 * X * (1 + 19 * X + 2 * X ^ 2 - 28 * X ^ 3 + 7 * X ^ 4 + X ^ 5)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a207257
