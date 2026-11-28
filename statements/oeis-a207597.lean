import Mathlib

/-!
# A207597: Number of n X 6 0..1 arrays avoiding 0 0 0 and 0 1 0 horizontally and 0 0 1 and 1 0 1 vertically.

Source: https://oeis.org/A207597
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 25*x*(1 + 20*x + 6*x^2 - 4*x^3 + x^4) / (1 - x)^5.
* a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with n rows and 6 columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 0 or 0 1 0 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 1 0 1.
An independent transfer-matrix count reproduces the first 25 listed terms, and each formula was checked against every listed term (n up to 29).
-/

namespace OMA.S_oeis_a207597

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 1, 0)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 0, 1)))

/-- The number of n × 6 arrays with entries in `0..1` (`n` rows, `6` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 6 → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 : PowerSeries ℚ) = 25 * X * (1 + 20 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a207597
