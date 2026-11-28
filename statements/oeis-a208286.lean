import Mathlib

/-!
# A208286: Number of n X 7 0..1 arrays avoiding 0 0 0 and 0 0 1 horizontally and 0 0 1 and 1 1 0 vertically.

Source: https://oeis.org/A208286
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(21 + 714*x + 1005*x^2 - 1156*x^3 + 203*x^4 + 86*x^5 - 19*x^6) / (1 - x)^8.
* a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with n rows and 7 columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 0 or 0 0 1 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 1 1 0.
An independent transfer-matrix count reproduces the first 23 listed terms, and each formula was checked against every listed term (n up to 23).
-/

namespace OMA.S_oeis_a208286

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 1, 0)))

/-- The number of n × 7 arrays with entries in `0..1` (`n` rows, `7` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 7 → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = 2 * X * (21 + 714 * X + 1005 * X ^ 2 - 1156 * X ^ 3 + 203 * X ^ 4 + 86 * X ^ 5 - 19 * X ^ 6)) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a208286
