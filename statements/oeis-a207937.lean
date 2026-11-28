import Mathlib

/-!
# A207937: Number of n X 7 0..1 arrays avoiding 0 0 1 and 1 0 0 horizontally and 0 0 1 and 1 1 0 vertically.

Source: https://oeis.org/A207937
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(35 + 945*x + 157*x^2 - 1269*x^3 + 863*x^4 - 191*x^5 + 5*x^6 - x^7) / (1 - x)^8.
* a(n) = (1260 + 4974*n - 32165*n^2 - 6041*n^3 + 51940*n^4 + 21091*n^5 + 2905*n^6 + 136*n^7) / 1260.

Conventions: patterns are read left to right along rows and top to bottom along columns (this reading reproduces the OEIS data).
Offset 1: a(n) is the number of arrays with n rows and 7 columns, entries in 0..1, in which no three consecutive entries of a row (left to right) form 0 0 1 or 1 0 0 and no three consecutive entries of a column (top to bottom) form 0 0 1 or 1 1 0.
An independent transfer-matrix count reproduces the first 25 listed terms, and each formula was checked against every listed term (n up to 25).
-/

namespace OMA.S_oeis_a207937

/-- The entry of `x` in row `i`, column `j` (`0` outside the array). -/
def get {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- `x` avoids the two patterns horizontally (three consecutive entries of a row, read left to
right) and the two patterns vertically (three consecutive entries of a column, read top to
bottom). -/
def avoids {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Bool :=
  decide ((∀ i < r, ∀ j < c - 2, (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1) ∧ (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 0, 0)) ∧
    (∀ i < r - 2, ∀ j < c, (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧ (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 1, 0)))

/-- The number of n × 7 arrays with entries in `0..1` (`n` rows, `7` columns) avoiding the patterns. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 7 → Fin 2)).filter (fun x => avoids x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = X * (35 + 945 * X + 157 * X ^ 2 - 1269 * X ^ 3 + 863 * X ^ 4 - 191 * X ^ 5 + 5 * X ^ 6 - X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1260 + 4974 * (n : ℚ) - 32165 * (n : ℚ) ^ 2 - 6041 * (n : ℚ) ^ 3 + 51940 * (n : ℚ) ^ 4 + 21091 * (n : ℚ) ^ 5 + 2905 * (n : ℚ) ^ 6 + 136 * (n : ℚ) ^ 7) / 1260) := by
  sorry

end OMA.S_oeis_a207937
