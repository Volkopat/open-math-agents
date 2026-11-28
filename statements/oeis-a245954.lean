import Mathlib

/-!
# A245954: Number of length 4+3 0..n arrays with some pair in every consecutive four terms totalling exactly n.

Source: https://oeis.org/A245954
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(88 + 1325*x + 4478*x^2 + 12178*x^3 + 8990*x^4 + 2708*x^5 - 310*x^6 - 658*x^7 + 2*x^8 - x^9) / ((1 - x)^6*(1 + x)^4).
* a(n) = 1 + 34*n + 6*n^2 - 16*n^3 + 66*n^4 + 15*n^5 for n even.
* a(n) = 58 + 57*n - 80*n^2 - 28*n^3 + 66*n^4 + 15*n^5 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_6) of length 7 with entries in 0..n such that every 4 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a245954

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 7 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 7 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 4 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Bool :=
  decide (∀ i < (4 : ℕ), ∃ s < (4 : ℕ), ∃ t < (4 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 7 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 7 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 4 : PowerSeries ℚ) = X * (88 + 1325 * X + 4478 * X ^ 2 + 12178 * X ^ 3 + 8990 * X ^ 4 + 2708 * X ^ 5 - 310 * X ^ 6 - 658 * X ^ 7 + 2 * X ^ 8 - X ^ 9)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 34 * (n : ℚ) + 6 * (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3 + 66 * (n : ℚ) ^ 4 + 15 * (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 58 + 57 * (n : ℚ) - 80 * (n : ℚ) ^ 2 - 28 * (n : ℚ) ^ 3 + 66 * (n : ℚ) ^ 4 + 15 * (n : ℚ) ^ 5) := by
  sorry

end OMA.S_oeis_a245954
