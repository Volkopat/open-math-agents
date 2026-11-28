import Mathlib

/-!
# A245952: Number of length 2+3 0..n arrays with some pair in every consecutive four terms totalling exactly n.

Source: https://oeis.org/A245952
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(26 + 145*x + 230*x^2 + 299*x^3 + 18*x^4 - 141*x^5 - 2*x^6 + x^7) / ((1 - x)^5*(1 + x)^3).
* a(n) = 1 + 12*n - 5*n^2 + 18*n^3 + 3*n^4 for n even.
* a(n) = 16 - 5*n - 6*n^2 + 18*n^3 + 3*n^4 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_4) of length 5 with entries in 0..n such that every 4 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 32).
-/

namespace OMA.S_oeis_a245952

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 5 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 5 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 4 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Bool :=
  decide (∀ i < (2 : ℕ), ∃ s < (4 : ℕ), ∃ t < (4 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 5 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (26 + 145 * X + 230 * X ^ 2 + 299 * X ^ 3 + 18 * X ^ 4 - 141 * X ^ 5 - 2 * X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 12 * (n : ℚ) - 5 * (n : ℚ) ^ 2 + 18 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 16 - 5 * (n : ℚ) - 6 * (n : ℚ) ^ 2 + 18 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 4) := by
  sorry

end OMA.S_oeis_a245952
