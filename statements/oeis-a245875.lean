import Mathlib

/-!
# A245875: Number of length 6+2 0..n arrays with some pair in every consecutive three terms totalling exactly n.

Source: https://oeis.org/A245875
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(68 + 1077*x + 781*x^2 + 633*x^3 - 1143*x^4 - 561*x^5 + 103*x^6 + 3*x^7 - x^8) / ((1 - x)^6*(1 + x)^3).
* a(n) = 1 + 22*n + 31*n^2 + 77*n^3 + 29*n^4 + n^5 for n even.
* a(n) = -5 - 44*n + 10*n^2 + 77*n^3 + 29*n^4 + n^5 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_7) of length 8 with entries in 0..n such that every 3 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 28).
-/

namespace OMA.S_oeis_a245875

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 8 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 3 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Bool :=
  decide (∀ i < (6 : ℕ), ∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 8 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 8 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (68 + 1077 * X + 781 * X ^ 2 + 633 * X ^ 3 - 1143 * X ^ 4 - 561 * X ^ 5 + 103 * X ^ 6 + 3 * X ^ 7 - X ^ 8)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 22 * (n : ℚ) + 31 * (n : ℚ) ^ 2 + 77 * (n : ℚ) ^ 3 + 29 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -5 - 44 * (n : ℚ) + 10 * (n : ℚ) ^ 2 + 77 * (n : ℚ) ^ 3 + 29 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) := by
  sorry

end OMA.S_oeis_a245875
