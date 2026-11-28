import Mathlib

/-!
# A246482: Number of length 3+3 0..n arrays with no pair in any consecutive four terms totalling exactly n.

Source: https://oeis.org/A246482
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(1 + 7*x + 115*x^2 + 251*x^3 + 1161*x^4 + 1045*x^5 + 2001*x^6 + 617*x^7 + 562*x^8) / ((1 - x)^7*(1 + x)^4).
* a(n) = -20*n + 43*n^2 - 40*n^3 + 21*n^4 - 6*n^5 + n^6 for n even.
* a(n) = -26 + 37*n + 5*n^2 - 30*n^3 + 21*n^4 - 6*n^5 + n^6 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that no 4 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 27).
-/

namespace OMA.S_oeis_a246482

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: no 4 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (3 : ℕ), ∀ s < (4 : ℕ), ∀ t < (4 : ℕ), s < t → get x (i + s) + get x (i + t) ≠ n)

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X) ^ 4 : PowerSeries ℚ) = 2 * X * (1 + 7 * X + 115 * X ^ 2 + 251 * X ^ 3 + 1161 * X ^ 4 + 1045 * X ^ 5 + 2001 * X ^ 6 + 617 * X ^ 7 + 562 * X ^ 8)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = -20 * (n : ℚ) + 43 * (n : ℚ) ^ 2 - 40 * (n : ℚ) ^ 3 + 21 * (n : ℚ) ^ 4 - 6 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -26 + 37 * (n : ℚ) + 5 * (n : ℚ) ^ 2 - 30 * (n : ℚ) ^ 3 + 21 * (n : ℚ) ^ 4 - 6 * (n : ℚ) ^ 5 + (n : ℚ) ^ 6) := by
  sorry

end OMA.S_oeis_a246482
