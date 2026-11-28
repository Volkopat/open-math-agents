import Mathlib

/-!
# A245876: Number of length 7+2 0..n arrays with some pair in every consecutive three terms totalling exactly n.

Source: https://oeis.org/A245876
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(110 + 2747*x + 5836*x^2 + 8680*x^3 + 3456*x^4 - 2178*x^5 - 1148*x^6 - 224*x^7 + 2*x^8 - x^9) / ((1 - x)^6*(1 + x)^4).
* a(n) = 1 + 37*n + 43*n^2 + 126*n^3 + 89*n^4 + 9*n^5 for n even.
* a(n) = 7 - 76*n - 41*n^2 + 122*n^3 + 89*n^4 + 9*n^5 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_8) of length 9 with entries in 0..n such that every 3 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a245876

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 9 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 3 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Bool :=
  decide (∀ i < (7 : ℕ), ∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 9 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 4 : PowerSeries ℚ) = X * (110 + 2747 * X + 5836 * X ^ 2 + 8680 * X ^ 3 + 3456 * X ^ 4 - 2178 * X ^ 5 - 1148 * X ^ 6 - 224 * X ^ 7 + 2 * X ^ 8 - X ^ 9)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 37 * (n : ℚ) + 43 * (n : ℚ) ^ 2 + 126 * (n : ℚ) ^ 3 + 89 * (n : ℚ) ^ 4 + 9 * (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 7 - 76 * (n : ℚ) - 41 * (n : ℚ) ^ 2 + 122 * (n : ℚ) ^ 3 + 89 * (n : ℚ) ^ 4 + 9 * (n : ℚ) ^ 5) := by
  sorry

end OMA.S_oeis_a245876
