import Mathlib

/-!
# A246480: Number of length 1+3 0..n arrays with no pair in any consecutive four terms totalling exactly n.

Source: https://oeis.org/A246480
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(1 + 2*x + 16*x^2 + 6*x^3 + 23*x^4) / ((1 - x)^5*(1 + x)^2).
* a(n) = -n + 3*n^2 - 2*n^3 + n^4 for n even.
* a(n) = -3 + 3*n + 3*n^2 - 2*n^3 + n^4 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_3) of length 4 with entries in 0..n such that no 4 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 34).
-/

namespace OMA.S_oeis_a246480

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 4 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 4 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: no 4 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 4 → Fin (n + 1)) : Bool :=
  decide (∀ i < (1 : ℕ), ∀ s < (4 : ℕ), ∀ t < (4 : ℕ), s < t → get x (i + s) + get x (i + t) ≠ n)

/-- The number of arrays of length 4 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 4 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 2 : PowerSeries ℚ) = 2 * X * (1 + 2 * X + 16 * X ^ 2 + 6 * X ^ 3 + 23 * X ^ 4)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = -(n : ℚ) + 3 * (n : ℚ) ^ 2 - 2 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -3 + 3 * (n : ℚ) + 3 * (n : ℚ) ^ 2 - 2 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4) := by
  sorry

end OMA.S_oeis_a246480
