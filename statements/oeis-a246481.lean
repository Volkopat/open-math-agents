import Mathlib

/-!
# A246481: Number of length 2+3 0..n arrays with no pair in any consecutive four terms totalling exactly n.

Source: https://oeis.org/A246481
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(1 + 4*x + 45*x^2 + 52*x^3 + 191*x^4 + 72*x^5 + 115*x^6) / ((1 - x)^6*(1 + x)^3).
* a(n) = 5*n - 11*n^2 + 10*n^3 - 4*n^4 + n^5 for n even.
* a(n) = 9 - 10*n - 4*n^2 + 10*n^3 - 4*n^4 + n^5 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_4) of length 5 with entries in 0..n such that no 4 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 30).
-/

namespace OMA.S_oeis_a246481

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 5 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 5 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: no 4 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Bool :=
  decide (∀ i < (2 : ℕ), ∀ s < (4 : ℕ), ∀ t < (4 : ℕ), s < t → get x (i + s) + get x (i + t) ≠ n)

/-- The number of arrays of length 5 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3 : PowerSeries ℚ) = 2 * X * (1 + 4 * X + 45 * X ^ 2 + 52 * X ^ 3 + 191 * X ^ 4 + 72 * X ^ 5 + 115 * X ^ 6)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 5 * (n : ℚ) - 11 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = 9 - 10 * (n : ℚ) - 4 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5) := by
  sorry

end OMA.S_oeis_a246481
