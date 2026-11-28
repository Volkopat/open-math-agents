import Mathlib

/-!
# A245874: Number of length 5+2 0..n arrays with some pair in every consecutive three terms totalling exactly n.

Source: https://oeis.org/A245874
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(42 + 469*x + 574*x^2 + 371*x^3 + 10*x^4 - 121*x^5 - 2*x^6 + x^7) / ((1 - x)^5*(1 + x)^3).
* a(n) = 1 + 12*n + 26*n^2 + 39*n^3 + 7*n^4 for n even.
* a(n) = -9 - 18*n + 23*n^2 + 39*n^3 + 7*n^4 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_6) of length 7 with entries in 0..n such that every 3 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 30).
-/

namespace OMA.S_oeis_a245874

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 7 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 7 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 3 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Bool :=
  decide (∀ i < (5 : ℕ), ∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 7 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 7 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (42 + 469 * X + 574 * X ^ 2 + 371 * X ^ 3 + 10 * X ^ 4 - 121 * X ^ 5 - 2 * X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 12 * (n : ℚ) + 26 * (n : ℚ) ^ 2 + 39 * (n : ℚ) ^ 3 + 7 * (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -9 - 18 * (n : ℚ) + 23 * (n : ℚ) ^ 2 + 39 * (n : ℚ) ^ 3 + 7 * (n : ℚ) ^ 4) := by
  sorry

end OMA.S_oeis_a245874
