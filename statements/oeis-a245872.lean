import Mathlib

/-!
# A245872: Number of length 3+2 0..n arrays with some pair in every consecutive three terms totalling exactly n.

Source: https://oeis.org/A245872
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(16 + 71*x + 34*x^2 - 2*x^3 + 2*x^4 - x^5) / ((1 - x)^4*(1 + x)^2).
* a(n) = 1 + 5*n + 13*n^2 + 5*n^3 for n even.
* a(n) = -5 + 3*n + 13*n^2 + 5*n^3 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_4) of length 5 with entries in 0..n such that every 3 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 36).
-/

namespace OMA.S_oeis_a245872

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 5 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 5 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 3 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Bool :=
  decide (∀ i < (3 : ℕ), ∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 5 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 2 : PowerSeries ℚ) = X * (16 + 71 * X + 34 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 - X ^ 5)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 + 5 * (n : ℚ) + 13 * (n : ℚ) ^ 2 + 5 * (n : ℚ) ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -5 + 3 * (n : ℚ) + 13 * (n : ℚ) ^ 2 + 5 * (n : ℚ) ^ 3) := by
  sorry

end OMA.S_oeis_a245872
