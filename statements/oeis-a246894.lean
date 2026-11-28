import Mathlib

/-!
# A246894: Number of length 2+4 0..n arrays with some pair in every consecutive five terms totalling exactly n.

Source: https://oeis.org/A246894
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(58 + 557*x + 1844*x^2 + 4198*x^3 + 3740*x^4 + 2876*x^5 - 268*x^6 - 1486*x^7 + 2*x^8 - x^9) / ((1 - x)^6*(1 + x)^4).
* a(n) = 1 - 72*n + 146*n^2 - 57*n^3 + 31*n^4 + 6*n^5 for n even.
* a(n) = -101 + 84*n + 99*n^2 - 61*n^3 + 31*n^4 + 6*n^5 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that every 5 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a246894

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 5 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (2 : ℕ), ∃ s < (5 : ℕ), ∃ t < (5 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 4 : PowerSeries ℚ) = X * (58 + 557 * X + 1844 * X ^ 2 + 4198 * X ^ 3 + 3740 * X ^ 4 + 2876 * X ^ 5 - 268 * X ^ 6 - 1486 * X ^ 7 + 2 * X ^ 8 - X ^ 9)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 - 72 * (n : ℚ) + 146 * (n : ℚ) ^ 2 - 57 * (n : ℚ) ^ 3 + 31 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -101 + 84 * (n : ℚ) + 99 * (n : ℚ) ^ 2 - 61 * (n : ℚ) ^ 3 + 31 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 5) := by
  sorry

end OMA.S_oeis_a246894
