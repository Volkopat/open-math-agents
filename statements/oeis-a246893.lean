import Mathlib

/-!
# A246893: Number of length 1+4 0..n arrays with some pair in every consecutive five terms totalling exactly n.

Source: https://oeis.org/A246893
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(30 + 171*x + 378*x^2 + 619*x^3 + 394*x^4 + 329*x^5 - 2*x^6 + x^7) / ((1 - x)^5*(1 + x)^3).
* a(n) = 1 - 5*n + 30*n^2 - 5*n^3 + 10*n^4 for n even.
* a(n) = -15 + 20*n + 20*n^2 - 5*n^3 + 10*n^4 for n odd.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_4) of length 5 with entries in 0..n such that every 5 consecutive entries contain two (at different positions) summing to exactly n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 31).
-/

namespace OMA.S_oeis_a246893

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 5 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 5 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 5 consecutive entries contain two (at different positions) summing to exactly n. -/
def good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Bool :=
  decide (∀ i < (1 : ℕ), ∃ s < (5 : ℕ), ∃ t < (5 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n)

/-- The number of arrays of length 5 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (30 + 171 * X + 378 * X ^ 2 + 619 * X ^ 3 + 394 * X ^ 4 + 329 * X ^ 5 - 2 * X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = 1 - 5 * (n : ℚ) + 30 * (n : ℚ) ^ 2 - 5 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = -15 + 20 * (n : ℚ) + 20 * (n : ℚ) ^ 2 - 5 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4) := by
  sorry

end OMA.S_oeis_a246893
