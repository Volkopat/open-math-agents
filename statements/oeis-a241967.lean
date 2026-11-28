import Mathlib

/-!
# A241967: Number of length 4+3 0..n arrays with no consecutive four elements summing to more than 2*n.

Source: https://oeis.org/A241967
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(57 + 319*x + 607*x^2 + 140*x^3 + 70*x^4 - 28*x^5 + 8*x^6 - x^7) / (1 - x)^8.
* a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_6) of length 7 with entries in 0..n such that every 4 consecutive entries sum to at most 2 * n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 24).
-/

namespace OMA.S_oeis_a241967

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 7 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 7 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 4 consecutive entries sum to at most 2 * n. -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Bool :=
  decide (∀ i < (4 : ℕ), (∑ t ∈ Finset.range 4, get x (i + t)) ≤ 2 * n)

/-- The number of arrays of length 7 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 7 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = X * (57 + 319 * X + 607 * X ^ 2 + 140 * X ^ 3 + 70 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7)) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a241967
