import Mathlib

/-!
# A242145: Number of length 1+5 0..n arrays with no consecutive six elements summing to more than 3*n.

Source: https://oeis.org/A242145
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(42 + 141*x + 175*x^2 - 13*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7.
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that every 6 consecutive entries sum to at most 3 * n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a242145

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 6 consecutive entries sum to at most 3 * n. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (1 : ℕ), (∑ t ∈ Finset.range 6, get x (i + t)) ≤ 3 * n)

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) = X * (42 + 141 * X + 175 * X ^ 2 - 13 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a242145
