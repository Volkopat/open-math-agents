import Mathlib

/-!
# A241622: Number of length 7+2 0..n arrays with no consecutive three elements summing to more than n.

Source: https://oeis.org/A241622
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(41 + 146*x + 460*x^2 - 19*x^3 + 283*x^4 - 209*x^5 + 120*x^6 - 45*x^7 + 10*x^8 - x^9) / (1 - x)^10.
* a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_8) of length 9 with entries in 0..n such that every 3 consecutive entries sum to at most 1 * n.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 24).
-/

namespace OMA.S_oeis_a241622

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 9 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: every 3 consecutive entries sum to at most 1 * n. -/
def good {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Bool :=
  decide (∀ i < (7 : ℕ), (∑ t ∈ Finset.range 3, get x (i + t)) ≤ 1 * n)

/-- The number of arrays of length 9 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) = X * (41 + 146 * X + 460 * X ^ 2 - 19 * X ^ 3 + 283 * X ^ 4 - 209 * X ^ 5 + 120 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9)) ∧
    (∀ n : ℕ, 11 ≤ n → (a n : ℚ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10)) := by
  sorry

end OMA.S_oeis_a241622
