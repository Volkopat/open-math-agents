import Mathlib

/-!
# A249966: Number of length 6+5 0..n arrays with no six consecutive terms having the maximum of any two terms equal to the minimum of the remaining four terms.

Source: https://oeis.org/A249966
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(15 + 4819*x + 208006*x^2 + 2329714*x^3 + 9235434*x^4 + 14869326*x^5 + 10156734*x^6 + 2833778*x^7 + 273635*x^8 + 5339*x^9) / (1 - x)^12.
* a(n) = 12*a(n-1) - 66*a(n-2) + 220*a(n-3) - 495*a(n-4) + 792*a(n-5) - 924*a(n-6) + 792*a(n-7) - 495*a(n-8) + 220*a(n-9) - 66*a(n-10) + 12*a(n-11) - a(n-12) for n>12.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_10) of length 11 with entries in 0..n such that in no 6 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 4.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 17).
-/

namespace OMA.S_oeis_a249966

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 11 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 11 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 6 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 4. -/
def good {n : ℕ} (x : Fin 11 → Fin (n + 1)) : Bool :=
  decide (∀ i < (6 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 11 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 11 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 12 : PowerSeries ℚ) = X * (15 + 4819 * X + 208006 * X ^ 2 + 2329714 * X ^ 3 + 9235434 * X ^ 4 + 14869326 * X ^ 5 + 10156734 * X ^ 6 + 2833778 * X ^ 7 + 273635 * X ^ 8 + 5339 * X ^ 9)) ∧
    (∀ n : ℕ, 13 ≤ n → (a n : ℚ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12)) := by
  sorry

end OMA.S_oeis_a249966
