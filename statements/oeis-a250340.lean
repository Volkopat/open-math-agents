import Mathlib

/-!
# A250340: Number of length 4+5 0..n arrays with every six consecutive terms having the maximum of some three terms equal to the minimum of the remaining three terms.

Source: https://oeis.org/A250340
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(172 + 2861*x + 4335*x^2 - 2703*x^3 - 2357*x^4 + 227*x^5 + 65*x^6 - 9*x^7 + x^8) / (1 - x)^9.
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_8) of length 9 with entries in 0..n such that in every 6 consecutive entries, for some 3 of them (a set S of 3 positions of the window) the maximum over S equals the minimum over the remaining 3.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 23).
-/

namespace OMA.S_oeis_a250340

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 9 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in every 6 consecutive entries, for some 3 of them (a set S of 3 positions of the window) the maximum over S equals the minimum over the remaining 3. -/
def good {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Bool :=
  decide (∀ i < (4 : ℕ), ∃ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v))

/-- The number of arrays of length 9 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) = X * (172 + 2861 * X + 4335 * X ^ 2 - 2703 * X ^ 3 - 2357 * X ^ 4 + 227 * X ^ 5 + 65 * X ^ 6 - 9 * X ^ 7 + X ^ 8)) ∧
    (∀ n : ℕ, 10 ≤ n → (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a250340
