import Mathlib

/-!
# A254703: Number of length 5+4 0..n arrays with every five consecutive terms having the maximum of some two terms equal to the minimum of the remaining three terms.

Source: https://oeis.org/A254703
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(136 + 1222*x + 1604*x^2 - 873*x^3 - 204*x^4 - 20*x^5 + 8*x^6 - x^7) / (1 - x)^8.
* a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_8) of length 9 with entries in 0..n such that in every 5 consecutive entries, for some 2 of them (a set S of 2 positions of the window) the maximum over S equals the minimum over the remaining 3.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 23).
-/

namespace OMA.S_oeis_a254703

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 9 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in every 5 consecutive entries, for some 2 of them (a set S of 2 positions of the window) the maximum over S equals the minimum over the remaining 3. -/
def good {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Bool :=
  decide (∀ i < (5 : ℕ), ∃ S ∈ (Finset.univ : Finset (Fin 5)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v))

/-- The number of arrays of length 9 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = X * (136 + 1222 * X + 1604 * X ^ 2 - 873 * X ^ 3 - 204 * X ^ 4 - 20 * X ^ 5 + 8 * X ^ 6 - X ^ 7)) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a254703
