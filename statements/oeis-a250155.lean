import Mathlib

/-!
# A250155: Number of length 1+6 0..n arrays with every seven consecutive terms having the maximum of some two terms equal to the minimum of the remaining five terms.

Source: https://oeis.org/A250155
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(107 + 703*x + 1243*x^2 + 432*x^3 + 41*x^4 - 7*x^5 + x^6) / (1 - x)^7.
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_6) of length 7 with entries in 0..n such that in every 7 consecutive entries, for some 2 of them (a set S of 2 positions of the window) the maximum over S equals the minimum over the remaining 5.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 24).
-/

namespace OMA.S_oeis_a250155

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 7 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 7 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in every 7 consecutive entries, for some 2 of them (a set S of 2 positions of the window) the maximum over S equals the minimum over the remaining 5. -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Bool :=
  decide (∀ i < (1 : ℕ), ∃ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v))

/-- The number of arrays of length 7 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 7 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) = X * (107 + 703 * X + 1243 * X ^ 2 + 432 * X ^ 3 + 41 * X ^ 4 - 7 * X ^ 5 + X ^ 6)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a250155
