import Mathlib

/-!
# A249885: Number of length 2+6 0..n arrays with no seven consecutive terms having the maximum of any three terms equal to the minimum of the remaining four terms.

Source: https://oeis.org/A249885
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 5*x*(7 + 210*x + 1473*x^2 + 3340*x^3 + 2457*x^4 + 546*x^5 + 31*x^6) / (1 - x)^9.
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_7) of length 8 with entries in 0..n such that in no 7 consecutive entries is there a set S of 3 positions of the window such that the maximum over S equals the minimum over the remaining 4.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 22).
-/

namespace OMA.S_oeis_a249885

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 8 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 7 consecutive entries is there a set S of 3 positions of the window such that the maximum over S equals the minimum over the remaining 4. -/
def good {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Bool :=
  decide (∀ i < (2 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 8 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 8 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) = 5 * X * (7 + 210 * X + 1473 * X ^ 2 + 3340 * X ^ 3 + 2457 * X ^ 4 + 546 * X ^ 5 + 31 * X ^ 6)) ∧
    (∀ n : ℕ, 10 ≤ n → (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a249885
