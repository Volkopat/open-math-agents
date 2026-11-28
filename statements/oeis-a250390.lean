import Mathlib

/-!
# A250390: Number of length 4+3 0..n arrays with no four consecutive terms having the maximum of any two terms equal to the minimum of the remaining two terms.

Source: https://oeis.org/A250390
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(3 + 113*x + 680*x^2 + 1107*x^3 + 547*x^4 + 70*x^5) / (1 - x)^8.
* a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_6) of length 7 with entries in 0..n such that in no 4 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 2.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 24).
-/

namespace OMA.S_oeis_a250390

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 7 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 7 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 4 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 2. -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Bool :=
  decide (∀ i < (4 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 7 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 7 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = 2 * X * (3 + 113 * X + 680 * X ^ 2 + 1107 * X ^ 3 + 547 * X ^ 4 + 70 * X ^ 5)) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a250390
