import Mathlib

/-!
# A249712: Number of length 6+3 0..n arrays with every four consecutive terms having the maximum of some two terms equal to the minimum of the remaining two terms.

Source: https://oeis.org/A249712
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(52 + 295*x - 81*x^2 - 136*x^3 + 20*x^4 - 7*x^5 + x^6) / (1 - x)^7.
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_8) of length 9 with entries in 0..n such that in every 4 consecutive entries, for some 2 of them (a set S of 2 positions of the window) the maximum over S equals the minimum over the remaining 2.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a249712

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 9 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in every 4 consecutive entries, for some 2 of them (a set S of 2 positions of the window) the maximum over S equals the minimum over the remaining 2. -/
def good {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Bool :=
  decide (∀ i < (6 : ℕ), ∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v))

/-- The number of arrays of length 9 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) = X * (52 + 295 * X - 81 * X ^ 2 - 136 * X ^ 3 + 20 * X ^ 4 - 7 * X ^ 5 + X ^ 6)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a249712
