import Mathlib

/-!
# A249961: Number of length 1+5 0..n arrays with no six consecutive terms having the maximum of any two terms equal to the minimum of the remaining four terms.

Source: https://oeis.org/A249961
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 15*x*(1 + x)^2*(1 + 10*x + x^2) / (1 - x)^7.
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_5) of length 6 with entries in 0..n such that in no 6 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 4.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a249961

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 6 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 4. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (1 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 6 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 7 : PowerSeries ℚ) = 15 * X * (1 + X) ^ 2 * (1 + 10 * X + X ^ 2)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a249961
