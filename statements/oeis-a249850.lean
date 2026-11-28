import Mathlib

/-!
# A249850: Number of length 6+4 0..n arrays with no five consecutive terms having the maximum of any two terms equal to the minimum of the remaining three terms.

Source: https://oeis.org/A249850
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(10 + 2053*x + 58573*x^2 + 451667*x^3 + 1221975*x^4 + 1285419*x^5 + 529155*x^6 + 77117*x^7 + 2831*x^8) / (1 - x)^11.
* a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>11.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_9) of length 10 with entries in 0..n such that in no 5 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 3.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 19).
-/

namespace OMA.S_oeis_a249850

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 10 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 10 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 5 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 3. -/
def good {n : ℕ} (x : Fin 10 → Fin (n + 1)) : Bool :=
  decide (∀ i < (6 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 5)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 10 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 10 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 11 : PowerSeries ℚ) = X * (10 + 2053 * X + 58573 * X ^ 2 + 451667 * X ^ 3 + 1221975 * X ^ 4 + 1285419 * X ^ 5 + 529155 * X ^ 6 + 77117 * X ^ 7 + 2831 * X ^ 8)) ∧
    (∀ n : ℕ, 12 ≤ n → (a n : ℚ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11)) := by
  sorry

end OMA.S_oeis_a249850
