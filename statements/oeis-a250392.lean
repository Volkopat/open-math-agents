import Mathlib

/-!
# A250392: Number of length 6+3 0..n arrays with no four consecutive terms having the maximum of any two terms equal to the minimum of the remaining two terms.

Source: https://oeis.org/A250392
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(3 + 453*x + 8594*x^2 + 43211*x^3 + 73495*x^4 + 45443*x^5 + 9692*x^6 + 549*x^7) / (1 - x)^10.
* a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_8) of length 9 with entries in 0..n such that in no 4 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 2.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 20).
-/

namespace OMA.S_oeis_a250392

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 9 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 4 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 2. -/
def good {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Bool :=
  decide (∀ i < (6 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 9 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 9 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) = 2 * X * (3 + 453 * X + 8594 * X ^ 2 + 43211 * X ^ 3 + 73495 * X ^ 4 + 45443 * X ^ 5 + 9692 * X ^ 6 + 549 * X ^ 7)) ∧
    (∀ n : ℕ, 11 ≤ n → (a n : ℚ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10)) := by
  sorry

end OMA.S_oeis_a250392
