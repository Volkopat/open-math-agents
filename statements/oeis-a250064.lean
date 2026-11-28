import Mathlib

/-!
# A250064: Number of length 4+6 0..n arrays with no seven consecutive terms having the maximum of any two terms equal to the minimum of the remaining five terms.

Source: https://oeis.org/A250064
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(21 + 3799*x + 88879*x^2 + 565631*x^3 + 1296585*x^4 + 1192749*x^5 + 430621*x^6 + 49661*x^7 + 854*x^8) / (1 - x)^11.
* a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>11.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_9) of length 10 with entries in 0..n such that in no 7 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 5.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 18).
-/

namespace OMA.S_oeis_a250064

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 10 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 10 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 7 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 5. -/
def good {n : ℕ} (x : Fin 10 → Fin (n + 1)) : Bool :=
  decide (∀ i < (4 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 7)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 10 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 10 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 11 : PowerSeries ℚ) = X * (21 + 3799 * X + 88879 * X ^ 2 + 565631 * X ^ 3 + 1296585 * X ^ 4 + 1192749 * X ^ 5 + 430621 * X ^ 6 + 49661 * X ^ 7 + 854 * X ^ 8)) ∧
    (∀ n : ℕ, 12 ≤ n → (a n : ℚ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11)) := by
  sorry

end OMA.S_oeis_a250064
