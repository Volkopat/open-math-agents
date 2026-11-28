import Mathlib

/-!
# A250393: Number of length 7+3 0..n arrays with no four consecutive terms having the maximum of any two terms equal to the minimum of the remaining two terms.

Source: https://oeis.org/A250393
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: 2*x*(3 + 875*x + 27441*x^2 + 220687*x^3 + 609695*x^4 + 647425*x^5 + 267419*x^6 + 39317*x^7 + 1538*x^8) / (1 - x)^11.
* a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>11.

Conventions: length P+Q in the name is the array length P + Q; windows are runs of consecutive positions; this reading reproduces the OEIS data.
Offset 1: a(n) is the number of arrays (x_0, ..., x_9) of length 10 with entries in 0..n such that in no 4 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 2.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 19).
-/

namespace OMA.S_oeis_a250393

/-- The entry of `x` at position `k` (`0` past the end). -/
def get {n : ℕ} (x : Fin 10 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 10 then (x ⟨k, h⟩ : ℕ) else 0

/-- The window condition: in no 4 consecutive entries is there a set S of 2 positions of the window such that the maximum over S equals the minimum over the remaining 2. -/
def good {n : ℕ} (x : Fin 10 → Fin (n + 1)) : Bool :=
  decide (∀ i < (7 : ℕ), ¬ (∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1, (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧ (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v)))

/-- The number of arrays of length 10 with entries in `0..n` satisfying the window condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 10 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 11 : PowerSeries ℚ) = 2 * X * (3 + 875 * X + 27441 * X ^ 2 + 220687 * X ^ 3 + 609695 * X ^ 4 + 647425 * X ^ 5 + 267419 * X ^ 6 + 39317 * X ^ 7 + 1538 * X ^ 8)) ∧
    (∀ n : ℕ, 12 ≤ n → (a n : ℚ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11)) := by
  sorry

end OMA.S_oeis_a250393
