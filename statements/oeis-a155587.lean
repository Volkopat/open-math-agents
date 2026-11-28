import Mathlib

/-!
# A155587: Mathar's recurrence for the expansion of (1 + x*c(x))/(1 - x)

Source: https://oeis.org/A155587
Credit: @ivillar

A155587 (offset 0) is the expansion of (1 + x*c(x))/(1 - x), where c(x) is the g.f. of the
Catalan numbers A000108; data 1, 2, 3, 5, 10, 24, 66, 198, ...
Conjecture (R. J. Mathar, Nov 15 2011): n*a(n) + (6-5*n)*a(n-1) + 2*(2*n-3)*a(n-2) = 0.
Petros Hadjicostas (Aug 03 2020) gives a proof in the OEIS entry.

Formalization notes.
* c(x) is `PowerSeries.mk` of Mathlib's `catalan`, and 1/(1 - x) is the geometric series
  `PowerSeries.mk (fun _ => 1)`; a(n) is the n-th coefficient of the product in ℤ⟦X⟧.
* The recurrence is stated for every n ≥ 2, i.e. wherever all three terms exist.
-/

namespace OMA.S_oeis_a155587

open PowerSeries

/-- The g.f. of the Catalan numbers A000108. -/
def c : PowerSeries ℤ := PowerSeries.mk (fun k => (catalan k : ℤ))

/-- A155587: the coefficients of (1 + x*c(x))/(1 - x). -/
noncomputable def a (n : ℕ) : ℤ := coeff n ((1 + X * c) * PowerSeries.mk (fun _ => (1 : ℤ)))

/-- Mathar's recurrence, for every n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * a n + (6 - 5 * (n : ℤ)) * a (n - 1) + 2 * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a155587
