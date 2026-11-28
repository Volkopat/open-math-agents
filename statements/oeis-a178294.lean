import Mathlib

/-!
# A178294: Number of collinear point triples in a 4 X 4 X 4 X... n-dimensional cubic grid

Source: https://oeis.org/A178294
Credit: @xor2k
Sibling of OEIS A178295 (same conjecture wording); statement modelled on the accepted one for that entry.

`a(n)` is the number of collinear point triples in a 4 X 4 X ... n-dimensional cubic grid, i.e. the
number of `3`-element sets of points of `{0, ..., 3}^n` that lie on a common line (offset 0). The
entry records a conjecture of R. J. Mathar (May 24 2010):
Conjecture: a(n) = 8^n/2-3*4^n/2+6^n. a(n) = +18*a(n-1) -104*a(n-2) +192*a(n-3).
G.f.: 4*x*(-1+7*x)/((6*x-1)*(8*x-1)*(4*x-1)).

The grid point `p : Fin n → Fin 4` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `3` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `3`-subset of `4` points on a line counts,
giving `a 1 = 4`, and the line-by-line count gives `a 2 = 44` as listed.

`main` states all three parts of the conjecture: the closed form (multiplied by `2` to clear
denominators and read in `ℤ`); the recurrence in `ℤ` for every `n ≥ 3` (all indices `n-3, ..., n`
within the offset); and the generating function identity in `ℚ⟦X⟧`, where the division is
multiplication by the power-series inverse of the denominator (its constant coefficient is `-1`).
-/

namespace OMA.S_oeis_a178294

open PowerSeries

/-- The grid point `p` of `{0, ..., 3}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 4) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `3`-element sets of points of the `4^n` grid (OEIS A178294). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 4) | s.card = 3 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 4)))}.ncard

/-- Mathar's conjectured closed form, recurrence and generating function for OEIS A178294. -/
theorem main :
    (∀ n : ℕ, 2 * (a n : ℤ) = 8 ^ n - 3 * 4 ^ n + 2 * 6 ^ n) ∧
    (∀ n : ℕ, 3 ≤ n →
      (a n : ℤ) = 18 * (a (n - 1) : ℤ) - 104 * (a (n - 2) : ℤ) + 192 * (a (n - 3) : ℤ)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (4 * X * (-1 + 7 * X)) * ((6 * X - 1) * (8 * X - 1) * (4 * X - 1))⁻¹ := by
  sorry

end OMA.S_oeis_a178294
