import Mathlib

/-!
# A096222: Number of different rectangles when a piece of paper is folded n times in alternate directions.

Source: https://oeis.org/A096222 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A096222 (Bill Liebeskind, Jul 29 2004), offset 0. The entry's comment fixes the model:
"In this sequence we count the rectangles in an a X b array of squares, where a=2^floor(n/2)
and b=2^ceiling(n/2)." Formula section, verbatim:
Conjectures from Colin Barker, Feb 04 2020:
G.f.: (1 - 3*x - 9*x^2 + 24*x^3) / ((1 - 2*x)*(1 - 4*x)*(1 - 8*x^2)).
a(n) = 6*a(n-1) - 48*a(n-3) + 64*a(n-4) for n>3.

Formalization notes:
* Folding a sheet n times in alternate directions creates a grid of p X q unit squares with
  p = 2^floor(n/2) and q = 2^ceiling(n/2), as in the entry's comment; ceiling(n/2) is written
  (n + 1) / 2 and floor(n/2) is n / 2 (natural-number division).
* A rectangle of the p X q array of squares (a union of squares forming a rectangle) is
  determined by two distinct horizontal grid lines out of the p + 1 lines and two distinct
  vertical grid lines out of the q + 1 lines; `rectCount p q` counts these choices as pairs of
  2-element subsets. (This reproduces the entry's formula a(n) = a*b*(a+1)*(b+1)/4.)
* The statement is the conjunction of the two conjectures, on the range the entry gives
  (n > 3 for the recurrence). The recurrence is stated in the integers. The generating function
  is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the rationals, and the
  identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives 1, 3, 9, 30, 100, 360, 1296, 4896, 18496 for
  n = 0..8, matching the entry's data.
-/

namespace OMA.S_oeis_a096222

open PowerSeries

/-- The number of rectangles in a `p X q` array of unit squares: a choice of two of the
`p + 1` horizontal grid lines and two of the `q + 1` vertical grid lines. -/
def rectCount (p q : ℕ) : ℕ :=
  ((Finset.range (p + 1)).powersetCard 2 ×ˢ (Finset.range (q + 1)).powersetCard 2).card

/-- A096222(n): rectangles in the `2^floor(n/2) X 2^ceiling(n/2)` array of squares. -/
def a (n : ℕ) : ℕ := rectCount (2 ^ (n / 2)) (2 ^ ((n + 1) / 2))

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's generating function and recurrence for OEIS A096222. -/
theorem main :
    A = (1 - 3 * X - 9 * X ^ 2 + 24 * X ^ 3) * ((1 - 2 * X) * (1 - 4 * X) * (1 - 8 * X ^ 2))⁻¹ ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 6 * a (n - 1) - 48 * a (n - 3) + 64 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a096222
