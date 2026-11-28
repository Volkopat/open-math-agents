import Mathlib

/-!
# A153367: Barker's closed form and recurrence for zig-zag paths of width 9

Source: https://oeis.org/A153367
Credit: @ivillar

The number of zig-zag paths from top to bottom of a rectangle of width 9 with 2n-1 rows whose
color is not that of the top right corner (offset 1; data 4, 14, 50, 180, 650, 2350, 8500, ...).
Colin Barker conjectured (Feb 11 2018)
a(n) = (2^(-n)*((5-sqrt(5))^n*(-5+3*sqrt(5)) + (5+sqrt(5))^n*(5+3*sqrt(5)))) / (5*sqrt(5))
for n > 0, and a(n) = 5*a(n-1) - 5*a(n-2) for n > 2 (his earlier empirical g.f. is
x*(4-6*x)/(1-5*x+5*x^2), Jan 04 2012).

Status: open conjecture (Colin Barker, Feb 11 2018).

Formalization notes:
* The rectangle has rows 0, ..., 2n-2 (top to bottom) and columns 0, ..., 8 (left to right),
  colored like a chessboard: cell (i, c) has color (i + c) mod 2, so the top right corner (0, 8)
  has color 0. A zig-zag path visits one cell `(i, p i)` in every row `i`, and the cells of
  consecutive rows are in adjacent columns (as in A153362: words over a 9-letter alphabet in
  which neighboring letters are neighbors in the alphabet). Its cells all have the same color;
  `a n` counts the paths all of whose cells have color 1, i.e. not the color of the top right
  corner.
* The closed form is stated over ℝ exactly as written, with 2^(-n) as `((2 : ℝ) ^ n)⁻¹`; the
  recurrence is stated over ℤ.
* Ehren Metcalfe's consequences a(2n) = 2*5^(n-1)*Lucas(2(n+1)), a(2n+1) = 2*5^n*Fibonacci(2n+3)
  (stated assuming Barker's conjectures) are not restated.
-/

namespace OMA.S_oeis_a153367

/-- A153367: the zig-zag paths `p : Fin (2n-1) → Fin 9` (row `i` ↦ column `p i`) of the width-9
rectangle with `2n-1` rows, all of whose cells `(i, p i)` have color `(i + p i) mod 2 = 1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin (2 * n - 1) → Fin 9 =>
    (∀ i j : Fin (2 * n - 1), j.val = i.val + 1 →
      (p i).val = (p j).val + 1 ∨ (p j).val = (p i).val + 1) ∧
    ∀ i : Fin (2 * n - 1), (i.val + (p i).val) % 2 = 1).card

/-- Barker's conjectured closed form (for `n > 0`) and recurrence (for `n > 2`) for A153367. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℝ) =
      ((2 : ℝ) ^ n)⁻¹ * ((5 - Real.sqrt 5) ^ n * (-5 + 3 * Real.sqrt 5) +
        (5 + Real.sqrt 5) ^ n * (5 + 3 * Real.sqrt 5)) / (5 * Real.sqrt 5)) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 5 * a (n - 1) - 5 * a (n - 2)) := by
  sorry

end OMA.S_oeis_a153367
