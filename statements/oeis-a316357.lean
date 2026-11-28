import Mathlib

/-!
# The partial sums of the coordination sequence of the chamfered square grid

Source: https://oeis.org/A316357 and https://oeis.org/A316316
Credit: @etaubman

The shell counts below use the twelve positive-index initial values and
N. J. A. Sloane's 2018 coloring-book theorem that shifting a positive index
by twelve increases the count by forty. We prove both of Colin Barker's
December 2018 conjectures for their partial sums. The power-series identity
is written after multiplication by its denominator, which has constant
coefficient one.
-/

namespace OMA.S_oeis_a316357

/-- The coordination sequence A316316 at positive index n+1. -/
def shell : ℕ → ℤ
  | 0 => 4
  | 1 => 8
  | 2 => 8
  | 3 => 12
  | 4 => 20
  | 5 => 20
  | 6 => 20
  | 7 => 28
  | 8 => 32
  | 9 => 32
  | 10 => 36
  | 11 => 40
  | n + 12 => shell n + 40

/-- A316357. The coordination sequence has one vertex at radius zero. -/
def total : ℕ → ℤ
  | 0 => 1
  | n + 1 => total n + shell n

open PowerSeries

theorem main :
    (∀ n : ℕ, total (n+7) = 2*total (n+6) - 2*total (n+5) +
      3*total (n+4) - 3*total (n+3) + 2*total (n+2) - 2*total (n+1) + total n) ∧
    (1 - X)^3 * (1 + X^2) * (1 + X + X^2) * mk total =
      (1 + 3*X + 5*X^2 + 2*X^3 + 5*X^4 + 3*X^5 + X^6 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a316357
