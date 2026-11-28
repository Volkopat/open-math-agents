import Mathlib

/-!
# Mathar's conjecture on sums of central-factorial triangle rows

A008956 lists the absolute scaled central factorial numbers. Meijer's
published entry recurrence generates the triangle from row zero [1].
Mathar conjectured that row n sums to the absolute value of term n+1
of A101927, whose terms are the odd exponential coefficients of
sin(arcsinh(x)) with offset one. Slattery's 2022 product formula for
those absolute values gives the independent target below. At row zero
the empty product equals the first term, one.
Sources: https://oeis.org/A008956 and https://oeis.org/A101927
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a008956
open Finset

def entry : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => (2*n+1)^2*entry n k + entry n (k+1)

def absOddCoefficient (n : ℕ) : ℕ :=
  ∏ j ∈ range n, ((2*j+1)^2+1)

theorem main : ∀ n : ℕ, ∑ k ∈ range (n+1), entry n k = absOddCoefficient n := by
  sorry

end OMA.S_oeis_a008956
