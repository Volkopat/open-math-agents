import Mathlib

/-!
# Singular points on Chmutov surfaces (OEIS A057870)

Source: https://oeis.org/A057870
Credit: @physbuzz

The sequence is the number of singular points on the degree-n Chmutov surface,
starting at degree 1. We use Chmutov's 1992 count by residue class, given in
equation (6) at https://mathworld.wolfram.com/ChmutovSurface.html, the formula
referenced by the entry's author. Its value at zero is zero, as required for
the generating series with offset 1.

Colin Barker's two conjectures of January 2, 2020 concern the generating
function of these counts and a recurrence valid for n > 13.
-/

namespace OMA.S_oeis_a057870

open PowerSeries

def a (n : ℕ) : ℚ :=
  let d : ℚ := n
  (match n % 6 with
  | 0 => 5*d^3 - 13*d^2 + 12*d
  | 2 | 4 => 5*d^3 - 13*d^2 + 16*d - 8
  | 3 => 5*d^3 - 14*d^2 + 9*d
  | _ => 5*d^3 - 14*d^2 + 13*d - 4) / 12

theorem main :
    mk a * ((1-X)^4*(1+X)^3*(1-X+X^2)*(1+X+X^2)^2) =
      X^2*(1+3*X+12*X^2+21*X^3+27*X^4+28*X^5+31*X^6+25*X^7+
        18*X^8+11*X^9+3*X^10) ∧
    ∀ n : ℕ, 13 < n →
      a n = 2*a (n-2) + a (n-3) - a (n-4) - 2*a (n-5) + a (n-6) +
        a (n-7) - 2*a (n-8) - a (n-9) + a (n-10) + 2*a (n-11) - a (n-13) := by
  sorry

end OMA.S_oeis_a057870
