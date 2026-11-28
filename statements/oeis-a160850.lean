import Mathlib

/-!
# Lines through an 10-row rectangular grid (A160850)

Source: https://oeis.org/A160850
Credit: @physbuzz

We use the grid-line counting algorithm in the entry's Mathematica program.
For a primitive direction with positive displacements x and y, the number of
lines is the number of placements of a segment minus the number of placements
of a double segment. Taking second differences in the column count gives
height 10-y when x=n-1, less the positive part of 10-2y when 2x=n-1.
The factor two counts both signs of the slope. Horizontal and vertical lines
have zero second difference from n=4 on. The first four counts include them.
The offset is zero. Barker's conjectures give the series and the recurrence
for n>21.
-/

namespace OMA.S_oeis_a160850
open PowerSeries

def secondDiff (t : ℕ) : ℤ :=
  2 * ∑ i : Fin 9, (let y := i.val + 1
    (if Nat.Coprime y (t % y) then ((10-y : ℕ) : ℤ) else 0) -
    (if t % 2 = 0 ∧ Nat.Coprime y ((t/2) % y) then ((10-2*y : ℕ) : ℤ) else 0))

/-- The pair at k contains the counts for k+2 and k+3 columns. -/
def counts : ℕ → ℤ × ℤ
  | 0 => (102,203)
  | k+1 => let p := counts k
           (p.2, 2*p.2-p.1+secondDiff (k+3))

def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k+2 => (counts k).1

theorem main :
    mk a * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6)) = X*(1 + 102*X + 204*X^2 + 472*X^3 + 766*X^4 + 1205*X^5 + 1571*X^6 + 1999*X^7 + 2188*X^8 + 2334*X^9 + 2168*X^10 + 1959*X^11 + 1531*X^12 + 1165*X^13 + 746*X^14 + 462*X^15 + 214*X^16 + 112*X^17 + 21*X^18 + 10*X^19 + 10*X^20) ∧
    ∀ n : ℕ, 21 < n → a n = - a (n-2) + a (n-5) + a (n-6) + 2*a (n-7) + a (n-8) + a (n-9) - a (n-11) - a (n-12) - 2*a (n-13) - a (n-14) - a (n-15) + a (n-18) + a (n-20) := by
  sorry
end OMA.S_oeis_a160850
