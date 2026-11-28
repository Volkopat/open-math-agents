import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Int

/-!
# The unsigned projection difference, OEIS A340507

The input point on the nth upward antidiagonal enumeration is (x,y), with
row = A003056(n), y = A002262(n) = n − row(row+1)/2, and x = A025581(n) = row−y.
Here the enumeration index n starts at zero. Within the row, y starts at zero.

A072785 is A072781 − A072738. These two entries take the first coordinate
after applying respectively the variant triangle-stretching map A072734 and
the original map A072732. The definitions below keep the first coordinate
from the corresponding Scheme programs before Cantor packing. Integer
division and remainder by 2 agree with Scheme floor and modulo.

Sources: https://oeis.org/A340507, https://oeis.org/A072785,
https://oeis.org/A072734, https://oeis.org/A072732
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a340507

/-- The index of the row in the triangular enumeration, OEIS A003056. -/
def row (n : ℕ) : ℕ := ((8*n+1).sqrt-1)/2

def pointY (n : ℕ) : ℕ := n - row n * (row n + 1) / 2

def pointX (n : ℕ) : ℕ := row n - pointY n

/-- First coordinate in the original stretching map A072732. -/
def originalX (x y : ℤ) : ℤ :=
  let d := x-y
  if d ≤ 0 then 2*x + d%2 else 2*(1+y) + (d-2)/2

/-- First coordinate in the variant stretching map A072734. -/
def variantX (x y : ℤ) : ℤ :=
  let d := x-y
  if d < 0 then 2*x + (1+d)%2
  else if d < 3 then 2*y+d else 2*y + (1+d)/2 + (1+d)%2

/-- The projection difference A072785(n), signed as in its definition. -/
def difference (n : ℕ) : ℤ :=
  variantX (pointX n) (pointY n) - originalX (pointX n) (pointY n)

theorem main : ∀ n : ℕ, ((2*n).sqrt : ℤ) - (row n : ℤ) = |difference n| := by
  sorry

end OMA.S_oeis_a340507
