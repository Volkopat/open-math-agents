import Mathlib.Data.Nat.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Kimberling's row sums and Voznyy's generating function, OEIS A026765

The row recursion is the defining one for A026758. If G is the ordinary row-sum
generating series and Y = 1 + 2 X G, Voznyy's conjectured radical formula is
equivalent to (1 - 2 X) (1 - 5 X²) Y² = (1 + 2 X) (1 - X²). The cleared polynomial factors
have constant term one. The radical quotient minus one has zero constant term,
so division by 2 X shifts coefficients uniquely. Y(0) = 1 selects the square-root branch. This formulation avoids choosing a
square-root function for formal series.

Sources: https://oeis.org/A026758 and https://oeis.org/A026765
Formalization: @VirtualMe64
-/

namespace OMA.S_oeis_a026765

/-- Kimberling's triangle A026758, extended by zero to all integer column indices.
On odd rows the extra diagonal contribution is made on the left half. -/
def triangle : ℕ → ℤ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 1 then 1 else 0
  | n + 2, k => triangle (n + 1) (k - 1) + triangle (n + 1) k +
      (if n % 2 = 1 ∧ 2 * k ≤ (n + 1 : ℕ) then triangle n (k - 1) else 0)

/-- Sum of the values with indices from zero inclusive to m exclusive. -/
def prefixSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => prefixSum f m + f m

/-- Row sums of Kimberling's triangle, OEIS A026765. -/
def rowSum (n : ℕ) : ℕ := prefixSum (fun k => triangle n k) (n + 1)

open PowerSeries

/-- Ordinary generating function of the row sums. -/
def rowGF : PowerSeries ℚ := PowerSeries.mk (fun n => (rowSum n : ℚ))

/-- Voznyy's generating-function conjecture (August 2009), with units cleared. -/
theorem main :
    (1 - 2 * X) * (1 - 5 * X ^ 2) * (1 + 2 * X * rowGF) ^ 2 =
      (1 + 2 * X) * (1 - X ^ 2) := by
  sorry

end OMA.S_oeis_a026765
