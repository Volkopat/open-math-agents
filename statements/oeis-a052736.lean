import Mathlib

/-!
# A052736: factorial scaling of royal path numbers

This states Mathar's identity with the full range in which the index `n - 1`
is defined, starting at `n = 1`. In an exponential generating series,
the factor `n!` cancels and this becomes `X` times the ordinary generating
series of A006319. The square root is the formal branch with constant
coefficient one. Multiplication by two clears the displayed denominator.

A006319 gives its ordinary generating function as `(1 - X)` times the
series for the large Schröder numbers A006318, whose recurrence is used here.
The source tables differ at `n = 1`: A052736(1) is zero and A006319(0) is one.

Sources
- https://oeis.org/A052736
- https://oeis.org/A006319
- https://oeis.org/A006318
-/

namespace OMA.S_oeis_a052736

open Finset PowerSeries

def largeSchroeder : ℕ → ℕ
  | 0 => 1
  | n + 1 => largeSchroeder n + ∑ i : Fin (n + 1), largeSchroeder i * largeSchroeder (n - i)

noncomputable def royalSeries : PowerSeries ℚ :=
  (1 - X) * PowerSeries.mk (fun n => (largeSchroeder n : ℚ))

theorem main : ∃ root : PowerSeries ℚ,
    constantCoeff root = 1 ∧ root ^ 2 = 1 - C 6 * X + X ^ 2 ∧
      C 2 * X * royalSeries = 1 - C 3 * X - root - X * (1 - X - root) := by
  sorry

end OMA.S_oeis_a052736
