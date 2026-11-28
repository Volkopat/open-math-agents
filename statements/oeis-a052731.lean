import Mathlib

/-!
# A052731: factorial-scaled first differences of Motzkin numbers

Mathar's formula says that the exponential generating series of A052731
is the ordinary generating series of A002026 shifted by two degrees.
The factors `n!` cancel in the exponential coefficients. Degrees zero
and one are both zero in the source. The square root is the formal branch
with constant coefficient one. The equation is multiplied by `2 * X`.

Sources
- https://oeis.org/A052731
- https://oeis.org/A002026
- https://oeis.org/A001006
-/

namespace OMA.S_oeis_a052731

open Finset PowerSeries

def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => motzkin (n + 1) + ∑ i : Fin (n + 1), motzkin i * motzkin (n - i)

noncomputable def expectedSeries : PowerSeries ℚ :=
  X ^ 2 * PowerSeries.mk (fun n => (motzkin (n + 1) : ℚ) - (motzkin n : ℚ))

theorem main : ∃ root : PowerSeries ℚ,
    constantCoeff root = 1 ∧ root ^ 2 = 1 - C 2 * X - C 3 * X ^ 2 ∧
      C 2 * X * expectedSeries = 1 - X - root - X * (1 + X - root) := by
  sorry

end OMA.S_oeis_a052731
