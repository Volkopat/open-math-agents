import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The generating function and recurrence for OEIS A200431

R. H. Hardin counts ordered quadruples of integers from `-n` through `n`
with total zero and with nonzero sum on each consecutive pair and triple.
Colin Barker conjectured both formulas below on 20 May 2018.

OEIS indexes the sequence from 1. At index 0 the same counting rule gives
zero, the constant coefficient of the generating function. Its denominator
has constant coefficient 1, so we state the identity after multiplication.

Source: https://oeis.org/A200431
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a200431

/-- All ordered quadruples satisfying the conditions in the OEIS definition. -/
def quadruples (n : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  let box := Finset.Icc (-(n : ℤ)) (n : ℤ)
  (box ×ˢ (box ×ˢ (box ×ˢ box))).filter fun ⟨a, b, c, d⟩ =>
    a + b + c + d = 0 ∧
    a + b ≠ 0 ∧ b + c ≠ 0 ∧ c + d ≠ 0 ∧
    a + b + c ≠ 0 ∧ b + c + d ≠ 0

/-- The cardinality as an integer, for the signed recurrence. -/
def a (n : ℕ) : ℤ := (quadruples n).card

open PowerSeries

theorem main :
    mk a * (1 - X)^4 = 4 * X^2 * (5 + 3 * X) ∧
    ∀ n : ℕ, 4 < n →
      a n = 4 * a (n-1) - 6 * a (n-2) + 4 * a (n-3) - a (n-4) := by
  sorry

end OMA.S_oeis_a200431
