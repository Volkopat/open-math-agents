import Mathlib

/-!
# A359087: Apex of a reverse pyramid

Source: https://oeis.org/A359087
Related sequence: https://oeis.org/A132894
The two conjectures of Bernard Schott and Robert Israel are Theorem 53 and
Corollary 54 of Sela Fried, https://arxiv.org/abs/2607.24832.

The reverse pyramid of order `n` begins with the row
`1, 2, …, n-1, n, n-1, …, 2, 1` and replaces each interior position by
the sum of its three neighbors including itself. The apex has offset one.

A132894 counts horizontal steps across all length-`m` walks with height increments
`-1, 0, 1` that start at zero and never go below zero. We count walks and their
horizontal steps by partitioning them according to their first step.
-/

namespace OMA.S_oeis_a359087

/-- Entry at displacement `i` after `m` sweeps of the order-`n` pyramid.
The intended row has `i.natAbs + m < n`, so extending the base by zeros
outside its support does not affect its entries. -/
def row (n : ℕ) : ℕ → ℤ → ℕ
  | 0, i => n - i.natAbs
  | m + 1, i => row n m (i - 1) + row n m i + row n m (i + 1)

/-- The last remaining entry of the order-`n` reverse pyramid. -/
def a (n : ℕ) : ℕ := row n (n - 1) 0

/-- Number of length-`m` walks starting at height `h` and staying nonnegative. -/
def walks : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, 0 => walks m 0 + walks m 1
  | m + 1, h + 1 => walks m h + walks m (h + 1) + walks m (h + 2)

/-- Total number of horizontal steps over the same family of walks. The horizontal
first step contributes one for each walk in its tail class. -/
def horizontal : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, 0 => horizontal m 0 + horizontal m 1 + walks m 0
  | m + 1, h + 1 => horizontal m h + horizontal m (h + 1) +
      horizontal m (h + 2) + walks m (h + 1)

/-- A132894. -/
def b (m : ℕ) : ℕ := horizontal m 0

open PowerSeries in
/-- Schott's sequence identity and Israel's generating function. The series `s`
is the square root of `(1+X)(1-3X)` with constant coefficient one, and the
generating-function identity has its denominators cleared. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = n * 3 ^ (n - 1) - 2 * b (n - 1)) ∧
    ∃ s : PowerSeries ℤ, constantCoeff s = 1 ∧ s ^ 2 = (1 + X) * (1 - 3 * X) ∧
      (PowerSeries.mk fun n => (a n : ℤ)) * (1 - 3 * X) ^ 2 * s =
        X * s - 2 * X ^ 2 * (1 - 3 * X) := by
  sorry

end OMA.S_oeis_a359087
