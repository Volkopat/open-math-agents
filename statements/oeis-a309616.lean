import Mathlib

/-!
# OEIS A309616

Source: https://oeis.org/A309616 (OEIS Foundation, CC BY-SA 4.0).
The statement uses the one-based indexing of Sela Fried's proof
https://oeis.org/A309616/a309616.pdf and of the conjecture as written.

To count representations of m with digits 0 through 9 and place values 2^i,
strip the lowest digit. It must be 2j + m % 2, for 0 ≤ j ≤ 4 and j ≤ m / 2.
The remaining value is m / 2 - j, so its possible values run over the
interval from m / 2 - 4 to m / 2, with natural-number subtraction.
Zero has one representation, with every digit zero.
-/

namespace OMA.S_oeis_a309616

/-- Number of decibinary representations, obtained by stripping the lowest digit. -/
def representations : ℕ → ℕ
  | 0 => 1
  | m + 1 => ∑ t ∈ Finset.Icc ((m + 1) / 2 - 4) ((m + 1) / 2),
      if ht : t < m + 1 then representations t else 0
termination_by m => m
decreasing_by omega

/-- A309616 in the conjecture's one-based convention. -/
def a (n : ℕ) : ℕ := representations (2 * (n - 1))

/-- The stated recurrence, with the ceilings written using natural division. -/
theorem main : ∀ n : ℕ, 5 < n →
    (a n : ℤ) = (a (n - 1) : ℤ) + (a ((n + 1) / 2) : ℤ) -
      (a (((n - 5) + 1) / 2) : ℤ) := by
  sorry

end OMA.S_oeis_a309616
