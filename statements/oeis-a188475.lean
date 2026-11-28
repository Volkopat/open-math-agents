import Mathlib

/-!
# The Hankel transform of the shifted A137398 sequence

Source: Paul Barry, OEIS A188475, https://oeis.org/A188475. The input
sequence and its Catalan recurrence are given at https://oeis.org/A137398
(OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson

A137398 starts at index 1 with values 0, 1, 2, 7, 22. Shifting the sequence
once removes the initial zero. The order-n transform term is the determinant
of the size-(n+1) Hankel matrix beginning with A137398(2)=1. All entries are
represented as rationals so the division by 3 in Barry's formula is exact.
-/

namespace OMA.S_oeis_a188475
open Finset

/-- A137398 with its OEIS offset. The value q(0) is an unused extension. -/
def q : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => 2 * q (n + 2) + 2 * q (n + 1) +
      ∑ k ∈ range n, (catalan (k + 1) : ℚ) * q (n + 1 - k)
termination_by n => n
decreasing_by all_goals omega

/-- The Hankel matrix of the shifted sequence, indexed from zero. -/
def hankel (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => q (i.val + j.val + 2)

theorem main : ∀ n : ℕ, (hankel (n+1)).det =
    (2*(n:ℚ)^3 + 3*(n:ℚ)^2 + n + 3)/3 := by
  sorry

end OMA.S_oeis_a188475
