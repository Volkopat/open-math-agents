import Mathlib

/-!
# The return time of two colors under a perfect out-shuffle

Source: https://math.stackexchange.com/questions/4553718
Question by jlandercy (2022), CC BY-SA 4.0.
Formalization: @RobVanProd.

We use the out-shuffle shown in the source's Python program and worked
example: the top card stays on top, and the bottom card stays on the bottom.
Positions are numbered from zero. The first n cards are blue and the next
n cards are red. The position map below interleaves the two halves.

The proposed return time is the multiplicative order of 2 modulo 2*n-1,
as suggested in the source and discussed in Qiaochu Yuan's answer.
For n=1 the modulus is 1 and the multiplicative order is 1.

The full color-period result was proved by Angina Seng in 2020:
https://math.stackexchange.com/a/3759624 (CC BY-SA 4.0).
This contribution formalizes that known result.
-/

namespace OMA.S_mse_4553718

def outShuffle (n i : ℕ) : ℕ :=
  if i < n then 2 * i else 2 * (i - n) + 1

def colorsReturn (n k : ℕ) : Prop :=
  ∀ i : ℕ, i < 2 * n → ((outShuffle n)^[k] i < n ↔ i < n)

theorem main : ∀ n : ℕ, 0 < n →
    IsLeast {k : ℕ | 0 < k ∧ colorsReturn n k}
      (orderOf (2 : ZMod (2 * n - 1))) := by
  sorry

end OMA.S_mse_4553718
