import Mathlib

/-!
# A102751: two prime values determined by an odd integer k

Source: https://oeis.org/A102751
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A102/A102751.seq
Credit: @Bondyboy2001

The sequence consists of numbers `k` for which `1 + (k-1)^2` and
`((k-1)/2)^2 + ((k+1)/2)^2 = (k^2+1)/2` are both prime. The second value is integral exactly
when `k` is odd, and the entry's terms are odd. The sequence is conjectured to be infinite.
-/

namespace OMA.S_oeis_a102751

/-- Membership in A102751. -/
def IsTerm (k : ℕ) : Prop :=
  Odd k ∧ (1 + (k - 1) ^ 2).Prime ∧ ((k ^ 2 + 1) / 2).Prime

theorem main : {k : ℕ | IsTerm k}.Infinite := by
  sorry

end OMA.S_oeis_a102751
