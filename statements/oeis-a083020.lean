import Mathlib.Data.Nat.Squarefree

/-!
# OEIS A083020

Source: https://oeis.org/A083020
Credit: @PrimordialAA

The index starts at zero. The conjecture says that every number
`3 ^ (3 ^ n) + 2` is squarefree.
-/

namespace OMA.S_oeis_a083020

theorem main : ∀ n : ℕ, Squarefree (3 ^ (3 ^ n) + 2) := by
  sorry

end OMA.S_oeis_a083020
