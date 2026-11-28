import Mathlib

/-!
# Squarefreeness of the Fermat numbers

The comment on OEIS A078900 conjectures that every ordinary Fermat number
`2^(2^n) + 1` is squarefree. Mathlib's `Nat.fermatNumber` uses the ordinary
zero-based indexing of A000215.

Source: https://oeis.org/A078900
Credit: @wtho704
-/

namespace OMA.S_oeis_a078900

theorem main : ∀ n : ℕ, Squarefree (Nat.fermatNumber n) := by
  sorry

end OMA.S_oeis_a078900
