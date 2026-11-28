import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

/-!
# Finiteness of the primes whose squares use exactly two decimal digits

Source: https://oeis.org/A057659
Credit: @pyaf
-/

namespace OMA.S_oeis_a057659

/-- A057659 lists the elements of this set in increasing order, starting at index 1. -/
def terms : Set ℕ :=
  {p | p.Prime ∧ (Nat.digits 10 (p ^ 2)).toFinset.card = 2}

theorem main : terms.Finite := by
  sorry

end OMA.S_oeis_a057659
