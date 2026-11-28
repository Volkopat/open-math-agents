import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.PrimeCounting

/-! OEIS A067786. Donovan Johnson conjectured that the twenty displayed
solutions exhaust the positive integers satisfying the equality.
Source: https://oeis.org/A067786
Credit: @DomTheDeveloper -/

namespace OMA.S_oeis_a067786

def listed : Finset ℕ := {
  11, 13, 27, 39, 63, 122, 124, 136, 152, 176, 224, 322, 364, 410,
  460, 1086, 1164, 3432, 3612, 12012 }

theorem main : ∀ n : ℕ, 0 < n →
    (n.totient = 2 * Nat.primeCounting n ↔ n ∈ listed) := by
  sorry

end OMA.S_oeis_a067786
