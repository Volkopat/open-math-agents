import Mathlib

/-!
# Wu's congruence conjecture for A337818

Source: https://oeis.org/A337818.
The sequence lists in increasing order the odd integers k ≥ 3 for which
k(k-1)/2 divides 2^((k-1)/2)+1. Chai Wah Wu conjectured that all terms
from the sixth onward are congruent to 1 modulo 162. A term is sixth
or later exactly when at least five smaller integers satisfy the same
divisibility condition.
-/

namespace OMA.S_oeis_a337818

def IsTerm (k : ℕ) : Prop :=
  3 ≤ k ∧ Odd k ∧ (k*(k-1)/2) ∣ (2^((k-1)/2)+1)

theorem main : ∀ k : ℕ, IsTerm k →
    5 ≤ ((Finset.range k).filter (fun j => 3 ≤ j ∧ Odd j ∧
      (j*(j-1)/2) ∣ (2^((j-1)/2)+1))).card → k % 162 = 1 := by
  sorry

end OMA.S_oeis_a337818
