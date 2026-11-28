import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Function.Iterate

/-!
# Conway's RATS conjecture

Conway conjectured that the base-ten RATS trajectory of every positive integer eventually
enters a cycle or meets the trajectory starting at 12334444, known as the creeper.

Sources: https://oeis.org/A164338 and https://oeis.org/A036839
Credit: @PABixn
-/

namespace OMA.S_oeis_a164338

/-- Reverse the decimal digits, add, then sort the sum's digits in increasing order. -/
def rats (n : ℕ) : ℕ :=
  let reversed := Nat.ofDigits 10 (Nat.digits 10 n).reverse
  -- The digit list is little-endian, so decreasing list order gives increasing decimal order.
  Nat.ofDigits 10 ((Nat.digits 10 (n + reversed)).mergeSort fun a b => decide (b ≤ a))

/-- A repeated value in the deterministic trajectory starts a cycle. The other alternative
is that some iterate agrees with a term of the creeper. -/
theorem main : ∀ n : ℕ, 0 < n →
    (∃ k p : ℕ, 0 < p ∧ (rats^[k + p]) n = (rats^[k]) n) ∨
    (∃ k j : ℕ, (rats^[k]) n = (rats^[j]) 12334444) := by
  sorry

end OMA.S_oeis_a164338
