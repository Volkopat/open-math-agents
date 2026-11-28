import Mathlib

/-!
# Zero runs in the binary expansion of a cube

Source: https://oeis.org/A090049
Credit: @etaubman

A090049 assigns 1 to zero, using its one-digit binary representation.
For positive inputs, reversing the order in which the digits are read
preserves the length of every zero run.
-/

namespace OMA.S_oeis_a090049

/-- A contiguous block of r zero digits. -/
def zeroBlock (bits : List ℕ) (r : ℕ) : Prop :=
  ∃ before after : List ℕ, bits = before ++ List.replicate r 0 ++ after

/-- Length of the longest binary zero run of the cube, with A090049(0) = 1. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if n = 0 then 1 else
    Nat.findGreatest (zeroBlock (Nat.digits 2 (n ^ 3))) (Nat.digits 2 (n ^ 3)).length

/-- The valuation lower bound and the strict bound for all positive k.
At k = 0 the only eligible n is zero, and A090049(0) = 1. -/
theorem main : (∀ n e : ℕ, n ≠ 0 → 2 ^ e ∣ n → 3 * e ≤ a n) ∧
    (∀ n k : ℕ, n < 2 ^ k → (a n < 3 * k ↔ 0 < k)) := by
  sorry

end OMA.S_oeis_a090049
