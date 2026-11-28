import Mathlib.Data.Int.Basic
import Mathlib.Logic.Function.Iterate

/-!
# OEIS A386885

Every nonzero integer reaches 1 under the map that sends even x to
-x/2 and odd x to 3x + 1.
Source: https://oeis.org/A386885
-/

namespace OMA.S_oeis_a386885

def step (x : ℤ) : ℤ :=
  if x % 2 = 0 then -(x / 2) else 3 * x + 1

theorem main : ∀ x : ℤ, x ≠ 0 → ∃ k : ℕ, (step^[k]) x = 1 := by
  sorry

end OMA.S_oeis_a386885
