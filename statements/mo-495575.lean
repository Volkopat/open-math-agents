import Mathlib

/-!
# An alternating inequality with a moving denominator

Source: MathOverflow user 12493U28, https://mathoverflow.net/questions/495575 (CC BY-SA 4.0).
Contribution by @connoranderson.

The original inequality involves rational numbers; it is stated with the
same interval of summation and the two distinct positive denominators.
-/

namespace OMA.S_mo_495575
open Finset

theorem main : ∀ k : ℕ, 4 ≤ k → (-1:ℚ)^(k-1)/k <
    ∑ m ∈ Ico 2 k, ((-1:ℚ)^m/m)*
      (1/((k-m:ℕ):ℚ)^m + 1/((k-m+1:ℕ):ℚ)^m) := by
  sorry

end OMA.S_mo_495575
