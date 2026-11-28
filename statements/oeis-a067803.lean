import Mathlib

/-!
# A067803: Numbers n such that sigma(n)-sigma(n+1)=n.

Source: https://oeis.org/A067803
Credit: @azmiozgen

Conjecture (from the entry): the sequence gives even values only.

Formalization notes:
* The defining equation sigma(n) - sigma(n+1) = n is stated without subtraction as
  sigma(n) = sigma(n+1) + n, for n >= 1 (offset 1).
* Controls: for the first term 532, sigma(532) = 1120 and sigma(533) = 588, difference 532.
-/

namespace OMA.S_oeis_a067803

open ArithmeticFunction

/-- Every `n ≥ 1` with `σ(n) - σ(n+1) = n` is even. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sigma 1 n = sigma 1 (n + 1) + n → Even n := by
  sorry

end OMA.S_oeis_a067803
