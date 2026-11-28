import Mathlib

/-!
# A007691: Multiply-perfect numbers

Source: https://oeis.org/A007691
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Multiply-perfect numbers are the positive integers `n` with `n ∣ σ(n)`. OEIS comment: it is
conjectured that this sequence is infinite.

## Encoding

* `σ` is `ArithmeticFunction.sigma 1`; only positive `n` are considered (`0 ∣ σ 0` would hold
  vacuously in Mathlib, which would not change infinitude anyway).
* Only the first conjecture of the entry (infinitude) is stated here.
-/

namespace OMA.S_oeis_a007691

open ArithmeticFunction

theorem main : {n : ℕ | 0 < n ∧ n ∣ sigma 1 n}.Infinite := by
  sorry

end OMA.S_oeis_a007691
