import Mathlib

/-!
# Zeros in the decimal expansion of n!

Source: https://mathoverflow.net/questions/393993
Is `40` the largest number for which all the `0` digits in the decimal form of `n!` come at
the end? `main` states the affirmative answer: `40` is the greatest such `n`.

Conventions. Stripping the trailing zeros of `n!` means dividing by `10^v` with `v` the
`10`-adic valuation; the condition is that the result has no digit `0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_393993

/-- All zero digits of `n!` are trailing zeros. -/
def ZerosAtEnd (n : ℕ) : Prop :=
  0 ∉ Nat.digits 10 (n.factorial / 10 ^ padicValNat 10 n.factorial)

theorem main : IsGreatest {n : ℕ | ZerosAtEnd n} 40 := by
  sorry

end OMA.S_mo_393993
