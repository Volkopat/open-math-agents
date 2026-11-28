import Mathlib

/-!
# A393024: every number greater than 1190 is a sum of powers with increasing bases and
decreasing exponents

Source: https://oeis.org/A393024
Credit: @gblacher2

A393024 (Alberto Zanoni): "Numbers that can be written as s_1^x_1 + ... + s_t^x_t, with
0 < s_1 < ... < s_t and x_1 > ... > x_t > 1 for some t > 0, with the restriction that if s_1 = 1
then x_1 is the least possible."
Data: 1, 4, 5, 8, 9, 10, 16, 17, 18, 24, 25, 26, 27, 28, 32, 33, 34, 36, 37, 41, ...
Conjecture (in the entry): "All natural numbers greater than 1190 appear in this sequence."

`IsTerm n` encodes the definition literally, with the bases `s` and exponents `x` indexed by
`Fin t`. "If s_1 = 1 then x_1 is the least possible" is read as: when `s₁ = 1`, the exponent `x₁` is
the least `y > 1` with `y > x₂` (the only constraint on `x₁`; when `t = 1` there is no `x₂`). Since
`1 ^ y = 1` for every `y`, this restriction only fixes which representation is counted and does not
change which numbers are terms.

Checks: with this definition (computed by exhaustive search), the terms up to 117 are exactly the
71 listed terms of A393024, and the only number in `1001..6000` that is not a term is 1190
(checked numerically).
-/

namespace OMA.S_oeis_a393024

/-- `n` can be written as `s₁ ^ x₁ + ⋯ + s_t ^ x_t` with `t > 0`, `0 < s₁ < ⋯ < s_t`,
`x₁ > ⋯ > x_t > 1`, and, if `s₁ = 1`, with `x₁` the least possible exponent. -/
def IsTerm (n : ℕ) : Prop :=
  ∃ t : ℕ, ∃ ht : 0 < t, ∃ s x : Fin t → ℕ,
    (∀ i, 0 < s i) ∧ StrictMono s ∧ StrictAnti x ∧ (∀ i, 1 < x i) ∧
    (s ⟨0, ht⟩ = 1 → ∀ y : ℕ, 1 < y → (∀ h1 : 1 < t, x ⟨1, h1⟩ < y) → x ⟨0, ht⟩ ≤ y) ∧
    ∑ i, s i ^ x i = n

/-- **A393024 conjecture.** Every natural number greater than 1190 is a term of A393024. -/
theorem main : ∀ n : ℕ, 1190 < n → IsTerm n := by
  sorry

end OMA.S_oeis_a393024
