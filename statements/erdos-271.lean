import Mathlib

/-!
# Erdős Problem 271

Source: https://www.erdosproblems.com/271
Credit: @shc261392

The source: let `A(n) = {a₀ < a₁ < ⋯}` be the sequence defined by `a₀ = 0`, `a₁ = n`, and for
`k ≥ 1`, `a_{k+1}` the least positive integer such that there is no three-term arithmetic
progression in `{a₀, …, a_{k+1}}`. Can the `aₖ` be explicitly determined? How fast do they grow?

The question itself is open-ended. The source records the precise conjecture that answers the
growth question: Odlyzko and Stanley [OdSt78] conjectured that every such sequence eventually
satisfies either `aₖ ≍ k ^ (log₂ 3)` or `aₖ ≍ k² / log k`. This file states that conjecture.

Reading used here:
* `n ≥ 1`, since the sequence is listed in increasing order and `a₀ = 0 < a₁ = n`.
* "the least positive integer" is read, as the listing `a₀ < a₁ < ⋯` requires, as the least
  integer greater than `aₖ` (this is the standard definition of a Stanley sequence).
* "no three-term arithmetic progression" is Mathlib's `ThreeAPFree`: no `x, y, z` in the set
  with `x + z = 2y` other than `x = y = z`.
* The sequence is characterised by these properties (it exists and is unique), and the statement
  is made for every sequence with them.
* `aₖ ≍ f(k)` is `Asymptotics.IsTheta` along `atTop`, which already means "eventually".
-/

namespace OMA.S_erdos_271

open Filter Asymptotics

/-- `a` is the Stanley sequence `A(n)`: `a 0 = 0`, `a 1 = n`, it is strictly increasing, and each
`a (k + 1)` for `k ≥ 1` is the least integer above `a k` keeping `{a 0, …, a (k + 1)}` free of
three-term arithmetic progressions. -/
def IsStanleySeq (n : ℕ) (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = n ∧ StrictMono a ∧
    ∀ k : ℕ, 1 ≤ k →
      ThreeAPFree (a '' Set.Iic (k + 1)) ∧
      ∀ m : ℕ, a k < m → m < a (k + 1) → ¬ ThreeAPFree (insert m (a '' Set.Iic k))

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ a : ℕ → ℕ, IsStanleySeq n a →
      ((fun k : ℕ => (a k : ℝ)) =Θ[atTop] fun k : ℕ => (k : ℝ) ^ Real.logb 2 3) ∨
      ((fun k : ℕ => (a k : ℝ)) =Θ[atTop] fun k : ℕ => (k : ℝ) ^ 2 / Real.log k) := by
  sorry

end OMA.S_erdos_271
