import Mathlib

/-!
# OEIS A033093: zeros of `n` written in all bases

Source: https://oeis.org/A033093
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the total number of `0` digits of `n` written in base `b`, over `2 ≤ b ≤ n + 1`.
Conjectures (OEIS entry): `lim inf a(n) = ∞`; and (weaker) `2, 3` and `7` are the only `n` with
`a(n) = 1`.

Conventions:
* `n ≥ 1`; digits via `Nat.digits b n`. `lim inf = ∞` is `Tendsto a atTop atTop`.
-/

namespace OMA.S_oeis_a033093

open Filter

/-- Total number of zero digits of `n` in bases `2, …, n + 1`. -/
def a (n : ℕ) : ℕ :=
  ∑ b ∈ Finset.Icc 2 (n + 1), ((Nat.digits b n).filter (· = 0)).length

/-- `a(n) → ∞`, and `a(n) = 1` only for `n = 2, 3, 7`. -/
theorem main : Tendsto a atTop atTop ∧ ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 2 ∨ n = 3 ∨ n = 7) := by
  sorry

end OMA.S_oeis_a033093
