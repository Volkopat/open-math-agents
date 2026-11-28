import Mathlib

/-!
# OEIS A052542: compositions into odd parts of two types

Source: https://oeis.org/A052542
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(0) = 1, a(1) = 2, a(2) = 4`, `a(n) = 2 a(n-1) + a(n-2)`. Conjecture (OEIS entry; proved there
via the g.f. `1/(1 - 2x/(1 - x²))`): apart from the initial `1`, `a(n)` is the number of
compositions of `n` of two types having no even parts.

Conventions:
* A composition of two types with no even parts is a composition of `n` into odd parts, each part
  coloured in one of two ways; their number is `∑ 2^(number of parts)` over compositions into odd
  parts. Compositions are Mathlib's `Composition n`; `n ≥ 1`.
-/

namespace OMA.S_oeis_a052542

/-- The sequence. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | n + 3 => 2 * a (n + 2) + a (n + 1)

/-- `a(n)` counts two-coloured compositions of `n` into odd parts, for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ∑ c ∈ (Finset.univ : Finset (Composition n)).filter (fun c => ∀ p ∈ c.blocks, Odd p),
      2 ^ c.length := by
  sorry

end OMA.S_oeis_a052542
