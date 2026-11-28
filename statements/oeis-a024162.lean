import Mathlib

/-!
# OEIS A024162: primitive scalene integer triangles with perimeter `n`

Source: https://oeis.org/A024162
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of incongruent integer-sided triangles with sides `a < b < c`,
`a + b + c = n` and `gcd(a, b, c) = 1`. Conjecture (Huber, 2025): `a(2k - 1) ≥ a(2k)`.

Conventions:
* Triangles are nondegenerate: `c < a + b`. Triples with `a < b < c` are pairwise incongruent,
  so `a(n)` counts such triples. `k ≥ 1`.
-/

namespace OMA.S_oeis_a024162

/-- Number of `a < b < c`, `a + b + c = n`, `c < a + b`, `gcd(a, b, c) = 1`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun p =>
    let x := p.1; let y := p.2; let z := n - x - y
    0 < x ∧ x < y ∧ y < z ∧ x + y + z = n ∧ z < x + y ∧ Nat.gcd (Nat.gcd x y) z = 1).card

/-- `a(2k - 1) ≥ a(2k)` for all `k ≥ 1`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → a (2 * k) ≤ a (2 * k - 1) := by
  sorry

end OMA.S_oeis_a024162
