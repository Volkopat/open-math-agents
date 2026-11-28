import Mathlib

/-!
# OEIS A106228: inversion sequences avoiding a pattern

Source: https://oeis.org/A106228
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The g.f. `A(x)` of A106228 satisfies `A(x) = 1 + x A(x)/(1 - x A(x)²)`. Conjecture (Martinez and
Savage, 2.21): `a(n)` is the number of sequences `(e(1), …, e(n))` with `0 ≤ e(i) < i` such that
there is no triple `i < j < k` with `e(i) > e(j)` and `e(i) ≤ e(k)`.

Conventions:
* The functional equation, multiplied by `1 - x A²`, reads `A (1 - x A²) = 1 - x A² + x A` in
  `ℤ⟦x⟧`; with `A(0) = 1` it determines `A` uniquely (coefficient by coefficient). `main`
  quantifies over every such `A`.
* Inversion sequences of length `n` are `e : Fin n → ℕ` with `e i < i + 1` (0-based `i`).
-/

namespace OMA.S_oeis_a106228

open PowerSeries

/-- Inversion sequences of length `n` avoiding the pattern. -/
def count (n : ℕ) : ℕ :=
  ((Finset.univ : Finset ((i : Fin n) → Fin ((i : ℕ) + 1))).filter fun e =>
    ∀ i j k : Fin n, i < j → j < k → ¬ ((e j : ℕ) < e i ∧ (e i : ℕ) ≤ e k)).card

/-- The coefficients of `A` count the pattern-avoiding inversion sequences. -/
theorem main : ∀ A : PowerSeries ℤ, constantCoeff A = 1 →
    A * (1 - X * A ^ 2) = 1 - X * A ^ 2 + X * A →
    ∀ n : ℕ, coeff n A = count n := by
  sorry

end OMA.S_oeis_a106228
