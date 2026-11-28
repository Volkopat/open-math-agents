import Mathlib

/-!
# OEIS A002449: a nested-sum formula

Source: https://oeis.org/A002449
`a n` is the number of different types of binary trees of height `n` (1, 1, 2, 6, 26, 166, …),
with g.f. `F(x, 1)` where `F(x, n) = F(x, n-1) + x F(x, 2n)` for `n > 0` and `F(x, 0) = 1`
(Hanna). Conjecture (Irwin, 2016):
`a(n+2) = ∑_{i₁=1}^{2} ∑_{i₂=1}^{2 i₁} ⋯ ∑_{iₙ=1}^{2 i_{n-1}} 2 iₙ`.

Conventions. Telescoping the functional equation gives `F(x, n) = 1 + x ∑_{m=1}^{n} F(x, 2m)`,
so the coefficients `c k n = [x^k] F(x, n)` satisfy `c 0 n = 1` and
`c (k+1) n = ∑_{m=1}^{n} c k (2m)`; `a k = c k 1`. The nested sum with `n ≥ 1` summations is
`H n 1`, where `H 0 i = 2 i` and `H (k+1) i = ∑_{t=1}^{2i} H k t`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002449

/-- `c k n` is the coefficient of `x^k` in `F(x, n)`. -/
def c : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, n => ∑ m ∈ Finset.Icc 1 n, c k (2 * m)

/-- A002449. -/
def a (k : ℕ) : ℕ := c k 1

/-- The nested sums: `H 0 i = 2 i`, `H (k+1) i = ∑_{t=1}^{2i} H k t`. -/
def H : ℕ → ℕ → ℕ
  | 0, i => 2 * i
  | k + 1, i => ∑ t ∈ Finset.Icc 1 (2 * i), H k t

theorem main : ∀ n : ℕ, 1 ≤ n → a (n + 2) = H n 1 := by
  sorry

end OMA.S_oeis_a002449
