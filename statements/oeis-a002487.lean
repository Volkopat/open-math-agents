import Mathlib

/-!
# OEIS A002487 (Stern's diatomic sequence): frequency conjecture

Source: https://oeis.org/A002487
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Yosu Yurramendi, in the OEIS entry): let `f(m, n)` be the frequency of the integer
`n` in the interval `[a(2^(m-1)), a(2^m - 1)]`. Then `f(m, n) = φ(n)` for all integers
`n ≤ m`.

Reading: the "interval" is the block of terms `a(k)` with index `2^(m-1) ≤ k ≤ 2^m - 1` (the
`m`-th row of the Stern–Brocot / Calkin–Wilf diatomic array), and `1 ≤ n ≤ m`.
Stern's sequence: `a(0) = 0`, `a(1) = 1`, `a(2n) = a(n)`, `a(2n+1) = a(n) + a(n+1)`.
-/

namespace OMA.S_oeis_a002487

/-- Stern's diatomic sequence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if (n + 2) % 2 = 0 then a ((n + 2) / 2)
    else a ((n + 2) / 2) + a ((n + 2) / 2 + 1)
decreasing_by all_goals omega

/-- The conjecture. -/
theorem main :
    ∀ m n : ℕ, 1 ≤ n → n ≤ m →
      ((Finset.Icc (2 ^ (m - 1)) (2 ^ m - 1)).filter fun k => a k = n).card = Nat.totient n := by
  sorry

end OMA.S_oeis_a002487
