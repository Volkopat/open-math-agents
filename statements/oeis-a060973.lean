import Mathlib

/-!
# OEIS A060973: nested self-reference identities

Source: https://oeis.org/A060973
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 0, a(2) = 1`, `a(2n) = 2 a(n)`, `a(2n+1) = a(n+1) + a(n)`. Conjectures (Bala, 2022):
`a(n - a(n)) = a(n - a(n - a(n - a(n))))`; and with `b(n) = a(a(n))`,
`b(n - b(n)) = b(n - b(n - b(n - b(n))))` for `n ≥ 2`.

Conventions:
* `a 0 = 0` (a placeholder; `a(n) < n` for `n ≥ 1`, so the nested arguments stay `≥ 1` in the
  ranges used). The first identity is stated for `n ≥ 1`, the second for `n ≥ 2`; subtraction is
  in `ℕ`.
-/

namespace OMA.S_oeis_a060973

/-- The sequence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => if (n + 3) % 2 = 0 then 2 * a ((n + 3) / 2) else a ((n + 3) / 2 + 1) + a ((n + 3) / 2)
decreasing_by all_goals omega

/-- `b(n) = a(a(n))`. -/
def b (n : ℕ) : ℕ := a (a n)

/-- Bala's two conjectures. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a (n - a n) = a (n - a (n - a (n - a n)))) ∧
    (∀ n : ℕ, 2 ≤ n → b (n - b n) = b (n - b (n - b (n - b n)))) := by
  sorry

end OMA.S_oeis_a060973
