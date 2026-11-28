import Mathlib

/-!
# OEIS A033235: Primes of the Form x^2 + 55 y^2

Source: https://oeis.org/A033235
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $b(k)$ be the linear recurrence sequence defined by
$b(0) = 2$, $b(1) = 1$, $b(2) = 0$, $b(3) = -1$, and
$$b(k) = -b(k-1) - b(k-2) + b(k-3) - b(k-4) \quad (k \ge 4).$$

Conjecture (Lechoslaw Ratajczak, 2017):
A prime $p$ is of the form $x^2 + 55 y^2$ (for integers $x, y$) if and only if
$b(p) \equiv 1 \pmod{p}$.
-/

namespace OMA.S_oeis_a033235

/-- Linear recurrence `b(k) = -b(k-1) - b(k-2) + b(k-3) - b(k-4)` with initial values
`b(0) = 2, b(1) = 1, b(2) = 0, b(3) = -1`. -/
def b : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | 3 => -1
  | k + 4 => -b (k + 3) - b (k + 2) + b (k + 1) - b k

theorem main :
    ∀ p : ℕ, Nat.Prime p →
      ((∃ x y : ℤ, (p : ℤ) = x ^ 2 + 55 * y ^ 2) ↔ (p : ℤ) ∣ (b p - 1)) := by
  sorry

end OMA.S_oeis_a033235
