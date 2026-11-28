import Mathlib

/-!
# A077653: a(1)=1, a(2)=2, a(3)=2, a(n) = abs(a(n-1) - a(n-2) - a(n-3)).

Source: https://oeis.org/A077653
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: let z(1)=x, z(2)=y, z(3)=z, z(n) = abs(z(n-1) - z(n-2) - z(n-3)).
If z(n) is unbounded, then there are two integers n(x,y,z) and w(x,y,z) such that
M(n) = floor(sqrt(n + w(x,y,z))) for n > n(x,y,z), where M(n) = max { z(k) : 1 <= k <= n }.
-/

namespace OMA.S_oeis_a077653

/-- The recurrence `z(1) = x`, `z(2) = y`, `z(3) = w`, `z(n) = |z(n-1) - z(n-2) - z(n-3)|`. -/
def seq (x y w : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => x
  | 2 => y
  | 3 => w
  | n + 4 => |seq x y w (n + 3) - seq x y w (n + 2) - seq x y w (n + 1)|

/-- Running maximum `M(n) = max_{1 <= k <= n} seq x y w k`. -/
def maxUpTo (x y w : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => max (maxUpTo x y w n) (seq x y w (n + 1))

theorem main :
    ∀ x y w : ℕ, (∀ B : ℤ, ∃ n : ℕ, 1 ≤ n ∧ B < seq x y w n) →
      ∃ N : ℕ, ∃ C : ℤ, ∀ n : ℕ, N < n →
        maxUpTo x y w n = Int.floor (Real.sqrt ((n : ℝ) + (C : ℝ))) := by sorry

end OMA.S_oeis_a077653
