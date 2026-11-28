import Mathlib

/-!
# A081113: King paths of length n-1 across an n x n chessboard

Source: https://oeis.org/A081113
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Number of paths of length n-1 a king can take from one side of an n x n chessboard
to the opposite side.
Conjecture: (n+3)*a(n+4) = 27*n*a(n) + 27*a(n+1) - 9*(2*n+5)*a(n+2) + (8*n+21)*a(n+3).
-/

namespace OMA.S_oeis_a081113

noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {c : Fin n → Fin n //
    ∀ i : Fin n, ∀ h : i.1 + 1 < n, |((c ⟨i.1 + 1, h⟩).1 : ℤ) - ((c i).1 : ℤ)| ≤ 1}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℤ) + 3) * (a (n + 4) : ℤ) =
        27 * (n : ℤ) * (a n : ℤ) +
        27 * (a (n + 1) : ℤ) -
        9 * (2 * (n : ℤ) + 5) * (a (n + 2) : ℤ) +
        (8 * (n : ℤ) + 21) * (a (n + 3) : ℤ) := by
  sorry

end OMA.S_oeis_a081113
