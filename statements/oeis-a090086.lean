import Mathlib

/-!
# A090086: Smallest pseudoprime to base n, not necessarily exceeding n

Source: https://oeis.org/A090086
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Smallest pseudoprime to base n, not necessarily exceeding n (cf. A007535).
Conjecture: a(n) = A007535(n) (equivalently, a(n) > n) for only finitely many n.
-/

namespace OMA.S_oeis_a090086

/-- Smallest Fermat pseudoprime to base n (composite m > 1 with n^(m-1) ≡ 1 mod m). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ ¬ Nat.Prime m ∧ n ^ (m - 1) % m = 1}

theorem main :
    Set.Finite {n : ℕ | 2 ≤ n ∧ n < a n} := by
  sorry

end OMA.S_oeis_a090086
