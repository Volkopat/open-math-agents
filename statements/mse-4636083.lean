import Mathlib

/-!
# Proper subgroup of $GL(V)$ isomorphic to $GL(V)$

Source: https://math.stackexchange.com/questions/4636083/is-there-a-subgroup-of-the-general-linear-group-isomorphic-to-the-general-linear
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $V$ be a finite-dimensional vector space of dimension $n \ge 2$ over a field $K$ of
characteristic $0$. Does there exist a proper subgroup of $GL(V)$ isomorphic to $GL(V)$?
-/

namespace OMA.S_mse_4636083

theorem main :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (n : ℕ),
      2 ≤ n ∧
      ∃ H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K),
        H < ⊤ ∧ Nonempty (H ≃* Matrix.GeneralLinearGroup (Fin n) K) := by
  sorry

end OMA.S_mse_4636083
