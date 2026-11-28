import Mathlib

/-!
# A090975: Least integer k such that n!+1-k is prime.

Source: https://oeis.org/A090975
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjectures: |a(n)-1| is either 1 or a prime number.
-/

namespace OMA.S_oeis_a090975

noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime (Nat.factorial n + 1 - k)}

theorem main :
    ∀ n : ℕ,
      let d := Int.natAbs ((a n : ℤ) - 1)
      d = 1 ∨ Nat.Prime d := by
  sorry

end OMA.S_oeis_a090975
