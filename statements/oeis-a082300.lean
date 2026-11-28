import Mathlib

/-!
# OEIS A082300: numbers coprime to the sum of their prime factors

Source: https://oeis.org/A082300
`a n` lists the numbers relatively prime to the sum of their prime factors (with
repetition). Conjecture (Greathouse IV, 2016): `a(n) ~ (π²/6) n`.

Conventions. Numbers `m ≥ 2` are considered (whether `1` is included does not affect the
asymptotic), indexed from `0`; the prime factors are summed with multiplicity.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a082300

open Filter Asymptotics Real

/-- `m ≥ 2` is coprime to the sum of its prime factors with multiplicity. -/
def P (m : ℕ) : Prop := 2 ≤ m ∧ Nat.Coprime m m.primeFactorsList.sum

theorem main :
    (fun n : ℕ => (Nat.nth P n : ℝ)) ~[atTop] fun n : ℕ => π ^ 2 / 6 * n := by
  sorry

end OMA.S_oeis_a082300
