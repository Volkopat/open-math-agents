import Mathlib

/-!
# OEIS A109730: twin admirable numbers

Source: https://oeis.org/A109730
Lesser of twin admirable numbers: `k` such that `k` and `k + 2` are both admirable.
Conjecture: the sequence is infinite.

Conventions. `n` is admirable if, for some proper divisor `d` of `n`, the sum of the proper
divisors of `n` with `d` taken negatively equals `n`, i.e. `σ(n) - n - 2d = n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a109730

/-- `n` is admirable. -/
def IsAdmirable (n : ℕ) : Prop :=
  ∃ d ∈ n.properDivisors, (∑ e ∈ n.properDivisors, e) = n + 2 * d

theorem main : {k : ℕ | IsAdmirable k ∧ IsAdmirable (k + 2)}.Infinite := by
  sorry

end OMA.S_oeis_a109730
