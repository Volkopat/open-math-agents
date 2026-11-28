import Mathlib

/-!
A074915: Largest x such that the number of nonprimes (i.e., 1 and composites) in the reduced residue set (RRS(x)) of x equals n, or 0 if there is no such x.

Source: https://oeis.org/A074915
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

It is conjectured that x is always bounded.
-/

namespace OMA.S_oeis_a074915

/-- Number of nonprimes in the reduced residue system `{k ∈ [1, x] | gcd(k, x) = 1}`. -/
def nonprimeRRSCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun k => Nat.Coprime k x ∧ ¬ Nat.Prime k)).card

/-- Conjecture: for every `n`, the set of positive integers `x` whose reduced residue system
contains exactly `n` nonprimes is bounded above. -/
theorem main :
    ∀ n : ℕ, BddAbove {x : ℕ | 0 < x ∧ nonprimeRRSCount x = n} := by sorry

end OMA.S_oeis_a074915
