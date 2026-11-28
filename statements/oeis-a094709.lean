import Mathlib

/-!
# A094709: Smallest k such that prime(n)# - k and prime(n)# + k are primes, where prime(n)# = A002110(n).

Source: https://oeis.org/A094709
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Goldbach's conjecture implies that a(n) is defined for all n.
-/

namespace OMA.S_oeis_a094709

/-- The `n`-th primorial `prime(n)# = ∏_{i=0}^{n-1} prime(i+1)`. -/
noncomputable def primorial (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, k < primorial n ∧ (primorial n - k).Prime ∧ (primorial n + k).Prime := by
  sorry

end OMA.S_oeis_a094709
