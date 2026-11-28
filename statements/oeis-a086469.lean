import Mathlib

/-!
# A086469: Sum of the distinct (smallest) prime signature divisors of n. In case of two or more divisors with the same prime signature the smallest is chosen.

Source: https://oeis.org/A086469
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Define n as a 'psigma perfect number' if psigma(n) = 2n. 18 is a psigma perfect number.
Conjecture: 18 is the only psigma perfect number.
-/

namespace OMA.S_oeis_a086469

open Classical

noncomputable def primeSignature (n : ℕ) : Multiset ℕ :=
  n.factorization.support.val.map n.factorization

noncomputable def psigma (n : ℕ) : ℕ :=
  ∑ s ∈ (Nat.divisors n).image primeSignature,
    sInf {d : ℕ | d ∈ Nat.divisors n ∧ primeSignature d = s}

theorem main : ∀ n : ℕ, 1 ≤ n → psigma n = 2 * n → n = 18 := by
  sorry

end OMA.S_oeis_a086469
