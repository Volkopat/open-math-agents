import Mathlib

/-!
# A087318: Smallest number of the form n^k + 1 with the prime signature of n

Source: https://oeis.org/A087318
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the smallest number of the form n^k + 1 with the prime signature of n,
or 0 if no such number exists. If n is an i-th power for i > 1, then a(n) = 0.
The other zeros (including 12, 20, 24, 28, 40, 45, 48, 50, 52, 54, 55, 56, 60,
63, and 68) are conjectured to have no such k.
-/

namespace OMA.S_oeis_a087318

/-- The prime signature of `n`, as the multiset of exponents in its prime factorization. -/
noncomputable def primeSignature (n : ℕ) : Multiset ℕ :=
  n.factorization.support.val.map n.factorization

/-- The conjectured non-perfect-power zeros listed in A087318. -/
def conjecturedZeros : Finset ℕ :=
  {12, 20, 24, 28, 40, 45, 48, 50, 52, 54, 55, 56, 60, 63, 68}

theorem main :
    ∀ n ∈ conjecturedZeros, ∀ k : ℕ, 1 ≤ k →
      primeSignature (n ^ k + 1) ≠ primeSignature n := by
  sorry

end OMA.S_oeis_a087318
