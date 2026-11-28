import Mathlib

/-!
# OEIS A068405: k with k+1 squarefree composite and omega(k) = omega(k+1) + 1

Source: https://oeis.org/A068405
Credit: @unserus

OEIS: "Contains 15*p if p is a prime > 5 such that (15*p + 1)/2 is prime.
Thus Dickson's conjecture would imply that this sequence is infinite."

The sequence lists the numbers `k` such that `k + 1` is squarefree and composite
and `k` has exactly one more distinct prime factor than `k + 1`. The open
statement is that there are infinitely many such `k`. "Composite" is written as
`1 < k + 1 ∧ ¬ (k + 1).Prime`; the number of distinct prime factors is
`Nat.primeFactors _ |>.card` (the OEIS `omega`).
-/

namespace OMA.S_oeis_a068405

/-- The terms of A068405. -/
def a068405Set : Set ℕ :=
  {k | Squarefree (k + 1) ∧ 1 < k + 1 ∧ ¬ (k + 1).Prime ∧
    k.primeFactors.card = (k + 1).primeFactors.card + 1}

/-- A068405 is infinite (implied by Dickson's conjecture). -/
theorem main : a068405Set.Infinite := by
  sorry

end OMA.S_oeis_a068405
