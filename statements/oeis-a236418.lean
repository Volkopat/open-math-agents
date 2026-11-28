import Mathlib

/-!
# OEIS A236418: Primes p with A047967(p) also prime

Source: https://oeis.org/A236418
Credit: @unserus

OEIS: "According to the conjecture in A236417, this sequence should have
infinitely many terms."

A047967(n) is the number of partitions of `n` with some part repeated, i.e. the
partitions of `n` whose multiset of parts is not duplicate-free
(A047967(n) = A000041(n) - A000009(n)). The terms are the primes `p` for which
A047967(p) is prime; the statement is that there are infinitely many.
-/

namespace OMA.S_oeis_a236418

/-- A047967(n): the number of partitions of `n` with some part repeated. -/
def a047967 (n : ℕ) : ℕ :=
  (Finset.univ.filter fun π : Nat.Partition n => ¬ π.parts.Nodup).card

/-- The terms of A236418. -/
def a236418Set : Set ℕ := {p | p.Prime ∧ (a047967 p).Prime}

/-- A236418 is infinite. -/
theorem main : a236418Set.Infinite := by
  sorry

end OMA.S_oeis_a236418
