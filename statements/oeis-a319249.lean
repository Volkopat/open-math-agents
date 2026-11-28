import Mathlib

/-!
# Twin primes with primitive root 2

OEIS A319249 lists the larger prime in each twin-prime pair whose members
both belong to A001122. The conjecture is that this sequence is infinite.

Sources: https://oeis.org/A319249 and https://oeis.org/A001122
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a319249

/-- Membership in A001122 means that 2 has multiplicative order `p - 1` modulo the prime `p`. -/
def inA001122 (p : ℕ) : Prop :=
  p.Prime ∧ IsPrimitiveRoot (2 : ZMod p) (p - 1)

theorem main : {p : ℕ | inA001122 p ∧ inA001122 (p - 2)}.Infinite := by
  sorry

end OMA.S_oeis_a319249
