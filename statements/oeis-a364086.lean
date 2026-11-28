import Mathlib

/-!
# A364086: Fixed points of A002326, i.e., numbers k such that A002326(k) = k.

Source: https://oeis.org/A364086
Credit: @agchua

Comment of A364086 (unsigned; the entry is by Daniel Haase, Jul 09 2023):
  The related case of A002326(k) = 2k is true if (and conjecturally only if) 2k+1 is a prime with
  primitive root 2, see A001122.
A002326(n) (offset 0) is the multiplicative order of 2 modulo 2n+1; A002326(0) = 1, the order of 2
modulo 1. A001122 lists the primes with primitive root 2, i.e. the primes p for which the order of 2
modulo p is p - 1. The claim is stated for every k >= 0 (the offset of A002326): A002326(k) = 2k
holds if and only if 2k+1 is a prime with primitive root 2. For k = 0 both sides are false.
-/

namespace OMA.S_oeis_a364086

/-- A002326(n): the multiplicative order of 2 modulo 2n+1. -/
noncomputable def A002326 (n : ℕ) : ℕ := orderOf (2 : ZMod (2 * n + 1))

/-- p is in A001122: p is a prime and 2 is a primitive root modulo p. -/
noncomputable def HasPrimitiveRoot2 (p : ℕ) : Prop := Nat.Prime p ∧ orderOf (2 : ZMod p) = p - 1

/-- The claim: A002326(k) = 2k if and only if 2k+1 is a prime with primitive root 2. -/
theorem main : ∀ k : ℕ, A002326 k = 2 * k ↔ HasPrimitiveRoot2 (2 * k + 1) := by
  sorry

end OMA.S_oeis_a364086
