import Mathlib

/-!
# A242752: Primes p such that pi(p) is a primitive root modulo p, where pi(p) is the number of primes not exceeding p.

Source: https://oeis.org/A242752
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "According to the conjecture in A232748, this sequence
should contain infinitely many primes."

Conventions: `pi(p)` is `Nat.primeCounting p`, the number of primes `≤ p`. For a prime `p`,
"`g` is a primitive root modulo `p`" means that the residue of `g` has multiplicative order
`p - 1` in `ZMod p`, i.e. `IsPrimitiveRoot (g : ZMod p) (p - 1)`. For `p = 2` this holds for
`pi(2) = 1`, matching the OEIS data, which starts with `2`.
-/

namespace OMA.S_oeis_a242752

/-- The terms of A242752: primes `p` such that `pi(p)` is a primitive root modulo `p`. -/
def S : Set ℕ :=
  {p | p.Prime ∧ IsPrimitiveRoot (Nat.primeCounting p : ZMod p) (p - 1)}

/-- A242752 contains infinitely many primes. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a242752
