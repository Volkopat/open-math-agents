import Mathlib

/-!
# A175625: Numbers k such that gcd(k, 6) = 1, 2^(k-1) == 1 (mod k), and 2^(k-3) == 1 (mod (k-1)/2).

Source: https://oeis.org/A175625
Credit: @agchua

Comment of A175625 (Bill McEachen, Dec 27 2023), verbatim:
  Conjecture: The prime values belong to A039787.

A039787: Primes p such that p-1 is squarefree.

Formalisation. `IsTerm k` is the defining condition of A175625, with both congruences written
as `Nat.ModEq`. The listed terms are odd and at least 7, so the subtractions k - 1 and k - 3
and the modulus (k - 1) / 2 have their usual meaning there; the only k below 7 that satisfies
`IsTerm k` is k = 1, which is not prime, so the prime k with `IsTerm k` are exactly the prime
terms of A175625. The conjecture says that every such k lies in A039787, that is, k - 1 is
squarefree.
-/

namespace OMA.S_oeis_a175625

/-- The defining condition of A175625: gcd(k, 6) = 1, 2^(k-1) == 1 (mod k) and
2^(k-3) == 1 (mod (k-1)/2). -/
def IsTerm (k : ℕ) : Prop :=
  Nat.gcd k 6 = 1 ∧ 2 ^ (k - 1) ≡ 1 [MOD k] ∧ 2 ^ (k - 3) ≡ 1 [MOD (k - 1) / 2]

/-- A039787: the primes p such that p - 1 is squarefree. -/
def A039787 : Set ℕ := {p | p.Prime ∧ Squarefree (p - 1)}

/-- McEachen's conjecture: the prime terms of A175625 belong to A039787. -/
theorem main : ∀ k : ℕ, IsTerm k → k.Prime → k ∈ A039787 := by
  sorry

end OMA.S_oeis_a175625
