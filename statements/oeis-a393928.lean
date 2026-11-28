import Mathlib

/-!
# A393928: Smallest prime q such that the set of p-1 consecutive primes starting at q forms a complete system of residues modulo p (excluding p mod p), where p=prime(n)

Source: https://oeis.org/A393928
Credit: @gblacher2

Conjecture (stated in A393928): for any prime number p, there exists at least one prime number q
such that the sequence of p-1 consecutive prime numbers {p_k, p_{k+1}, ..., p_{k+p-2}} with
p_k = q forms a complete system of nonzero residues modulo p.

Formalization notes:
* The primes are enumerated by `Nat.nth Nat.Prime` (0-indexed: `Nat.nth Nat.Prime 0 = 2`); the
  p-1 consecutive primes starting at `q = Nat.nth Nat.Prime k` are `Nat.nth Nat.Prime (k + i)` for
  `i < p - 1`.
* "Complete system of nonzero residues modulo p": the residues of these p-1 primes modulo p are
  exactly 1, ..., p-1. As there are p-1 primes and p-1 nonzero residues, this says that each
  nonzero residue occurs exactly once (and the residue 0 does not occur).
* Check of the reading: the least such q for p = 2, 3, 5, 7, 11, 13, 17, 19, 23 is 3, 5, 11, 11,
  41, 10267, 832361, 1565437, 52112257, the first nine data terms of A393928.
-/

namespace OMA.S_oeis_a393928

/-- The conjecture of A393928: for every prime `p` there is a prime `q = p_k` such that the
residues modulo `p` of the `p - 1` consecutive primes `p_k, ..., p_{k+p-2}` are exactly
`1, ..., p - 1`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ q : ℕ, q.Prime ∧ ∃ k : ℕ, Nat.nth Nat.Prime k = q ∧
    (Finset.range (p - 1)).image (fun i => Nat.nth Nat.Prime (k + i) % p) =
      Finset.Icc 1 (p - 1) := by
  sorry

end OMA.S_oeis_a393928
