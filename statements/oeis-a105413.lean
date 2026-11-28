import Mathlib

/-!
# OEIS A105413: Primes p = prime(k) with p+2 and prime(k+6)-2 prime

Source: https://oeis.org/A105413
Credit: @unserus

OEIS: "Conjecture: There are infinitely many primes p(k) such that p(k)+2 and
p(k+m)-2 are both primes for all m > 1."

The sequence is the case `m = 6`. "For all m > 1" is read as: for every fixed
`m > 1` there are infinitely many `k` with `p(k) + 2` and `p(k+m) - 2` both
prime. With the 0-indexed `Nat.nth Nat.Prime i` (so `p(k) = Nat.nth Nat.Prime
(k - 1)`), the index shift `k ↦ k + m` is `i ↦ i + m`. The truncated subtraction
is harmless because every prime is at least 2.
-/

namespace OMA.S_oeis_a105413

/-- The indices `i` such that `p + 2` and `prime(i + m) - 2` are prime, where
`p = Nat.nth Nat.Prime i`. -/
def goodIndices (m : ℕ) : Set ℕ :=
  {i | (Nat.nth Nat.Prime i + 2).Prime ∧ (Nat.nth Nat.Prime (i + m) - 2).Prime}

/-- For every `m > 1` there are infinitely many such primes. -/
theorem main : ∀ m : ℕ, 1 < m → (goodIndices m).Infinite := by
  sorry

end OMA.S_oeis_a105413
