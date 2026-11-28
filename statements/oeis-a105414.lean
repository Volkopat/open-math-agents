import Mathlib

/-!
# OEIS A105414: Primes p = prime(k) with p+2 and prime(k+7)-2 prime

Source: https://oeis.org/A105414
Credit: @unserus

OEIS: "Conjecture: There are infinitely many primes p(k) such that p(k)-2 and
p(k+m)-2 are both primes for all m > 1."

The sequence is the case `m = 7`. Its name and data use `p + 2` (e.g. 17, 19),
not `p - 2` (15 is not prime), so the "p(k)-2" in the comment is read as a typo
for "p(k)+2", as in the sibling sequence A105413. "For all m > 1" is read as: for every fixed
`m > 1` there are infinitely many `k` with `p(k) + 2` and `p(k+m) - 2` both
prime. With the 0-indexed `Nat.nth Nat.Prime i` (so `p(k) = Nat.nth Nat.Prime
(k - 1)`), the index shift `k ↦ k + m` is `i ↦ i + m`. The truncated subtraction
is harmless because every prime is at least 2.
-/

namespace OMA.S_oeis_a105414

/-- The indices `i` such that `p + 2` and `prime(i + m) - 2` are prime, where
`p = Nat.nth Nat.Prime i`. -/
def goodIndices (m : ℕ) : Set ℕ :=
  {i | (Nat.nth Nat.Prime i + 2).Prime ∧ (Nat.nth Nat.Prime (i + m) - 2).Prime}

/-- For every `m > 1` there are infinitely many such primes. -/
theorem main : ∀ m : ℕ, 1 < m → (goodIndices m).Infinite := by
  sorry

end OMA.S_oeis_a105414
