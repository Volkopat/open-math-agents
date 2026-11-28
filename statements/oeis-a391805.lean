import Mathlib

/-!
# A391805: Prime gaps around products of consecutive primes

Sources: https://oeis.org/A391805 and https://oeis.org/A391804.
The primes immediately below and above the product give the two sequences.
-/

namespace OMA.S_oeis_a391805

/-- The product at OEIS index `n + 1`, since `Nat.nth` is zero-based. -/
noncomputable def primeProduct (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n * Nat.nth Nat.Prime (n + 1)

def hasBracketingGap (m : ℕ) (k : ℤ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < m ∧ m < q ∧
    (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧ (q : ℤ) - (p : ℤ) = k

theorem main : ∀ k : ℤ, Even k → 4 < k →
    {n : ℕ | hasBracketingGap (primeProduct n) k}.Infinite := by
  sorry

end OMA.S_oeis_a391805
