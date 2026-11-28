import Mathlib

/-!
# A387426: Numbers k such that all nonzero fractions (2*k mod m)/m (for 1 <= m <= k) are distinct.

Source: https://oeis.org/A387426
Credit: @agchua

Comment of A387426 (unsigned; the entry is by Kenneth J Scheller, Oct 01 2025):
  Conjecture: Every prime is in the sequence, and no composite greater than 24 is in the sequence.
  Empirically verified for k <= 10^6.
Membership of k is the predicate InSeq k below: the map m ↦ (2k mod m)/m, a rational number, is
injective on the set of m with 1 ≤ m ≤ k whose fraction is nonzero, that is 2k mod m ≠ 0. The
fractions are compared as rational numbers, as in the entry's programs (Mathematica Mod[2k,m]/m,
Python Fraction). For k > 24, composite is the same as not prime.
-/

namespace OMA.S_oeis_a387426

/-- k is a term of A387426: the nonzero fractions (2k mod m)/m, 1 ≤ m ≤ k, are pairwise distinct. -/
def InSeq (k : ℕ) : Prop :=
  Set.InjOn (fun m : ℕ => ((2 * k % m : ℕ) : ℚ) / (m : ℚ)) {m : ℕ | 1 ≤ m ∧ m ≤ k ∧ 2 * k % m ≠ 0}

/-- The comment's conjecture: every prime is a term, and no composite k > 24 is a term. -/
theorem main : (∀ p : ℕ, p.Prime → InSeq p) ∧ (∀ k : ℕ, 24 < k → ¬ k.Prime → ¬ InSeq k) := by
  sorry

end OMA.S_oeis_a387426