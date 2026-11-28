import Mathlib

/-!
# A387319: Numbers k for which modulo 3 and modulo another multiple of 3 are coincident among the fractions (2*k mod m)/m for 1 <= m <= k.

Source: https://oeis.org/A387319
Credit: @agchua

Comment of A387319 (unsigned; the entry is by Kenneth J Scheller, Oct 24 2025):
  Conjecture: Every composite number, except 4, 8, 10, and 25, has at least one coincident pair
  linking m = 3 with another multiple of 3 among the fractions (2*k mod m)/m for 1 <= m <= k, while
  no prime has such a pair. Empirically verified to 10^5.
The sequence has offset 1. As in the entry's programs (Mathematica: AnyTrue over Range[6, k, 3] of
Mod[2k,m]/m == Mod[2k,3]/3; Python: Fraction, m in range(6, k+1, 3)), k has such a pair when the
fraction at m = 3*j equals the fraction at m = 3 for some j ≥ 2 with 3*j ≤ k, the fractions being
compared as rational numbers (the value 0 included). A composite number is a k > 1 that is not prime.
-/

namespace OMA.S_oeis_a387319

/-- The fraction (2k mod m)/m as a rational number. -/
def fracVal (k m : ℕ) : ℚ := ((2 * k % m : ℕ) : ℚ) / (m : ℚ)

/-- k has a coincident pair linking m = 3 with another multiple of 3, m ≤ k. -/
def InSeq (k : ℕ) : Prop := ∃ j : ℕ, 2 ≤ j ∧ 3 * j ≤ k ∧ fracVal k (3 * j) = fracVal k 3

/-- The comment's conjecture: every composite k other than 4, 8, 10, 25 has such a pair, and no
prime has one. -/
theorem main : (∀ k : ℕ, 1 < k → ¬ k.Prime → k ≠ 4 → k ≠ 8 → k ≠ 10 → k ≠ 25 → InSeq k) ∧
    (∀ p : ℕ, p.Prime → ¬ InSeq p) := by
  sorry

end OMA.S_oeis_a387319
