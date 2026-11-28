import Mathlib

/-!
# A389863: Numbers k with exactly two distinct repeated values among the fractions (2*k mod m)/m for 1 <= m <= k.

Source: https://oeis.org/A389863
Credit: @agchua

Comment of A389863 (unsigned; the entry is by Kenneth J Scheller, Oct 17 2025):
  Conjecture: All numbers of the form 2*p with p prime and p > 5 belong to the sequence, and no other
  numbers greater than 36 do.  Empirically verified for k <= 100000.
The sequence has offset 1. As in the entry's programs (Mathematica: Tally of the list Mod[2k,m]/m,
then the number of values with multiplicity > 1 equals 2; Maple and Python: the set of repeated
values has two elements) and its examples, the fractions (2k mod m)/m for 1 ≤ m ≤ k are compared as
rational numbers, the value 0 counts like any other value, and k is a term when exactly two
distinct values occur at least twice in the list. repeatedValues k is that set of values.
-/

namespace OMA.S_oeis_a389863

/-- The fraction (2k mod m)/m as a rational number. -/
def fracVal (k m : ℕ) : ℚ := ((2 * k % m : ℕ) : ℚ) / (m : ℚ)

/-- The values that occur at least twice among fracVal k m for 1 ≤ m ≤ k. -/
def repeatedValues (k : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 k).image (fracVal k)).filter
    (fun v => 2 ≤ ((Finset.Icc 1 k).filter (fun m => fracVal k m = v)).card)

/-- k is a term of A389863: exactly two values occur more than once. -/
def InSeq (k : ℕ) : Prop := (repeatedValues k).card = 2

/-- The comment's conjecture: 2p is a term for every prime p > 5, and every term k > 36 has
this form. -/
theorem main : (∀ p : ℕ, p.Prime → 5 < p → InSeq (2 * p)) ∧
    (∀ k : ℕ, 36 < k → InSeq k → ∃ p : ℕ, p.Prime ∧ 5 < p ∧ k = 2 * p) := by
  sorry

end OMA.S_oeis_a389863
