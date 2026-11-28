import Mathlib

/-!
# A389221: Numbers k with exactly four coincident values among the fractions (2*k mod m)/m for 1 <= m <= k.

Source: https://oeis.org/A389221
Credit: @agchua

Comment of A389221 (unsigned; the entry is by Kenneth J Scheller, Oct 24 2025):
  Conjecture: All numbers of the form 4*p with p prime and p > 13 belong to the sequence, and no other
  numbers greater than 80 do.  Empirically verified through 100000.
The sequence has offset 1. As in the entry's programs (Mathematica: Tally of the list Mod[2k,m]/m,
then the number of values with multiplicity > 1 equals 4; Python: Fraction) and its examples, the
fractions (2k mod m)/m for 1 ≤ m ≤ k are compared as rational numbers, the value 0 counts like any
other value, and k is a term when exactly four distinct values occur at least twice in the list.
repeatedValues k is that set of values.
-/

namespace OMA.S_oeis_a389221

/-- The fraction (2k mod m)/m as a rational number. -/
def fracVal (k m : ℕ) : ℚ := ((2 * k % m : ℕ) : ℚ) / (m : ℚ)

/-- The values that occur at least twice among fracVal k m for 1 ≤ m ≤ k. -/
def repeatedValues (k : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 k).image (fracVal k)).filter
    (fun v => 2 ≤ ((Finset.Icc 1 k).filter (fun m => fracVal k m = v)).card)

/-- k is a term of A389221: exactly four values occur more than once. -/
def InSeq (k : ℕ) : Prop := (repeatedValues k).card = 4

/-- The comment's conjecture: 4p is a term for every prime p > 13, and every term k > 80 has
this form. -/
theorem main : (∀ p : ℕ, p.Prime → 13 < p → InSeq (4 * p)) ∧
    (∀ k : ℕ, 80 < k → InSeq k → ∃ p : ℕ, p.Prime ∧ 13 < p ∧ k = 4 * p) := by
  sorry

end OMA.S_oeis_a389221
