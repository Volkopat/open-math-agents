import Mathlib

/-!
# A044140: Numbers k such that substring 02 occurs in the base-7 representation of k but not of k-1.

Source: https://oeis.org/A044140

Conjecture in the entry (Colin Barker, May 20 2019):
a(n) = a(n-1) + a(n-8) - a(n-9) for n>9.

Formalization notes:
* The sequence is defined by the name of the entry, not by the conjectured recurrence.
* The base-7 representation of k is `(Nat.digits 7 k).reverse`, written from the most
  significant digit, with no leading zeros (the representation of 0 is the empty list).
  The substring 02 occurs in it when the list [0, 2] is a contiguous sublist (`List.IsInfix`).
* `IsTerm k` says that 02 occurs in the representation of k but not in that of k - 1. The
  natural-number subtraction is harmless here: for k = 0 the substring does not occur in the
  representation of 0, so 0 is not a term.
* The terms are listed in increasing order with offset 1: `a n = Nat.nth IsTerm (n - 1)`,
  so a(1) = 51 is the least term. The set of terms is infinite (every number whose base-7
  representation is 102 followed by zeros is a term), so `Nat.nth` is the genuine
  enumeration. The junk value at n = 0 is never used: the claim is made only for
  n > 9, so the indices n - 1, n - 8 and n - 9 are at least 1.
* The values of a are natural numbers. The recurrence is stated in the integers, so that the
  subtraction of a(n-9) is the ordinary one.
* The same formula block of the entry also gives a conjectured generating function. It
  encodes this recurrence together with the first 9 terms, and it is not restated here.
-/

namespace OMA.S_oeis_a044140

/-- The substring 02 occurs in the base-7 representation of m. -/
def Has02 (m : ℕ) : Prop :=
  ([0, 2] : List ℕ).IsInfix (Nat.digits 7 m).reverse

/-- k is a term: 02 occurs in the base-7 representation of k but not of k - 1. -/
def IsTerm (k : ℕ) : Prop :=
  Has02 k ∧ ¬ Has02 (k - 1)

/-- A044140, offset 1: a(n) is the n-th number k such that 02 occurs in the base-7
representation of k but not of k - 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsTerm (n - 1)

/-- Barker's conjecture on A044140: a(n) = a(n-1) + a(n-8) - a(n-9) for n > 9. -/
theorem main :
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = (a (n - 1) : ℤ) + (a (n - 8) : ℤ) - (a (n - 9) : ℤ) := by
  sorry

end OMA.S_oeis_a044140
