import Mathlib

/-!
# A147296: a(n) = n*(9*n+2).

Source: https://oeis.org/A147296
Credit: @agchua

M. F. Hasler (Mar 01 2009), in the formula section of A147296:
  a(n) = n*(9*n + 2), as conjectured by V. Librandi.

Paul Curtz (Nov 05 2008) created the entry as a decimation of A144454; its cross-reference line
says: Equals first 9-fold decimation of A144454. V. Librandi conjectured (SeqFan list, March 2009,
linked from the entry) that these terms are n*(9*n+2), and the name of the entry now records that
formula. Read with the name as definition the claim would be a tautology, so it is stated here for
the sequence as defined by the cross-reference line: a(n) = A144454(9n+1) for n >= 0 (offset 0;
A144454 has offset 1, and A144454(1), A144454(10), A144454(19), ... = 0, 11, 40, ... are the data
of A147296). A144454(n) = A061039(3n) (A144454 is the first trisection of A061039, which has
offset 3), and A061039(n) is the numerator of 1/9 - 1/n^2 (the name of A061039). The numerator of
a rational number is taken in lowest terms (`Rat.num`).
-/

namespace OMA.S_oeis_a147296

/-- A061039(n): the numerator of 1/9 - 1/n^2. -/
def A061039 (n : ℕ) : ℤ := ((1 : ℚ) / 9 - 1 / (n : ℚ) ^ 2).num

/-- A144454(n) = A061039(3n): the first trisection of A061039. -/
def A144454 (n : ℕ) : ℤ := A061039 (3 * n)

/-- A147296(n) as the first 9-fold decimation of A144454: a(n) = A144454(9n+1). -/
def a (n : ℕ) : ℤ := A144454 (9 * n + 1)

/-- Librandi's conjecture: a(n) = n*(9n+2) for all n >= 0. -/
theorem main : ∀ n : ℕ, a n = (n : ℤ) * (9 * n + 2) := by
  sorry

end OMA.S_oeis_a147296
