import Mathlib

/-!
# A243927: Number of numbers in row n of the array at A243925.

Source: https://oeis.org/A243927
Credit: @agchua

Comment of A243927 (the entry is by Clark Kimberling, Jun 15 2014):
  Decree that (row 1) = (1). For n >=2, row n consists of numbers in increasing order generated
  as follows: x+1 for each x in row n-1 together with -2/x for each nonzero x in row n-1, where
  duplicates are deleted as they occur. The number of numbers in row n is A243927(n).
  Conjecture: every rational number occurs exactly once in the array.
As in the entry's Mathematica program, the candidates for row n are x+1 and -2/x (x nonzero) for
x in row n-1, and row n keeps the candidates that are in no earlier row. The order inside a row
plays no part in the claim, so a row is taken as a finite set of rationals. R k is the pair
(row k+1, union of rows 1 to k+1), and row n = (R (n-1)).1 for n >= 1. The claim is stated for
every rational number and the rows n >= 1.
-/

namespace OMA.S_oeis_a243927

/-- The candidates generated from a row: x+1 for each x, and -2/x for each nonzero x. -/
def cand (s : Finset ℚ) : Finset ℚ :=
  s.image (fun x => x + 1) ∪ (s.filter (fun x => x ≠ 0)).image (fun x => -2 / x)

/-- R k = (row k+1 of the array, the set of all numbers in rows 1 to k+1). -/
def R : ℕ → Finset ℚ × Finset ℚ
  | 0 => ({1}, {1})
  | k + 1 => (cand (R k).1 \ (R k).2, (R k).2 ∪ cand (R k).1)

/-- Row n of the array (n >= 1). -/
def row (n : ℕ) : Finset ℚ := (R (n - 1)).1

/-- Kimberling's conjecture: every rational number occurs in exactly one row n >= 1. -/
theorem main : ∀ r : ℚ, ∃! n : ℕ, 1 ≤ n ∧ r ∈ row n := by
  sorry

end OMA.S_oeis_a243927
