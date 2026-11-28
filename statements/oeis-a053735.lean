import Mathlib

/-!
# A053735: Sum of digits of (n written in base 3).

Source: https://oeis.org/A053735
Credit: @agchua

Example lines of A053735 (the entry is by Henry Bottomley, Mar 28 2000), verbatim:
  From Omar E. Pol, Feb 20 2010: (Start)
  This can be written as a triangle with row lengths A025192 (see the example in the entry
  A000120):
    0,
    1,2,
    1,2,3,2,3,4,
    1,2,3,2,3,4,3,4,5,2,3,4,3,4,5,4,5,6,
    1,2,3,2,3,4,3,4,5,2,3,4,3,4,5,4,5,6,3,4,5,4,5,6,5,6,7,2,3,4,3,4,5,4,5,6,3,...
  where the k-th row contains a(3^k+i) for 0<=i<2*3^k and converges to A173523 as k->infinity.
  (End) [Changed conjectures to statements in this entry. - Franklin T. Adams-Watters, Jul 02 2015]
A025192 (offset 0), name line: a(0)=1; a(n) = 2*3^(n-1) for n >= 1.
A173523 (offset 1), name line: 1+A053735(n-1), where A053735 is the sum-of-digits function in
base 3.

Formalisation. Offset 0: a(n) is the sum of the base-3 digits of n. The triangle is the sequence
read in rows of lengths A025192(0), A025192(1), ...: row r starts at position
rowStart(r) = A025192(0) + ... + A025192(r-1), and its entry i (0 <= i < A025192(r)) is
T(r, i) = a(rowStart(r) + i). The statement says
(1) the top row is 0, as displayed;
(2) the rows below it, row k+1 for k = 0, 1, 2, ... (the k-th row of the comment, which counts
the row 1,2 as k = 0), have 2*3^k entries and contain a(3^k+i) for 0 <= i < 2*3^k;
(3) the rows converge to A173523: for every n >= 1, from some row on, every row has an entry at
position n - 1 (counted from 0) and that entry equals A173523(n).
-/

namespace OMA.S_oeis_a053735

/-- A053735(n): the sum of the digits of n written in base 3. -/
def a (n : ℕ) : ℕ := (Nat.digits 3 n).sum

/-- A025192: a(0) = 1, a(n) = 2*3^(n-1) for n >= 1. -/
def A025192 : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * 3 ^ n

/-- The position at which row r of the triangle starts (rows of lengths A025192). -/
def rowStart (r : ℕ) : ℕ := ∑ q ∈ Finset.range r, A025192 q

/-- Entry i of row r of the triangle (0 <= i < A025192(r)). -/
def T (r i : ℕ) : ℕ := a (rowStart r + i)

/-- A173523(n) = 1 + A053735(n-1), offset 1. -/
def A173523 (n : ℕ) : ℕ := 1 + a (n - 1)

/-- The top row is 0; row k+1 has 2*3^k entries a(3^k+i), 0 <= i < 2*3^k; the rows converge to
A173523. -/
theorem main : T 0 0 = 0 ∧
    (∀ k : ℕ, A025192 (k + 1) = 2 * 3 ^ k ∧
      ∀ i : ℕ, i < 2 * 3 ^ k → T (k + 1) i = a (3 ^ k + i)) ∧
    ∀ n : ℕ, 1 ≤ n → ∃ K : ℕ, ∀ r : ℕ, K ≤ r →
      n - 1 < A025192 r ∧ T r (n - 1) = A173523 n := by
  sorry

end OMA.S_oeis_a053735
