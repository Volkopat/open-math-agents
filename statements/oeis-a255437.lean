import Mathlib

/-!
# A255437: In positive integers: replace k^2 with the first k odd numbers.

Source: https://oeis.org/A255437
Credit: @agchua

Comment of A255437 (unsigned; the entry is by Reinhard Zumkeller, Mar 23 2015):
  conjecture: a(A068722(n)) = (2*n+1)^2, i.e. A068722(n) = gives the position of the first
  occurrence of n-th odd square;
Offset of A255437: 1 (data 1, 2, 3, 1, 3, 5, 6, 7, 8, 1, 3, 5, 10, ...).
A068722 (offset 0): a(n) = (1+2*n+2*n^2) * (1+3*n+3*n^2), its formula line and the programs
of that entry (data 1, 35, 247, 925, ...).

Formalisation. blk m is the block that replaces the positive integer m: the first k odd numbers
1, 3, ..., 2k-1 if m = k^2, and m itself otherwise. pre M is the concatenation of the blocks of
1, 2, ..., M. Every block is nonempty, so pre n has at least n entries, and pre n is an initial
segment of the whole sequence; a(n) is the n-th entry of pre n. The n-th odd square, counted
from n = 0 as the offset of A068722 is 0, is (2*n+1)^2. The conjecture says that a(A068722(n))
is (2*n+1)^2 and that (2*n+1)^2 does not occur at any position i with 1 <= i < A068722(n).
-/

namespace OMA.S_oeis_a255437

/-- The block that replaces m: the first k odd numbers if m = k^2, and [m] otherwise. -/
def blk (m : ℕ) : List ℕ :=
  if Nat.sqrt m * Nat.sqrt m = m then (List.range (Nat.sqrt m)).map (fun j => 2 * j + 1)
  else [m]

/-- The concatenation of the blocks of 1, 2, ..., M. -/
def pre (M : ℕ) : List ℕ := (List.range M).flatMap (fun i => blk (i + 1))

/-- A255437(n) for n >= 1: the n-th entry of the concatenation of all blocks. -/
def a (n : ℕ) : ℕ := (pre n).getD (n - 1) 0

/-- A068722(n) = (1+2*n+2*n^2) * (1+3*n+3*n^2). -/
def A068722 (n : ℕ) : ℕ := (1 + 2 * n + 2 * n ^ 2) * (1 + 3 * n + 3 * n ^ 2)

/-- The conjecture: (2*n+1)^2 stands at position A068722(n) and at no earlier position. -/
theorem main : ∀ n : ℕ, a (A068722 n) = (2 * n + 1) ^ 2 ∧
    ∀ i : ℕ, 1 ≤ i → i < A068722 n → a i ≠ (2 * n + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a255437
