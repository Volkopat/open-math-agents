import Mathlib

/-!
# A284948: 1-limiting word of the morphism 0 -> 10, 1 -> 00.

Source: https://oeis.org/A284948
Credit: @rickmanelius

Conjecture (R. J. Mathar, Jun 24 2025): a(n) = A096268(n-2), n>1.

Formalization notes:
* The morphism sends 0 to 10 and 1 to 00 (`morph`; every letter other than 0 goes to 00, and
  only the letters 0 and 1 occur). S(0) = 0 and S(k+1) is the image of S(k) under the morphism
  (`iter`), as in the comment of the entry: 0 -> 10 -> 0010 -> 10100010 -> 0010001010100010.
  S(k) has length 2^k.
* The comment says there are two limiting words, one with initial term 1 and one with initial
  term 0, the fixed points of the squared morphism 0 -> 0010, 1 -> 1010. The odd iterates S(1),
  S(3), S(5), ... begin with 1, and each one is an initial segment of the next (S(3) = 10100010
  begins with S(1) = 10, and applying the squared morphism keeps this), so they converge to the
  1-limiting word. (The even iterates begin with 0 and converge to the 0-limiting word, A328979.)
  The entry computes the sequence the same way, as the seventh iterate of 0. Letter n of the
  1-limiting word, counting from 1 as in the entry (offset 1), is letter n of S(2k+1) for every
  k with 2^(2k+1) ≥ n, so `a n` reads it from S(2n+1). The values a(1), a(2), ... are 1, 0, 1,
  0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, ..., matching the data.
* A096268 is the period-doubling word, the fixed point of the morphism 0 -> 01, 1 -> 00
  (`pdMorph`), with offset 0. T(0) = 0 and T(k+1) is the image of T(k) (`pdIter`); T(1) = 01
  begins with T(0) = 0, so each T(k) is an initial segment of T(k+1), and T(k) has length 2^k.
  Term m of A096268 (m ≥ 0) is letter m + 1 of T(k) for every k with 2^k > m, so `A096268 m`
  reads it from T(m+1). The values for m = 0, 1, 2, ... are 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0,
  ..., matching the data of A096268.
* The conjecture is stated for n > 1, as in the entry; then n - 2 is a natural number index
  (offset 0 of A096268) and the subtraction is exact.
-/

namespace OMA.S_oeis_a284948

/-- The morphism 0 -> 10, 1 -> 00 (every letter other than 0 goes to 00). -/
def morph : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 0]

/-- S(0) = 0 and S(k+1) = image of S(k) under the morphism. -/
def iter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (iter k).flatMap morph

/-- A284948(n) for n ≥ 1: letter n, counting from 1, of the 1-limiting word (the limit of the
odd iterates S(2k+1)), read from S(2n+1). -/
def a (n : ℕ) : ℕ := (iter (2 * n + 1)).getD (n - 1) 0

/-- The period-doubling morphism 0 -> 01, 1 -> 00 (every letter other than 0 goes to 00). -/
def pdMorph : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [0, 0]

/-- T(0) = 0 and T(k+1) = image of T(k) under the period-doubling morphism. -/
def pdIter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (pdIter k).flatMap pdMorph

/-- A096268(m) for m ≥ 0: letter m + 1 (term m, offset 0) of the period-doubling word, the fixed
point of 0 -> 01, 1 -> 00, read from T(m+1). -/
def A096268 (m : ℕ) : ℕ := (pdIter (m + 1)).getD m 0

/-- Mathar's conjecture: a(n) = A096268(n-2) for n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → a n = A096268 (n - 2) := by
  sorry

end OMA.S_oeis_a284948
