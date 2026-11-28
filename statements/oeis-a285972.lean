import Mathlib

/-!
# A285972: {10->1}-transform of the Thue-Morse word A010060.

Source: https://oeis.org/A285972
Credit: @rickmanelius

Conjecture (R. J. Mathar, May 08 2017): a(n) = A285960(n-1).

Formalization notes:
* The Thue-Morse word A010060 has letters t(0), t(1), t(2), ... with t(i) the binary digit sum of
  i taken mod 2 (the formula a(n) = A000120(n) mod 2 of A010060), here `tm i` with Mathlib's
  `Nat.digits 2`. `tmWord L` is the list of its first L letters t(0), ..., t(L-1). It begins
  0110100110010110..., as in the example of the entry.
* The {10->1}-transform replaces each occurrence of 10 by 1, scanning from left to right as the
  StringReplace of the entry program does (`rep10`). Two occurrences of 10 never overlap, so the
  transform deletes exactly the letters 0 that come right after a letter 1. Whether a letter is
  deleted depends only on the letter before it, so the transform of the first L letters of the
  Thue-Morse word is an initial segment of the transform of the whole word. Each output letter uses
  at most two input letters, so the transform of the first 2n+2 letters has at least n+1 letters,
  and `a n` reads letter n of the transform there (counting from 1, offset 1). The values a(1),
  a(2), ... are 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, ..., matching the data.
* A285960 is the {01->1}-transform of the same word (`rep01`): each 01 is replaced by 1, which
  deletes exactly the letters 0 that come right before a letter 1. On the first L letters every
  output letter except possibly the last one is a letter of the transform of the whole word (the
  last input letter may be a 0 that the next letter 1 deletes). The transform of the first 2m+4
  letters has at least m+2 letters, so `A285960 m` reads letter m (offset 1) there. The values for
  m = 1, 2, 3, ... are 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, ..., matching its data.
* A285960 has offset 1 and its entry gives no term A285960(0), so A285960(n-1) is a term only for
  n ≥ 2, and the conjecture is stated for every n ≥ 2. (The first term a(1) = 0 is the first letter
  of the Thue-Morse word, which no letter 1 precedes.)
-/

namespace OMA.S_oeis_a285972

/-- The Thue-Morse word A010060: t(i) = binary digit sum of i, mod 2. -/
def tm (i : ℕ) : ℕ := (Nat.digits 2 i).sum % 2

/-- The first L letters t(0), ..., t(L-1) of the Thue-Morse word. -/
def tmWord (L : ℕ) : List ℕ := (List.range L).map tm

/-- Replace each 10 by 1, scanning from left to right. -/
def rep10 : List ℕ → List ℕ
  | 1 :: 0 :: w => 1 :: rep10 w
  | c :: w => c :: rep10 w
  | [] => []

/-- Replace each 01 by 1, scanning from left to right. -/
def rep01 : List ℕ → List ℕ
  | 0 :: 1 :: w => 1 :: rep01 w
  | c :: w => c :: rep01 w
  | [] => []

/-- A285972(n) for n ≥ 1: letter n, counting from 1, of the {10->1}-transform of the Thue-Morse
word, read from the transform of its first 2n+2 letters. -/
def a (n : ℕ) : ℕ := (rep10 (tmWord (2 * n + 2))).getD (n - 1) 0

/-- A285960(m) for m ≥ 1: letter m, counting from 1, of the {01->1}-transform of the Thue-Morse
word, read from the transform of its first 2m+4 letters. -/
def A285960 (m : ℕ) : ℕ := (rep01 (tmWord (2 * m + 4))).getD (m - 1) 0

/-- Mathar's conjecture: a(n) = A285960(n-1) for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = A285960 (n - 1) := by
  sorry

end OMA.S_oeis_a285972
