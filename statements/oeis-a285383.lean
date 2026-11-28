import Mathlib

/-!
# A285383: Limiting 0-word of the morphism 0 -> 11, 1 -> 01.

Source: https://oeis.org/A285383
Credit: @rickmanelius

Conjecture (R. J. Mathar, May 08 2017): a(n) = A035263(n-1).

Formalization notes:
* The morphism sends 0 to 11 and 1 to 01 (`morph`; every letter other than 0 goes to 01, and
  only the letters 0 and 1 occur). S(0) = 0 and S(k+1) is the image of S(k) under the morphism
  (`iter`), as in the example of the entry: 0 -> 11 -> 0101 -> 11011101 -> 0101110101011101.
  S(k) has length 2^k.
* The even iterates S(0), S(2), S(4), ... begin with 0, and each one is an initial segment of the
  next (S(2) = 0101 begins with S(0) = 0, and applying the morphism keeps this), so they converge
  to an infinite word: the limiting 0-word. (The odd iterates begin with 1 and converge to the
  limiting 1-word, A285384.) Its letter n, counting from 1 as in the entry (offset 1), is letter
  n of S(2k) for every k with 4^k ≥ n, so `a n` reads it from S(2n). The values a(1), a(2), ...
  are 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, ..., matching the data.
* The name of A035263 gives it two ways: the trajectory of 1 under the morphism 0 -> 11,
  1 -> 10, and the parity of the 2-adic valuation of 2n, a(n) = A000035(A001511(n)). The
  statement uses the second, with Mathlib's `padicValNat 2`. The values for n = 1, 2, 3, ... are
  1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, ..., matching the data of A035263.
* A035263 has offset 1, so A035263(n-1) is one of its terms for n ≥ 2. At n = 1 the conjecture
  reads a(1) = A035263(0). The entry A035263 extends the sequence by a(0) = 0 (Michael Somos,
  Sep 04 2006: a(-n) = a(n), a(0) = 0), and the definition below also gives 0 at 0 (Mathlib has
  `padicValNat 2 0 = 0`). The conjecture is stated for every n ≥ 1, the offset of A285383; for
  n ≥ 2 only terms of A035263 inside its offset are used.
-/

namespace OMA.S_oeis_a285383

/-- The morphism 0 -> 11, 1 -> 01 (every letter other than 0 goes to 01). -/
def morph : ℕ → List ℕ
  | 0 => [1, 1]
  | _ => [0, 1]

/-- S(0) = 0 and S(k+1) = image of S(k) under the morphism. -/
def iter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (iter k).flatMap morph

/-- A285383(n) for n ≥ 1: letter n, counting from 1, of the limiting 0-word (the limit of the
even iterates S(2k)), read from S(2n). -/
def a (n : ℕ) : ℕ := (iter (2 * n)).getD (n - 1) 0

/-- A035263(n): the parity of the 2-adic valuation of 2n, A000035(A001511(n)). -/
def A035263 (n : ℕ) : ℕ := padicValNat 2 (2 * n) % 2

/-- Mathar's conjecture: a(n) = A035263(n-1) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = A035263 (n - 1) := by
  sorry

end OMA.S_oeis_a285383
