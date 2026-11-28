import Mathlib

/-!
# A285358: Fixed point of the morphism 0 -> 10, 1 -> 1101.

Source: https://oeis.org/A285358
Credit: @rickmanelius

Conjecture (R. J. Mathar, May 08 2017): a(n) = A284929(n+1).

Formalization notes:
* The morphism sends 0 to 10 and 1 to 1101 (`morph`; every letter other than 0 goes to 1101, and
  only the letters 0 and 1 occur). Both images begin with 1, so the morphism has exactly one fixed
  point, the infinite word beginning with 1. Y(0) = 1 and Y(k+1) is the image of Y(k) under the
  morphism (`iter`); Y(1) = 1101 begins with Y(0) = 1, so each Y(k) is an initial segment of
  Y(k+1), and the fixed point is their limit. Y(k) has length at least 2^k, so letter n of the
  fixed point, counting from 1 as in the entry (offset 1), is letter n of Y(n), and `a n` reads it
  there. The values a(1), a(2), ... are 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, ..., matching the
  data.
* The program of the entry iterates the morphism from 0 instead. The image of 0 is 10, so iterate
  k+1 of 0 is Y(k) followed by iterate k of 0: it computes the same word.
* A284929 is the fixed point of the morphism 0 -> 01, 1 -> 1011 (`morph2`) beginning with 0, as in
  its data, its example 0 -> 01 -> 011011 -> ... and its program (iterates of 0). X(0) = 0 and
  X(k+1) is the image of X(k) (`iter2`); X(1) = 01 begins with X(0) = 0, so each X(k) is an initial
  segment of X(k+1), and X(k) has length at least 2^k. Term m of A284929 (offset 1) is letter m of
  X(m), read by `A284929 m`. The values for m = 1, 2, 3, ... are 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, ...,
  matching its data.
* The conjecture is stated for every n ≥ 1, the offset of A285358; then n + 1 ≥ 2 lies inside the
  offset of A284929.
-/

namespace OMA.S_oeis_a285358

/-- The morphism 0 -> 10, 1 -> 1101 (every letter other than 0 goes to 1101). -/
def morph : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [1, 1, 0, 1]

/-- Y(0) = 1 and Y(k+1) = image of Y(k) under the morphism. -/
def iter : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => (iter k).flatMap morph

/-- A285358(n) for n ≥ 1: letter n, counting from 1, of the fixed point, read from Y(n). -/
def a (n : ℕ) : ℕ := (iter n).getD (n - 1) 0

/-- The morphism 0 -> 01, 1 -> 1011 (every letter other than 0 goes to 1011). -/
def morph2 : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [1, 0, 1, 1]

/-- X(0) = 0 and X(k+1) = image of X(k) under the morphism 0 -> 01, 1 -> 1011. -/
def iter2 : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (iter2 k).flatMap morph2

/-- A284929(m) for m ≥ 1: letter m, counting from 1, of the fixed point of 0 -> 01, 1 -> 1011
beginning with 0, read from X(m). -/
def A284929 (m : ℕ) : ℕ := (iter2 m).getD (m - 1) 0

/-- Mathar's conjecture: a(n) = A284929(n+1) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = A284929 (n + 1) := by
  sorry

end OMA.S_oeis_a285358
