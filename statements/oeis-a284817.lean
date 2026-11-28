import Mathlib

/-!
# A284817: a(n) = 2n - 1 - A284776(n).

Source: https://oeis.org/A284817
Credit: @rickmanelius

Conjecture (R. J. Mathar, Jun 21 2025): a(n) = A189664(n-1).

Formalization notes:
* A284775 is the fixed point of the morphism 0 -> 01, 1 -> 0011 (`morph`; every letter other
  than 0 goes to 0011, and only the letters 0 and 1 occur). S(0) = 0 and S(k+1) is the image of
  S(k) under the morphism (`iter`), as in the program of the entry (iterates of 0). Both images
  begin with 0, so S(1) = 01 begins with S(0) = 0, each S(k) is an initial segment of S(k+1), and
  the fixed point is their limit. Its values 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, ... match
  the data of A284775.
* A284776(n) is the position of the n-th letter 0 of A284775, positions counted from 1 (offset 1
  of A284775) and the zeros counted in increasing order from n = 1 (offset 1 of A284776).
  `zeroPositions w` lists the positions of 0 in a finite word w, counted from 1, in increasing
  order, as Flatten[Position[s, 0]] in the program of the entry. For k ≥ 1 the word S(k) has as
  many letters 0 as letters 1 (each image does) and length at least 2^k, so S(n+1) has at least
  n zeros, and its n-th zero is the n-th zero of the fixed point: `A284776 n` reads it there.
  The values 1, 3, 4, 7, 9, 11, 12, 15, 16, 19, ... match the data of A284776.
* a(n) = 2n - 1 - A284776(n) is computed in the integers, so no subtraction is truncated. The
  values a(1), a(2), ... are 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, ..., matching the data.
* A189664 is the fixed point of the morphism 0 -> 010, 1 -> 001 (`morph3`) with offset 1.
  P(0) = 0 and P(k+1) is the image of P(k) (`iter3`); P(1) = 010 begins with P(0) = 0, so each
  P(k) is an initial segment of P(k+1), and P(k) has length 3^k. For m ≥ 1, term m of A189664 is
  letter m of P(m+1), counting from 1. The values for m = 1, 2, 3, ... are 0, 1, 0, 0, 0, 1, 0, 1,
  0, 0, 1, ..., matching its data.
* At n = 1 the conjecture reads a(1) = A189664(0). A189664 has offset 1, but its formula line
  sets a(0) = 0 (next to a(3k-2) = 0, a(3k-1) = 1 - a(k), a(3k) = a(k) for k ≥ 1), and
  `A189664 0` is defined as 0 accordingly. The conjecture is stated for every n ≥ 1, the offset of
  A284817; for n ≥ 2 only terms of A189664 inside its offset are used.
-/

namespace OMA.S_oeis_a284817

/-- The morphism 0 -> 01, 1 -> 0011 (every letter other than 0 goes to 0011). -/
def morph : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [0, 0, 1, 1]

/-- S(0) = 0 and S(k+1) = image of S(k) under the morphism. -/
def iter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (iter k).flatMap morph

/-- The positions of the letter 0 in the word w, counted from 1, in increasing order. -/
def zeroPositions (w : List ℕ) : List ℕ :=
  ((List.range w.length).filter (fun i => w.getD i 1 = 0)).map (· + 1)

/-- A284776(n) for n ≥ 1: the position of the n-th zero of A284775, read from S(n+1). -/
def A284776 (n : ℕ) : ℕ := (zeroPositions (iter (n + 1))).getD (n - 1) 0

/-- A284817(n) = 2n - 1 - A284776(n), in the integers. -/
def a (n : ℕ) : ℤ := 2 * (n : ℤ) - 1 - (A284776 n : ℤ)

/-- The morphism 0 -> 010, 1 -> 001 (every letter other than 0 goes to 001). -/
def morph3 : ℕ → List ℕ
  | 0 => [0, 1, 0]
  | _ => [0, 0, 1]

/-- P(0) = 0 and P(k+1) = image of P(k) under the morphism 0 -> 010, 1 -> 001. -/
def iter3 : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (iter3 k).flatMap morph3

/-- A189664(m): for m ≥ 1 letter m, counting from 1, of the fixed point of 0 -> 010, 1 -> 001,
read from P(m+1); A189664(0) = 0 as in the formula line of the entry. -/
def A189664 (m : ℕ) : ℕ := if m = 0 then 0 else (iter3 (m + 1)).getD (m - 1) 0

/-- Mathar's conjecture: a(n) = A189664(n-1) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (A189664 (n - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a284817
