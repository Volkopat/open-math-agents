import Mathlib

/-!
# OEIS A158233: the products of consecutive terms of A120070 mod 9 are 0, 3, 4 or 6

Source: https://oeis.org/A158233 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Paul Curtz, Mar 14 2009), offset 1: a(n) = A120070(n+1)*A120070(n+2) mod 9. Comment:
Conjecture: this contains only the numbers 0,3,4,6 (verified for the first 5000 terms).
Entry A120070 (Wolfdieter Lang, Jul 20 2006), offset 2: Triangle of numbers used to compute the
frequencies of the spectral lines of the hydrogen atom. Formula: a(m,n) = m^2 - n^2 for m-1 >= n,
otherwise 0.

Formalization notes:
* A120070 is read by rows m = 2, 3, 4, ..., each row n = 1, ..., m-1 (the entry's triangle begins
  3; 8, 5; 15, 12, 7), with its offset 2: A120070(2) = 3, A120070(3) = 8, A120070(4) = 5. `pos i`
  is the position (m, n) of the term A120070(i + 2).
* The conjecture says that every term of A158233 is one of 0, 3, 4, 6.
* Controls: the definitions give A120070(2..12) = 3, 8, 5, 15, 12, 7, 24, 21, 16, 9, 35 and
  a(1..34) = 6, 4, 3, 0, 3, 6, 0, 3, 0, 0, 4, 0, 0, 4, 6, 0, 0, 6, 0, 6, 0, 0, 6, 3, 0, 3, 6, 3, 4,
  0, 0, 4, 0, 0, as in the entries.
-/

namespace OMA.S_oeis_a158233

/-- The position after (m, n) when reading the triangle by rows. -/
def next (mn : ℕ × ℕ) : ℕ × ℕ := if mn.2 + 1 < mn.1 then (mn.1, mn.2 + 1) else (mn.1 + 1, 1)

/-- Position (row m, column n) of the i-th term, i counted from 0. -/
def pos : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | i + 1 => next (pos i)

/-- A120070(i), with the entry's offset 2: A120070(2) = 3 is the first term. -/
def T (i : ℕ) : ℕ := (pos (i - 2)).1 ^ 2 - (pos (i - 2)).2 ^ 2

/-- A158233(n) = A120070(n+1) * A120070(n+2) mod 9. -/
def a (n : ℕ) : ℕ := T (n + 1) * T (n + 2) % 9

/-- Curtz's conjecture: every term is 0, 3, 4 or 6. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 ∨ a n = 3 ∨ a n = 4 ∨ a n = 6 := by
  sorry

end OMA.S_oeis_a158233
