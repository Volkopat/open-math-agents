import Mathlib

/-!
# A185061: Position of the first occurrence of n in A193358 when it is considered to have the starting offset 1 instead of 0.

Source: https://oeis.org/A185061
Credit: @rickmanelius

Conjecture (Antti Karttunen, Jun 13 2013): Only odd numbers occur after 2.
(Chai Wah Wu, Jun 07 2016, in the entry: Conjecture is true.)

Formalization notes:
* A193358 (offset 0): a(0) = 1; a(1) = 2 and for n > 1: a(n) = a(n - a(n-2)) + 2. In `b`, the
  case a(n-2) = 0 returns 0 only so that the recursion is visibly well founded (the index
  n - a(n-2) is then below n); it never occurs, since every term is 1 or a term plus 2. The index
  n - a(n-2) uses natural number subtraction; in A193358 it is never negative (a(n-2) ≤ n).
  This `b` reproduces the 70 listed terms 1, 2, 4, 4, 3, 4, 6, 6, 6, 6, 5, 6, 8, ... of A193358.
* A185061(n), offset 1, is the position of the first occurrence of n in A193358 counted from 1:
  one plus the least m with A193358(m) = n (`a`, with `sInf`). This reproduces the 56 listed
  terms 1, 2, 5, 3, 11, 7, 19, 13, 29, 21, 41, ... of A185061 (checked by computer).
* The terms after 2 are a(n) for n ≥ 3 (a(2) = 2). A position is defined only when n occurs
  in A193358, so the statement assumes that n occurs (this guards against the junk value
  sInf of the empty set; the entry A193358 records that every positive integer occurs).
  Only odd numbers occur after 2 is stated as: for every n ≥ 3 that occurs in A193358, a(n) is odd.
-/

namespace OMA.S_oeis_a185061

/-- A193358: b(0) = 1, b(1) = 2 and b(n) = b(n - b(n-2)) + 2 for n > 1 (the guard b(n-2) = 0
never fires). -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => if h : b n = 0 then 0 else b (n + 2 - b n) + 2
decreasing_by all_goals omega

/-- A185061(n): one plus the least m with b(m) = n, the position of the first occurrence of n in
A193358 counted from 1. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | b m = n} + 1

/-- The conjecture: after the term a(2) = 2, every term is odd. -/
theorem main : ∀ n : ℕ, 3 ≤ n → (∃ m, b m = n) → Odd (a n) := by
  sorry

end OMA.S_oeis_a185061
