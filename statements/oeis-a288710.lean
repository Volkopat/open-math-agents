import Mathlib

/-!
# A288710: 0-limiting word of the mapping 00->1000, 10->0001, starting with 00.

Source: https://oeis.org/A288710
Credit: @agchua

Comment of A288710 (the entry is by Clark Kimberling, Jun 2017), verbatim:
  The 0-limiting word is the limit of the n-th iterates for n == 0 mod 2.
  Conjecture:  the number of letters (0's and 1's) in the n-th iterate is given by A288925(n),
  for n >= 0.
The iterates are those of the entry's Mathematica program, whose first iterates the entry lists
(00, 1000, 00011000, 10000100011000, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 1000, 10 -> 0001}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise it keeps the letter and moves on by one. Words are lists of Booleans, the
letter 0 being false and the letter 1 being true. A288925 (offset 0) is defined in its entry by
a(n) = a(n-1) + a(n-2) + 3*a(n-4) - 2*a(n-5) for n >= 5, where a(0) = 2, a(1) = 4, a(2) = 8,
a(3) = 13, a(4) = 26; its values are taken in the integers because of the subtraction.
-/

namespace OMA.S_oeis_a288710

/-- One application of the mapping 00 -> 1000, 10 -> 0001 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => true :: false :: false :: false :: step rest
  | true :: false :: rest => false :: false :: false :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288925. -/
def A288925 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 13
  | 4 => 26
  | n + 5 => A288925 (n + 4) + A288925 (n + 3) + 3 * A288925 (n + 1) - 2 * A288925 n

/-- The conjecture: the n-th iterate has A288925(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288925 n := by
  sorry

end OMA.S_oeis_a288710
