import Mathlib

/-!
# A288929: Fixed point of the mapping 00->1000, 10->10011, starting with 00.

Source: https://oeis.org/A288929
Credit: @agchua

Comment of A288929 (the entry is by Clark Kimberling, Jun 25 2017):
  Conjecture: The number of letters (0's and 1's) in the n-th iterate of the mapping is given by
  A192967(n+2) for n >= 0.
The iterates are those of the entry's Mathematica program and of its list of iterates (00, 1000,
100111000, ...): w(0) = 00 and w(n) = StringReplace[w(n-1), {00 -> 1000, 10 -> 10011}].
StringReplace reads the word from the left; at each position it replaces a block 00 or 10 that
starts there and continues after the block, and otherwise it keeps the letter and moves on by
one. Words are lists of Booleans, the letter 0 being false and the letter 1 being true.
A192967 (offset 0; data 1, 0, 2, 4, 9, 17, 31, 54, ...) is given by the formula of its entry
a(0) = 1, a(1) = 0, a(n) = a(n-1) + a(n-2) + n - 1 for n > 1 (Alex Ratushnyak, May 10 2012),
which reproduces its listed data; its name line defines it through a reduction of polynomials.
-/

namespace OMA.S_oeis_a288929

/-- One application of the mapping 00 -> 1000, 10 -> 10011 (StringReplace, read from the
left). -/
def step : List Bool → List Bool
  | false :: false :: rest => true :: false :: false :: false :: step rest
  | true :: false :: rest => true :: false :: false :: true :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A192967: a(0) = 1, a(1) = 0, a(n) = a(n-1) + a(n-2) + n - 1 for n > 1. -/
def A192967 : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => A192967 (n + 1) + A192967 n + (n + 1)

/-- The conjecture: the n-th iterate has A192967(n+2) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, (w n).length = A192967 (n + 2) := by
  sorry

end OMA.S_oeis_a288929
