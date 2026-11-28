import Mathlib

/-!
# A288732: a(n) = a(n-1) + 2*a(n-4) - 2*a(n-5) for n >= 5, where a(0) = 2, a(1) = 4, a(2) = 6, a(3) = 8, a(4) = 10.

Source: https://oeis.org/A288732
Credit: @agchua

Comment of A288732 (the entry is by Clark Kimberling):
  Conjecture:  a(n) is the number of letters (0's and 1's) in the n-th iterate of the mapping
  00->1000, 10->01, starting with 00; see A288729.
Offset 0; the claim is stated for all n >= 0. The sequence is defined by its name line (values in
the integers because of the subtraction); it gives the listed terms 2, 4, 6, 8, 10, 14, 18, 22,
26, 34, ... The iterates are those of A288729 and its sibling entries (A288733, A288736,
A288741), whose Mathematica programs and lists of iterates start with w(0) = 00 and set
w(n) = StringReplace[w(n-1), {00 -> 1000, 10 -> 01}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise it keeps the letter and moves on by one. Words are lists of Booleans, the
letter 0 being false and the letter 1 being true.
-/

namespace OMA.S_oeis_a288732

/-- A288732: a(n) = a(n-1) + 2*a(n-4) - 2*a(n-5) for n >= 5, a(0..4) = 2, 4, 6, 8, 10. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | 4 => 10
  | n + 5 => a (n + 4) + 2 * a (n + 1) - 2 * a n

/-- One application of the mapping 00 -> 1000, 10 -> 01 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => true :: false :: false :: false :: step rest
  | true :: false :: rest => false :: true :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- The conjecture: a(n) is the number of letters of the n-th iterate, for all n >= 0. -/
theorem main : ∀ n : ℕ, a n = ((w n).length : ℤ) := by
  sorry

end OMA.S_oeis_a288732
