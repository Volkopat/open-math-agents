import Mathlib

/-!
# A288596: Fixed point of the mapping 00->0101, 10->1000, starting with 00.

Source: https://oeis.org/A288596
Credit: @agchua

Example section of A288596 (the entry is by Clark Kimberling, Jun 14 2017), after the list of
iterates 00, 0101, 010001, 0100001011, ..., verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate is given by A288599(n).
The entry's Mathematica program marks the same claim: Table[StringLength[w[n]], {n, 1, 35}]
(* A288599 conjectured *). The iterates are those of that program: w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0101, 10 -> 1000}]. StringReplace reads the word from the
left; at each position it replaces a block 00 or 10 that starts there and continues after the
block, and otherwise it keeps the letter and moves on by one. Words are lists of Booleans, the
letter 0 being false and the letter 1 being true.
A288599 (offset 0; data 2, 4, 6, 10, 16, 28, 50, 90, ...): its name line gives the initial values
a(0) = 2, a(1) = 4, a(2) = 6, a(3) = 10, a(4) = 16 and the recurrence a(n) = 2*a(n-1) - a(n-4);
since a(4) = 16 is given (while 2*a(3) - a(0) = 18), the recurrence applies from n = 5 on, which
is also what its g.f. -2*(-1 + x^2 + x^3 + x^4)/(1 - 2*x + x^4) and its listed data say. Values
are taken in the integers because of the subtraction. The n-th iterate is w(n), n >= 0, as
A288599 has offset 0 and A288599(0) = 2 is the length of the starting word 00.
-/

namespace OMA.S_oeis_a288596

/-- One application of the mapping 00 -> 0101, 10 -> 1000 (StringReplace, read from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: true :: false :: true :: step rest
  | true :: false :: rest => true :: false :: false :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A288599: a(0..4) = 2, 4, 6, 10, 16 and a(n) = 2*a(n-1) - a(n-4) for n >= 5. -/
def A288599 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 10
  | 4 => 16
  | n + 5 => 2 * A288599 (n + 4) - A288599 (n + 1)

/-- The conjecture: the n-th iterate has A288599(n) letters, for all n >= 0. -/
theorem main : ∀ n : ℕ, ((w n).length : ℤ) = A288599 n := by
  sorry

end OMA.S_oeis_a288596
