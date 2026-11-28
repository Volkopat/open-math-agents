import Mathlib

/-!
# A289035: Fixed point of the mapping 00->0010, 01->010, 10->010, starting with 00.

Source: https://oeis.org/A289035
Credit: @agchua

Comments of A289035 (Clark Kimberling, Jun 27 2017; Michel Dekking, Mar 20 2022), verbatim:
  Conjecture: the number of letters (0's and 1's) in the n-th iterate of the mapping is given by
  A289004.
  Conjecture: a(n) = A171588(n-3) for n>3.
The iterates are those of the entry's Mathematica program, whose first seven iterates the entry
lists (00, 0010, 0010010, 00100100100, 001001001000100100, ...): w(0) = 00 and
w(n) = StringReplace[w(n-1), {00 -> 0010, 01 -> 010, 10 -> 010}]. StringReplace reads the word from
the left; at each position it replaces a block 00, 01, or 10 that starts there and continues after
the block, and otherwise (a letter 1 followed by 1, or a single last letter) it keeps the letter
and moves on by one. Words are lists of Booleans, the letter 0 being false and the letter 1 being
true.
A289004 (offset 0) is defined in its entry by
a(n) = 2*a(n-1) - a(n-2) + 2*a(n-4) - a(n-5) + a(n-7) - a(n-8) - a(n-10) for n >= 10, with initial
values a(0..9) = 2, 4, 7, 11, 18, 31, 52, 89, 151, 257 (the entry's prose prints a(9) = 151,
a(9) = 257 for a(8) = 151, a(9) = 257, as confirmed by its data, generating function, and
LinearRecurrence program); its values are taken in the integers because of the subtraction.
A171588 (offset 1) is the Pell word, the fixed point of the morphism 0 -> 001, 1 -> 0 starting
with 0. Since the m-th iterate pellWord m is a prefix of all later iterates and has length at least
m for all m >= 1, its (m-1)-th letter gives A171588(m). The second conjecture states that for every
n > 3, the (n-1)-th letter of w(k) eventually equals A171588(n-3) (1-indexed, matching offset 1 of
A289035 and A171588). Both conjectures are stated together as a conjunction.
-/

namespace OMA.S_oeis_a289035

/-- One application of the mapping 00 -> 0010, 01 -> 010, 10 -> 010 (StringReplace, from the left). -/
def step : List Bool → List Bool
  | false :: false :: rest => false :: false :: true :: false :: step rest
  | false :: true :: rest => false :: true :: false :: step rest
  | true :: false :: rest => false :: true :: false :: step rest
  | x :: rest => x :: step rest
  | [] => []

/-- The n-th iterate of the mapping, starting with 00. -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- A289004: a(0..9) = 2, 4, 7, 11, 18, 31, 52, 89, 151, 257 and
a(n) = 2*a(n-1) - a(n-2) + 2*a(n-4) - a(n-5) + a(n-7) - a(n-8) - a(n-10) for n >= 10. -/
def A289004 : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 31
  | 6 => 52
  | 7 => 89
  | 8 => 151
  | 9 => 257
  | n + 10 =>
    2 * A289004 (n + 9) - A289004 (n + 8) + 2 * A289004 (n + 6) - A289004 (n + 5) +
      A289004 (n + 3) - A289004 (n + 2) - A289004 n

/-- One application of the Pell morphism 0 -> 001, 1 -> 0. -/
def pellStep : List Bool → List Bool
  | [] => []
  | false :: rest => false :: false :: true :: pellStep rest
  | true :: rest => false :: pellStep rest

/-- The m-th iterate of the Pell morphism starting with 0. -/
def pellWord : ℕ → List Bool
  | 0 => [false]
  | m + 1 => pellStep (pellWord m)

/-- A171588 (1-indexed): the m-th letter of the Pell word. -/
def A171588 (m : ℕ) : Bool :=
  (pellWord m).getD (m - 1) false

/-- The two conjectures of A289035: iterate lengths equal A289004, and the fixed point satisfies
a(n) = A171588(n-3) for all n > 3. -/
theorem main :
    (∀ n : ℕ, ((w n).length : ℤ) = A289004 n) ∧
    (∀ n : ℕ, 3 < n → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (w k)[n - 1]? = some (A171588 (n - 3))) := by
  sorry

end OMA.S_oeis_a289035
