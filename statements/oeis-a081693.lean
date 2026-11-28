import Mathlib

/-!
# OEIS A081693: B_n is the position of the n-th 1 in the fixed point of 0 -> 01, 1 -> 0000

Source: https://oeis.org/A081693 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 02 2003), offset 0: Define two sequences by A_n = mex{A_i,B_i : 0 <= i
< n}, B_n = B_{n-1} + (A_n-A_{n-1})(A_n-A_{n-1}+1), where the mex of a set is the smallest
nonnegative integer not in the set. Sequence gives B_n. A_n is in A081692.
Conjecture: Except for the initial 0, this is the sequence of positions of 1 in the fixed point of
the morphism 0->01, 1->0000; see A284683. - Clark Kimberling, Apr 13 2017
Data: 0, 2, 8, 10, 12, 14, 16, 22, 28, 34, 40, 46, ...
A284683 (Clark Kimberling, Apr 13 2017), offset 1: Fixed point of the morphism 0 -> 01, 1 -> 0000.
Data: 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, ...

Formalization notes:
* `IsSolution A B` states the defining conditions of the pair: A_n is the mex (the infimum of the
  natural numbers that are neither an A_i nor a B_i for i < n, a nonempty set, so the smallest
  of them), B_0 = 0 (the initial 0 of the data; the recursion for B starts at n = 1), and the
  recursion for B for n >= 1. These conditions determine A_n and B_n one after the other, so
  exactly one pair satisfies them, the pair of the entry, and `main` is stated for every pair that
  satisfies them. The data show that A is increasing, so the differences A_n - A_(n-1) in the
  natural numbers are the differences of the entry.
* `sig` applies the morphism 0 -> 01, 1 -> 0000 letter by letter, and `sigIter n` is its n-th
  power applied to 0. As 01 begins with 0, `sigIter n` is a prefix of `sigIter (n + 1)`, and it
  has at least n + 1 letters, so `w i`, letter i of `sigIter (i + 1)`, is letter i of the fixed
  point: `w` is A284683, indexed from 0.
* `pos1 n` adds 1 to the 0-based index of the n-th 1 of `w`, so positions count from 1 as in
  A284683 (`Nat.nth` counts its argument from 0). Except for the initial 0 means for n >= 1.
-/

namespace OMA.S_oeis_a081693

/-- The defining conditions of the pair (A, B) = (A081692, A081693): A_n is the smallest natural
number that is not an A_i or a B_i with i < n, B_0 = 0, and
B_n = B_(n-1) + (A_n - A_(n-1)) (A_n - A_(n-1) + 1) for n >= 1. -/
def IsSolution (A B : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, A n = sInf {m : ℕ | ∀ i < n, A i ≠ m ∧ B i ≠ m}) ∧ B 0 = 0 ∧
    ∀ n : ℕ, 1 ≤ n → B n = B (n - 1) + (A n - A (n - 1)) * (A n - A (n - 1) + 1)

/-- The morphism 0 -> 01, 1 -> 0000, applied letter by letter (other letters are copied). -/
def sig : List ℕ → List ℕ
  | 0 :: l => 0 :: 1 :: sig l
  | 1 :: l => 0 :: 0 :: 0 :: 0 :: sig l
  | x :: l => x :: sig l
  | [] => []

/-- The images of 0 under the powers of the morphism: 0, 01, 010000, ... -/
def sigIter : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => sig (sigIter n)

/-- A284683 (0-indexed): the fixed point of the morphism; its letter i is read off the (i + 1)-th
image of 0. -/
def w (i : ℕ) : ℕ := (sigIter (i + 1)).getD i 0

/-- The position, counted from 1, of the n-th 1 of A284683. -/
noncomputable def pos1 (n : ℕ) : ℕ := Nat.nth (fun i => w i = 1) (n - 1) + 1

/-- Kimberling's conjecture: except for the initial 0, B_n is the position of the n-th 1 in the fixed
point of 0 -> 01, 1 -> 0000. -/
theorem main : ∀ A B : ℕ → ℕ, IsSolution A B → ∀ n : ℕ, 1 ≤ n → B n = pos1 n := by
  sorry

end OMA.S_oeis_a081693
