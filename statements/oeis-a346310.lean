import Mathlib

/-!
# A346310: Positions of words in A076478 such that #0's - #1's is even

Source: https://oeis.org/A346310
Credit: @jagong-cmu

Formalizes the conjecture stated in the OEIS entry (offset 1):
a(n) = A053738(n+1) - 1 for n >= 1.

Conventions:
* A076478 is the binary Champernowne sequence: the binary vectors of lengths 1, 2, 3, ...
  are concatenated, each length in numerical order. A word is a `List Bool`, with `true` for
  the digit 1 and `false` for the digit 0, most significant digit first. The vectors of
  length `L` are the `L`-digit binary expansions of `0, 1, ..., 2^L - 1`, in this order.
* The words are numbered from 1, as in the example of the entry: w(1) = 0, w(2) = 1,
  w(3) = 00, w(4) = 01, ... The list `wordsUpTo n` (all words of lengths 1..n) has
  `2^(n+1) - 2 >= n` entries, so `w n` is the `n`-th word for every `n >= 1`.
* The difference #0's - #1's is computed in `ℤ`.
* `a n` is the `n`-th position (offset 1) of a word with an even difference, and
  `A053738 n` is the `n`-th positive integer (offset 1) with an odd number of binary digits.
  Both are written with `Nat.nth`, which is indexed from 0. The subtraction `- 1` on `ℕ` is
  exact, since A053738 has only positive terms.
-/

namespace OMA.S_oeis_a346310

/-- The binary vectors of length `L` in numerical order: the `j`-th one is the `L`-digit
binary expansion of `j`, most significant digit first. -/
def vectors (L : ℕ) : List (List Bool) :=
  (List.range (2 ^ L)).map (fun j => (List.range L).reverse.map (fun i => j.testBit i))

/-- The words of A076478 of lengths `1, 2, ..., N`, in order. -/
def wordsUpTo (N : ℕ) : List (List Bool) :=
  (List.range' 1 N).flatMap vectors

/-- The `n`-th word of A076478, numbered from 1. -/
def w (n : ℕ) : List Bool :=
  (wordsUpTo n).getD (n - 1) []

/-- The position `n` holds a word with #0's - #1's even. -/
def EvenPos (n : ℕ) : Prop :=
  1 ≤ n ∧ Even (((w n).count false : ℤ) - ((w n).count true : ℤ))

/-- A346310, offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth EvenPos (n - 1)

/-- A053738, offset 1: numbers with an odd number of digits in binary. -/
noncomputable def A053738 (n : ℕ) : ℕ :=
  Nat.nth (fun k => Odd (Nat.digits 2 k).length) (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A053738 (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a346310
