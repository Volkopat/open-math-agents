import Mathlib

/-!
# A109733: Sequence is its own base-10 ASCII representation.

Source: https://oeis.org/A109733
Credit: @agchua

Formula line of A109733 (conjecture by Jonathan Cross, Oct 14 2005):
  I conjecture that a(n) = 53 when n is congruent to 1, 3 or 5 (mod 8) and a(n) = 51 when n is
  congruent to 2 (mod 8).
Offset 1, data 53, 51, 53, 49, 53, 51, 52, 57, ... The ASCII code of the decimal digit d is 48 + d.
Write the terms a(1), a(2), a(3), ... in decimal one after the other, without separators; the
sequence is its own base-10 ASCII representation: for every n >= 1, a(n) is the ASCII code of the
n-th digit of this string. Below, digitString a n is the list of the decimal digits of a(1), ...,
a(n), written one after the other. Every term is at least 48, so this list has at least n entries
and its entry n - 1 (counting from 0) is the n-th digit of the whole string.
The statement says that such a sequence exists, and that every such sequence satisfies the
conjecture for every n >= 1 (the property determines the sequence).
-/

namespace OMA.S_oeis_a109733

/-- The decimal digits of a(1), a(2), ..., a(n), most significant digit first, written one after
the other. -/
def digitString (a : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => digitString a n ++ (Nat.digits 10 (a (n + 1))).reverse

/-- a is its own base-10 ASCII representation: for every n >= 1, a(n) = 48 + (the n-th decimal
digit of the string a(1) a(2) a(3) ...). -/
def SelfASCII (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n = 48 + (digitString a n).getD (n - 1) 0

/-- The conjecture: a sequence that is its own base-10 ASCII representation exists, and every
such sequence has a(n) = 53 for n = 1, 3, 5 (mod 8) and a(n) = 51 for n = 2 (mod 8). -/
theorem main : (∃ a : ℕ → ℕ, SelfASCII a) ∧
    ∀ a : ℕ → ℕ, SelfASCII a → ∀ n : ℕ, 1 ≤ n →
      ((n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5) → a n = 53) ∧ (n % 8 = 2 → a n = 51) := by
  sorry

end OMA.S_oeis_a109733
