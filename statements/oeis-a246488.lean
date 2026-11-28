import Mathlib

/-!
# OEIS A246488: Gridgeman pairs

Source: https://oeis.org/A246488
Credit: @unserus

OEIS: "Gridgeman pairs in increasing order: pairs of palindromic primes which
differ only in their middle digits whose difference is equal to 1." and "It has
been conjectured by Norman T. Gridgeman that infinitely many pairs of such
primes exist."

Two palindromes that differ only in their middle digit, by 1, have the same odd
number `2k + 1` of decimal digits, and the larger is the smaller plus `10^k`. So
a Gridgeman pair is determined by its smaller member `p`: a palindromic prime
with `2k + 1` digits whose middle digit `(p / 10^k) % 10` is at most 8, such that
`p + 10^k` is prime (`p + 10^k` is then a palindrome with the same digits except
the middle one). Example: 181, 191 (k = 1); the one-digit pair is 2, 3 (k = 0).
The conjecture is that there are infinitely many such pairs.
-/

namespace OMA.S_oeis_a246488

/-- `p` is a palindrome in base 10. -/
def IsPalindrome (p : ℕ) : Prop := (Nat.digits 10 p).reverse = Nat.digits 10 p

/-- `p` is the smaller member of a Gridgeman pair. -/
def IsGridgemanLower (p : ℕ) : Prop :=
  ∃ k : ℕ, (Nat.digits 10 p).length = 2 * k + 1 ∧ IsPalindrome p ∧
    (p / 10 ^ k) % 10 < 9 ∧ p.Prime ∧ (p + 10 ^ k).Prime

/-- There are infinitely many Gridgeman pairs. -/
theorem main : {p : ℕ | IsGridgemanLower p}.Infinite := by
  sorry

end OMA.S_oeis_a246488
