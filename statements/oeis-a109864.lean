import Mathlib

/-!
# A109864: Least palindromic prime beginning with n, or 0 if no such prime exists.

Source: https://oeis.org/A109864
Credit: @agchua

Comment of A109864 (unsigned; the entry is by Amarnath Murthy, Jul 08 2005):
  Conjecture: a(n) = 0 if and only if n > 3 and n begins with 2,4,6,8 or 5 (most significant
  digit).
The sequence has offset 1, so the claim is stated for n >= 1. A number is a palindrome when its
list of decimal digits equals its reverse; m begins with n when the decimal digits of n, read from
the most significant one, are an initial segment of those of m (for a one-digit d, m begins with
d iff the most significant digit of m is d). a(n) is the least element of the set of palindromic
primes beginning with n, and 0 when that set is empty (sInf of the empty set of naturals is 0).
-/

namespace OMA.S_oeis_a109864

/-- m is a palindrome in base 10. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- The decimal representation of m begins with the decimal representation of n. -/
def BeginsWith (n m : ℕ) : Prop := (Nat.digits 10 n).reverse <+: (Nat.digits 10 m).reverse

/-- A109864(n): the least palindromic prime beginning with n, or 0 if there is none. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ IsPal p ∧ BeginsWith n p}

/-- The comment's conjecture: for n >= 1, a(n) = 0 iff n > 3 and the most significant digit of n
is 2, 4, 6, 8 or 5. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ (3 < n ∧ (BeginsWith 2 n ∨ BeginsWith 4 n ∨
    BeginsWith 6 n ∨ BeginsWith 8 n ∨ BeginsWith 5 n))) := by
  sorry

end OMA.S_oeis_a109864
