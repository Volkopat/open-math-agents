import Mathlib

/-!
# A085096: Index of the first occurrence of n in A082744, or 0 if n does not occur in the sequence A082744.

Source: https://oeis.org/A085096
Credit: @agchua

A082744(n) is the smallest k such that n*k + 1 is a palindrome (name line of A082744; offset 1,
data 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 10, 10, ...). Here k ranges over the positive integers, since
k = 0 would always give the palindrome 1. A085096 has offset 1.

Conjecture of A085096 (unsigned comment), verbatim:
  Conjecture: a(11) = 0, or in other words,if 11k+1 is a palindrome then at least one of the
  numbers in the sequence k+1,2k+1, 3k+1,...,10k+1 is also a palindrome.
Formalised with both of its forms: a(11) = 0, and for every k >= 1, if 11k+1 is a palindrome
in base 10, then jk+1 is a palindrome for some j with 1 <= j <= 10.
-/

namespace OMA.S_oeis_a085096

/-- m is a palindrome in base 10: its list of decimal digits equals its reverse. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- A082744(n): the smallest k >= 1 such that n*k + 1 is a palindrome. -/
noncomputable def A082744 (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ IsPal (n * k + 1)}

/-- A085096(n): the smallest index i >= 1 with A082744(i) = n, or 0 if there is none
(the infimum of the empty set of natural numbers is 0). -/
noncomputable def a (n : ℕ) : ℕ := sInf {i : ℕ | 1 ≤ i ∧ A082744 i = n}

/-- The conjecture in both of its forms: a(11) = 0, and if 11k+1 is a palindrome then one of
k+1, 2k+1, ..., 10k+1 is a palindrome. -/
theorem main : a 11 = 0 ∧
    ∀ k : ℕ, 1 ≤ k → IsPal (11 * k + 1) → ∃ j : ℕ, 1 ≤ j ∧ j ≤ 10 ∧ IsPal (j * k + 1) := by
  sorry

end OMA.S_oeis_a085096
