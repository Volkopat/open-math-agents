import Mathlib

/-!
# A082769: a(n) = smallest palindromic prime that begins with A082768(n), or 0 if no such number exists.

Source: https://oeis.org/A082769
Credit: @gblacher2

Conjecture (comment in A082769): "no entry is zero."

A082768 (https://oeis.org/A082768) is "Numbers that begin with 1, 3, 7 or 9", with offset 1
and first terms `1, 3, 7, 9, 10, 11, 12, ...`.

Conventions:
* numbers are written in base 10;
* `p` *begins with* `m` when the decimal digits of `m` form an initial segment of those of `p`
  (the whole of `p` allowed, as in `a(2) = 3`); for `m ≥ 1` this is exactly `p / 10 ^ k = m`
  for some `k`, which is how `BeginsWith` is defined;
* a number belongs to A082768 when it begins, in the same sense, with one of the digits
  `1, 3, 7, 9`;
* a palindrome is a natural number whose list of decimal digits equals its reverse;
* an entry `a(n)` is zero exactly when no palindromic prime begins with `A082768(n)`. Since
  A082768 lists all of its members, "no entry is zero" is stated as: every member of A082768
  is the beginning of some palindromic prime.
-/

namespace OMA.S_oeis_a082769

/-- `p` begins with `m` in base 10: the decimal digits of `m` are an initial segment of those
of `p`. -/
def BeginsWith (p m : ℕ) : Prop :=
  ∃ k : ℕ, p / 10 ^ k = m

/-- `m` is a term of A082768: its decimal expansion begins with 1, 3, 7 or 9. -/
def InA082768 (m : ℕ) : Prop :=
  ∃ d ∈ ({1, 3, 7, 9} : Finset ℕ), BeginsWith m d

/-- `n` is a base-10 palindrome. -/
def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- The conjecture: no entry of A082769 is zero, i.e. every term of A082768 is the beginning of
some palindromic prime. -/
theorem main : ∀ m : ℕ, InA082768 m → ∃ p : ℕ, p.Prime ∧ IsPalindrome p ∧ BeginsWith p m := by
  sorry

end OMA.S_oeis_a082769
