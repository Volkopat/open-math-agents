import Mathlib

/-!
# A302864: the smallest palindrome with exactly `n` trailing binary zeros

Source: https://oeis.org/A302864
Credit: @avivorly

A302864 lists `a(n)`, the smallest positive palindromic number whose binary expansion ends in exactly `n` zeros, or `0`
if no such number exists. The entry adds: equivalently, `a(n)` is the smallest base-10 palindrome of the form
`(2k+1)*2^n`.

Conjecture (in the entry): a(n) > 0 for all n >= 0.

Conventions:
- Palindromic means palindromic in base 10 (the entry's keyword base and its equivalent form): `p` is a palindrome when
  the list of its decimal digits `Nat.digits 10 p` equals its own reverse. `Nat.digits` has no leading zeros, and the
  test is the same whichever end the list starts from.
- For `p > 0`, the binary expansion of `p` ends in exactly `n` zeros iff `2 ^ n ∣ p` and not `2 ^ (n + 1) ∣ p`, iff
  `p = (2k+1)*2^n` for some natural `k`: this is the entry's equivalent form.
- `Good n p` collects the conditions on `p`: positive, a palindrome, exactly `n` trailing binary zeros.
- `a n` is the least `p` with `Good n p` (`Nat.find`) when such a `p` exists, and `0` otherwise, as in the entry. So
  `0 < a n` says exactly that such a palindrome exists.
- The offset is `0`: `n` ranges over all of `ℕ`.
-/

namespace OMA.S_oeis_a302864

/-- `p` is a palindrome in base 10: its list of decimal digits is equal to its reverse. -/
def IsPal (p : ℕ) : Prop := (Nat.digits 10 p).reverse = Nat.digits 10 p

/-- `p` is a positive base-10 palindrome whose binary expansion ends in exactly `n` zeros. -/
def Good (n p : ℕ) : Prop := 0 < p ∧ IsPal p ∧ 2 ^ n ∣ p ∧ ¬ 2 ^ (n + 1) ∣ p

/-- A302864: the least `p` with `Good n p`, or `0` if there is none. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, Good n p then Nat.find h else 0

theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a302864
