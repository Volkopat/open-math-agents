import Mathlib

/-!
# A088288: Palindromic primes made of only two digits say a and b such that replacing a with b and vice versa one gets another prime.

Source: https://oeis.org/A088288
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. Its first terms are 131, 191, 313, 919,
113111311, 131333131, ... (131 and 313 are both members: swapping the digits 1 and 3 maps one to
the other).

Reading of the source:
* `n` is a term if it is prime, its decimal expansion is a palindrome, exactly two distinct digits
  `a ≠ b` occur in it, and the number obtained by replacing every digit `a` by `b` and every
  digit `b` by `a` is prime ("another prime": it differs from `n` since `a ≠ b`).
* The swapped number is read from the swapped digit string with `Nat.ofDigits`. (A leading digit
  becoming `0` cannot happen for a term: the swapped string is again a palindrome, so its last
  digit would be `0` too, and the number would not be prime.)
* With this reading the terms below `2 * 10^6` are exactly 131, 191, 313, 919, as listed.
-/

namespace OMA.S_oeis_a088288

/-- Replace each decimal digit `a` of `n` by `b` and each digit `b` by `a`. -/
def swapDigits (a b n : ℕ) : ℕ :=
  Nat.ofDigits 10 ((Nat.digits 10 n).map (fun d => if d = a then b else if d = b then a else d))

/-- `n` is a term of A088288. -/
def IsTerm (n : ℕ) : Prop :=
  n.Prime ∧ (Nat.digits 10 n).reverse = Nat.digits 10 n ∧
    ∃ a b : ℕ, a ≠ b ∧ (Nat.digits 10 n).toFinset = {a, b} ∧ (swapDigits a b n).Prime

theorem main : {n : ℕ | IsTerm n}.Finite := by
  sorry

end OMA.S_oeis_a088288
