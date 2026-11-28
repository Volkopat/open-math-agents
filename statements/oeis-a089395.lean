import Mathlib

/-!
# A089395: Prime productive numbers m: Let the digits of m be abcd. Then the numbers bcd*a+1, cd*ab+1, d*abc+1, abcd+1 etc. are all primes. If m is a k-digit number it produces k such primes.

Source: https://oeis.org/A089395
Credit: @luciusacarr

The entry records one conjecture: the sequence is infinite.

Reading of the source:
* For `m` with `k` decimal digits, the `k` numbers are `m + 1` and, for each way of cutting the
  digit string into a nonempty leading part and a nonempty trailing part of `i` digits
  (`1 ≤ i < k`), the product of the two parts plus one: `(m / 10^i) * (m % 10^i) + 1`.
  The trailing part may have leading zeros and is read as the number it denotes (502 is a term:
  5 * 02 + 1 = 11, 50 * 2 + 1 = 101 and 503 are prime).
* `m` ranges over the natural numbers (offset 0, first terms 1, 2, 4, 6, 12, 16, 22, ...); with
  this reading the terms below 5000 are exactly those listed in the entry.
-/

namespace OMA.S_oeis_a089395

/-- `m` is prime productive: `m + 1` is prime, and so is `(leading part) * (trailing part) + 1`
for every cut of the decimal digits of `m` into two nonempty parts. -/
def IsPrimeProductive (m : ℕ) : Prop :=
  (m + 1).Prime ∧
    ∀ i : ℕ, 1 ≤ i → i < (Nat.digits 10 m).length → ((m / 10 ^ i) * (m % 10 ^ i) + 1).Prime

theorem main : {m : ℕ | IsPrimeProductive m}.Infinite := by
  sorry

end OMA.S_oeis_a089395
