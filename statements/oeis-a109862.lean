import Mathlib

/-!
# A109862: Palindromic primes p such that p's 10's complement is also a prime.

Source: https://oeis.org/A109862
Credit: @luciusacarr

The entry records one conjecture: the sequence is infinite. Its terms begin 3, 5, 7, 11, 191, 353,
383, 929, 10601, ... (353 is a term as 1000 - 353 = 647 is prime).

Reading of the source:
* The 10's complement of a number `p` with `L` decimal digits is `10^L - p`
  (`L = (Nat.digits 10 p).length`).
* `p` is a term if `p` is prime, its decimal expansion is a palindrome, and `10^L - p` is prime.
  With this reading the terms below `1.6 * 10^6` are exactly the listed ones.
-/

namespace OMA.S_oeis_a109862

/-- The 10's complement of `p`: `10^L - p`, where `L` is the number of decimal digits of `p`. -/
def tensComplement (p : ℕ) : ℕ := 10 ^ (Nat.digits 10 p).length - p

/-- `p` is a term of A109862. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ (Nat.digits 10 p).reverse = Nat.digits 10 p ∧ (tensComplement p).Prime

theorem main : {p : ℕ | IsTerm p}.Infinite := by
  sorry

end OMA.S_oeis_a109862
