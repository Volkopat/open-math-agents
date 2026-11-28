import Mathlib

/-!
# OEIS A110408: a(n) is 0 exactly for palindromic primes and multiples of 3

Source: https://oeis.org/A110408 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Amarnath Murthy, Jul 30 2005; edited by T. D. Noe, Oct 30 2008), offset 0: Smallest prime
which is the repeated reverse concatenation of n followed by n (ending in n), where n == 1,3,7 or 9
(mod 10), or 0 if no such prime exists. Comment: Conjecture: a(n) is 0 iff n is a palindromic
prime == 1,3,7 or 9 (mod 10) and/or n ==0 (mod 3). As rev(n) followed by n is == 0 (mod 11), hence
every nonzero term contains at least two reverse concatenations of n followed by n.

Formalization notes:
* n is the number itself, with last digit 1, 3, 7 or 9, not the index of the term: the terms run
  over n = 1, 3, 7, 9, 11, 13, ... (a(1) = 0 belongs to n = 3, a(5) to n = 13).
* The numbers in question are rev(n) written m times followed by n, with m >= 1: the data give
  3131313131313131313113 for n = 13 and 71717117 for n = 17, and a(2) = 0 for n = 7 although 7
  is prime. `Nat.digits` lists digits from the least significant one, so the digit list of such a
  number is the digit list of n followed by m copies of the digit list of rev(n).
* a(n) is 0 when none of these numbers is prime. A palindromic prime is a prime n with
  rev(n) = n; and/or is the inclusive or.
* The last sentence of the comment is the reason given for m >= 2 in every prime found, not a
  further conjecture; it is not part of `main`.
* Control from the data that the proof file proves: for n = 17 the numbers with m = 1, 2 are
  composite and the one with m = 3 is the prime 71717117.
-/

namespace OMA.S_oeis_a110408

/-- The digit reversal of n. -/
def rev (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- The number whose decimal digits are those of rev(n) written m times, followed by those of n. -/
def F (n m : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n ++ (List.replicate m (Nat.digits 10 (rev n))).flatten)

/-- a(n) = 0: no number rev(n)...rev(n)n with at least one copy of rev(n) is prime. -/
def ZeroTerm (n : ℕ) : Prop := ∀ m, 1 ≤ m → ¬ (F n m).Prime

/-- Murthy's conjecture: for n with last digit 1, 3, 7 or 9, a(n) = 0 if and only if n is a
palindromic prime or a multiple of 3. -/
theorem main : ∀ n : ℕ, (n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9) →
    (ZeroTerm n ↔ ((n.Prime ∧ rev n = n) ∨ n % 3 = 0)) := by
  sorry

end OMA.S_oeis_a110408
