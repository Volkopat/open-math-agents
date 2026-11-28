import Mathlib

/-!
# A269018: Primes p of the form 2^k + 2*(-1)^k - 1.

Source: https://oeis.org/A269018
Credit: @agchua

Comment of A269018 (unsigned; the entry is by Jaroslav Krizek, Feb 17 2016):
  Conjecture: union of {2}, {A019434(n) for n > 1} and {A176680(n)}.
Here A019434 is the sequence of Fermat primes (Fermat primes: primes of the form 2^(2^k) + 1, for
some k >= 0; offset 1, listed in increasing order), so A019434(1) = 3 and the terms A019434(n) for
n > 1 are exactly the Fermat primes other than 3. A176680 is the sequence of primes p == 2 (mod 3)
of the form 2^n - 3.

Formalisation. In A269018, k runs over the natural numbers (the entry lists the values
k = 0, 2, 3, 4, 5, 8, 9, 16, ...), and 2^k + 2*(-1)^k - 1 is computed in the integers (for k = 1
it is -1). The three sets of the comment are given by their defining properties. The conjecture
says that a natural number p is a term of A269018 if and only if p lies in their union.
-/

namespace OMA.S_oeis_a269018

/-- p is a term of A269018: p is prime and p = 2^k + 2*(-1)^k - 1 for some k >= 0. -/
def IsTerm (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k : ℕ, (p : ℤ) = 2 ^ k + 2 * (-1) ^ k - 1

/-- p is a Fermat prime, that is, a term of A019434. -/
def IsFermatPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1

/-- p is a term of A176680: a prime p == 2 (mod 3) of the form 2^n - 3. -/
def IsA176680 (p : ℕ) : Prop :=
  Nat.Prime p ∧ p % 3 = 2 ∧ ∃ n : ℕ, (p : ℤ) = 2 ^ n - 3

/-- The conjecture: A269018 is the union of {2}, the Fermat primes other than A019434(1) = 3,
and A176680. -/
theorem main : ∀ p : ℕ, IsTerm p ↔ (p = 2 ∨ (IsFermatPrime p ∧ p ≠ 3) ∨ IsA176680 p) := by
  sorry

end OMA.S_oeis_a269018
