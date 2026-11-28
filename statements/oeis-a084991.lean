import Mathlib

/-!
# A084991: Palindromes which can be written as a sum of two prime numbers

Source: https://oeis.org/A084991
Credit: @xor2k

The entry's comment is a remark that partly mentions the Goldbach conjecture:
An odd palindrome k is in the sequence iff k-2 is prime. Assuming the Goldbach conjecture all even
palindromes > 2 are in the sequence.

Formalized claims (the Goldbach conjecture itself is NOT asserted; it only appears as the hypothesis
of the second, conditional claim):
1. for every odd palindrome `k`, `k` is in the sequence iff `k - 2` is prime;
2. if every even number `n > 2` is a sum of two primes (Goldbach), then every even palindrome
   `k > 2` is in the sequence.

Conventions: palindrome means decimal palindrome, i.e. the list `Nat.digits 10 k` is a
`List.Palindrome` (equivalently the base-10 representation reads the same backwards). Being in the
sequence means being a palindrome that equals `p + q` for primes `p`, `q` (not necessarily
distinct). `k - 2` is natural-number subtraction; for odd `k < 2`, i.e. `k = 1`, it gives `0`, which
is not prime, matching that `1` is not a sum of two primes.
-/

namespace OMA.S_oeis_a084991

/-- `k` is a decimal palindrome. -/
def IsPal (k : ℕ) : Prop :=
  List.Palindrome (Nat.digits 10 k)

/-- `k` is a term of A084991: a palindrome that is a sum of two primes. -/
def InSeq (k : ℕ) : Prop :=
  IsPal k ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = k

/-- Odd palindromes are terms iff `k - 2` is prime; and, assuming Goldbach, every even
palindrome `k > 2` is a term. -/
theorem main :
    (∀ k : ℕ, IsPal k → Odd k → (InSeq k ↔ (k - 2).Prime)) ∧
    ((∀ n : ℕ, Even n → 2 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) →
      ∀ k : ℕ, IsPal k → Even k → 2 < k → InSeq k) := by
  sorry

end OMA.S_oeis_a084991
