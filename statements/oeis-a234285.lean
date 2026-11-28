import Mathlib

/-!
# A234285: Positive odd numbers n such that sigma(m) - 2m is never equal to n, where sigma(.) is the sum of divisors function A000203. Conjectural.

Source: https://oeis.org/A234285
Credit: @agchua

The problem text is the comment block of the entry by Farideh Firoozbakht, Jan 12 2014:
  1. Mersenne primes are not in this sequence. Because if M=2^p-1 is prime then M=sigma(m)-2m, where
  m=2^(p-1)*(2^p-1)^2=(1/2)*(M+1)*M^2 (please see Proposition 2.1 of Firoozbakht-Hasler, 2010).
  2. If M = 2^p - 1 is a Mersenne prime then M^2 + 3M + 1 = 4^p + 2^p - 1 is not in the sequence.
  Because M^2 + 3M + 1 = sigma(m) - 2m where m = M^3 + M^2 = 2^p(2^p-1)^2 (please see
  Proposition 2.5, op. cit.).
  3. Note that if r is an even number and if for a number k p = 2^k - r - 1 is an odd prime then
  r = sigma(m) - 2m where m = 2^(k-1)*p.
  Namely r is not in the sequence (see Theorem 1.1, op. cit.).
  It seems that for each even number r, there exists at least one odd prime of the form 2^k - r - 1.
  Moreover I conjecture that, for each even number r, there exist infinitely many primes p of the
  form 2^k - r - 1, or equivalently, I conjecture that: For each odd number s, there exists
  infinitely many primes p of the form 2^k - s.
The five claims are stated together, in this order. The offset of the sequence is 1.
The fifth claim, the conjecture proper, is stated in its first form: for each even integer r the
set of primes of the form 2^k - r - 1 is infinite. Its second form is the same statement with
s = r + 1 (the entry's special cases s = -1, -3, -5 show that s and r range over all integers).
IsTerm n says that n is a term: n is a positive odd number and sigma(m) - 2m differs from n for
every positive integer m (computed in the integers); sigma is ArithmeticFunction.sigma 1.
In claim 3 the number k is at least 1, since m = 2^(k-1)*p must be an integer; r ranges over all
even integers, as in the entry, where r = sigma(m) - 2m can be negative.
-/

namespace OMA.S_oeis_a234285

/-- n is a term of A234285: a positive odd number that is never equal to sigma(m) - 2m. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ Odd n ∧
    ∀ m : ℕ, 0 < m → (ArithmeticFunction.sigma 1 m : ℤ) - 2 * (m : ℤ) ≠ (n : ℤ)

/-- The five claims of the comment block of Farideh Firoozbakht (Jan 12 2014). -/
theorem main :
    (∀ p : ℕ, Nat.Prime (2 ^ p - 1) → ¬ IsTerm (2 ^ p - 1)) ∧
    (∀ p : ℕ, Nat.Prime (2 ^ p - 1) →
      ((2 : ℕ) ^ p - 1) ^ 2 + 3 * (2 ^ p - 1) + 1 = 4 ^ p + 2 ^ p - 1 ∧
        ¬ IsTerm ((2 ^ p - 1) ^ 2 + 3 * (2 ^ p - 1) + 1)) ∧
    (∀ r : ℤ, ∀ k p : ℕ, Even r → 1 ≤ k → p.Prime → Odd p → (p : ℤ) = 2 ^ k - r - 1 →
      r = (ArithmeticFunction.sigma 1 (2 ^ (k - 1) * p) : ℤ) - 2 * ((2 ^ (k - 1) * p : ℕ) : ℤ)) ∧
    (∀ r : ℤ, Even r → ∃ k q : ℕ, q.Prime ∧ Odd q ∧ (q : ℤ) = 2 ^ k - r - 1) ∧
    (∀ r : ℤ, Even r → Set.Infinite {q : ℕ | q.Prime ∧ ∃ k : ℕ, (q : ℤ) = 2 ^ k - r - 1}) := by
  sorry

end OMA.S_oeis_a234285
