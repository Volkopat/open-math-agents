import Mathlib

/-!
# A136162: List of prime quadruplets {p, p+2, p+6, p+8}.

Source: https://oeis.org/A136162
Credit: @agchua

Comment of A136162 by Jaroslav Krizek, Jul 07 2017, verbatim:
  {11, 13, 17, 19} is the only prime quadruplet {p, p+2, p+6, p+8} of the form
  {Q-4, Q-2, Q+2, Q+4} where Q is a product of a pair of twin primes {q, q+2} (for prime q = 3)
  because numbers Q-2 and Q+4 are for q>3 composites of the form 3*(12*k^2-1) and 3*(12*k^2+1)
  respectively (k is an integer). Conjecture: {11, 13, 17, 19} is the only prime quadruplet
  {p, p+2, p+6, p+8} of the form {q*(nextprime(q))-4, q*( nextprime(q))-2, q*( nextprime(q))+2,
  q*( nextprime(q))+4} where q is a prime (for prime q = 3).
The first claim is proved in the comment itself (the argument mod 3 quoted above).

Formalisation. A prime quadruplet {p, p+2, p+6, p+8} of the form {Q-4, Q-2, Q+2, Q+4} is the one
with p = Q-4. First part: Q = q*(q+2) with q and q+2 twin primes. Second part: Q = q*r with q a
prime and r = nextprime(q), the next prime after q (r is prime, q < r, and no prime lies strictly
between q and r). Each part says: p = Q-4 starts a prime quadruplet if and only if q = 3, which
gives Q = 15 and the quadruplet {11, 13, 17, 19}. In both parts Q >= 6, so the natural-number
subtraction Q-4 is exact.
-/

namespace OMA.S_oeis_a136162

/-- p, p+2, p+6, p+8 are all prime: {p, p+2, p+6, p+8} is a prime quadruplet. -/
def IsPrimeQuad (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime

/-- {11, 13, 17, 19} (the case q = 3) is the only prime quadruplet {Q-4, Q-2, Q+2, Q+4}, both for
Q = q*(q+2) with twin primes q, q+2 and for Q = q*nextprime(q) with q prime. -/
theorem main :
    (∀ q : ℕ, q.Prime → (q + 2).Prime → (IsPrimeQuad (q * (q + 2) - 4) ↔ q = 3)) ∧
    (∀ q r : ℕ, q.Prime → r.Prime → q < r → (∀ m : ℕ, q < m → m < r → ¬ m.Prime) →
      (IsPrimeQuad (q * r - 4) ↔ q = 3)) := by
  sorry

end OMA.S_oeis_a136162
