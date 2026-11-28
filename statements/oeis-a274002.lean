import Mathlib

/-!
# A274002: Primes p of the form (q-1)^2+1 that are a divisor of 4^(q-1)-1 where q is prime.

Source: https://oeis.org/A274002
Credit: @agchua

Comment of A274002 (unsigned; the entry is by Jaroslav Krizek, Jun 06 2016):
  Conjecture: also primes p of the form (q-1)^2+1, where q = prime, that are a divisor of
  (4^k)^(q-1)-1 for all k>=0.
The conjecture says that the terms of the sequence are exactly the primes p = (q-1)^2+1 with q
prime such that p divides (4^k)^(q-1)-1 for every k >= 0. It is stated as an equivalence for
every natural number p: p is a term of the sequence iff p has this second property.
-/

namespace OMA.S_oeis_a274002

/-- p is a term of A274002: p is a prime of the form (q-1)^2+1 with q prime, and p divides
4^(q-1)-1. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = (q - 1) ^ 2 + 1 ∧ p ∣ 4 ^ (q - 1) - 1

/-- The conjecture: the terms are exactly the primes p = (q-1)^2+1, q prime, that divide
(4^k)^(q-1)-1 for all k >= 0. -/
theorem main : ∀ p : ℕ, IsTerm p ↔
    (p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = (q - 1) ^ 2 + 1 ∧ ∀ k : ℕ, p ∣ (4 ^ k) ^ (q - 1) - 1) := by
  sorry

end OMA.S_oeis_a274002
