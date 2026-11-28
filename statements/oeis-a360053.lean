import Mathlib

/-!
# A360053: Primes p such that each prime < p in the prime factorization of 2^(p-1) - 1 has exponent 1.

Source: https://oeis.org/A360053
Credit: @azmiozgen

Conjecture (from the entry): 2^(a(n)-1) - 1 is always squarefree.

Formalization notes:
* p is a term when p is prime and no prime q < p has q^2 dividing 2^(p-1) - 1 (a prime q < p that
  does not divide it has exponent 0, which is allowed).
* Stated as: for every term p, 2^(p-1) - 1 is squarefree (in particular p itself is not a
  Wieferich prime).
* Controls (computed): the terms begin 2, 3, 5, 11, 17, 23, 29, 47, 53, 59, 71, 83, 89, as in the
  entry (1093 and 3511 are not terms), and 2^(p-1) - 1 is squarefree for each of these 13.
-/

namespace OMA.S_oeis_a360053

/-- `p` is a term of A360053. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∀ q : ℕ, q.Prime → q < p → ¬ q ^ 2 ∣ 2 ^ (p - 1) - 1

/-- For every term `p`, `2^(p-1) - 1` is squarefree. -/
theorem main : ∀ p : ℕ, IsTerm p → Squarefree (2 ^ (p - 1) - 1) := by
  sorry

end OMA.S_oeis_a360053
