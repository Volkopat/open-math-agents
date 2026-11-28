import Mathlib

/-!
# A274000: Primes p of the form k^2 + 1 that divide 4^k - 1.

Source: https://oeis.org/A274000
Credit: @agchua

Comment of A274000 (the entry is by Jaroslav Krizek, Jun 06 2016):
  Conjecture: also primes p of the form n^2+1 such that divides (4^k)^n-1 for all k >= 0.
Offset 1, first terms 5, 17, 257, 65537, 148997. A prime p = k^2 + 1 determines k. The
conjecture says that the terms are also exactly the primes p = n^2 + 1 such that p divides
(4^k)^n - 1 for every k >= 0 (the entry's example: 17 = 4^2 + 1 divides (4^k)^4 - 1 for all
k >= 0). It is stated as a characterisation of the terms, for every natural number p.
-/

namespace OMA.S_oeis_a274000

/-- p is a term of A274000: a prime of the form k^2 + 1 that divides 4^k - 1. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∃ k : ℕ, p = k ^ 2 + 1 ∧ p ∣ 4 ^ k - 1

/-- The conjecture: the terms are exactly the primes p = n^2 + 1 such that p divides
(4^k)^n - 1 for all k >= 0. -/
theorem main : ∀ p : ℕ, IsTerm p ↔
    (p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1 ∧ ∀ k : ℕ, p ∣ (4 ^ k) ^ n - 1) := by
  sorry

end OMA.S_oeis_a274000
