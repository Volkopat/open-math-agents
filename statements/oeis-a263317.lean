import Mathlib

/-!
# A263317: Least prime p > n such that the numbers sigma(k^2)/k^2 (k = 1,...,n) are pairwise incongruent modulo p, where sigma(m) is the sum of the divisors of m.

Source: https://oeis.org/A263317
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A263317 (Zhi-Wei Sun, Oct 14 2015): a(n) exists for any
n > 0, and a(n) < n^2 for all n > 2.

Conventions:
* The sequence has offset 1 (data 2, 5, 5, 7, 7, 29, 37, 37, 37, 37, 37, 43, ...).
* sigma(m) is the sum of the divisors of m, written as the sum over `Nat.divisors m`. For a prime
  p > n and 1 <= k <= n the rational number sigma(k^2)/k^2 has a denominator prime to p, and its
  residue modulo p is `s p k`, the residue of sigma(k^2) times the inverse of that of k^2 in
  `ZMod p`. `Pairwise incongruent modulo p` for k = 1, ..., n is injectivity of `s p` on
  `Finset.Icc 1 n` (helper `Good`).
* `a(n) exists` is the existence of a prime p > n with `Good n p`; `a(n) < n^2` for the least such
  prime is equivalent to the existence of such a prime below n^2. Both assertions are formalized,
  as a conjunction.
-/

namespace OMA.S_oeis_a263317

/-- The residue modulo p of the rational number sigma(k^2)/k^2 (for p not dividing k). -/
def s (p k : ℕ) : ZMod p := ((∑ d ∈ (k ^ 2).divisors, d : ℕ) : ZMod p) * ((k : ZMod p) ^ 2)⁻¹

/-- The numbers sigma(k^2)/k^2 (k = 1, ..., n) are pairwise incongruent modulo p. -/
def Good (n p : ℕ) : Prop := Set.InjOn (s p) (Finset.Icc 1 n : Finset ℕ)

/-- The conjecture recorded in A263317. -/
theorem main : (∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧ n < p ∧ Good n p) ∧
    (∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < n ^ 2 ∧ Good n p) := by
  sorry

end OMA.S_oeis_a263317
