import Mathlib

/-!
# A300984: factorization and the observed majority of primes

Source: https://oeis.org/A300984
Credit: @dwilfand-sys

The first assertion concerns individual members. The second counts distinct
odd prime factors represented among sequence values up to and including
10^m, following the finite set E in the entry. A majority means strictly
more than half. A082539 excludes primes with a smaller prime q for which
q+1 divides p+1.
-/

namespace OMA.S_oeis_a300984

def squarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

def nonsquarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ Squarefree d, d

def PrimeShape : Prop := ∀ n : ℕ, 0 < n → Squarefree (squarefreeSum n) →
    Squarefree (nonsquarefreeSum n) →
    ∃ p i j : ℕ, p.Prime ∧ n = 2^i * p^j

noncomputable def representedPrimes (bound : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (bound+1)).filter fun p ↦ p.Prime ∧ p ≠ 2 ∧
    ∃ n : ℕ, 0 < n ∧ n ≤ bound ∧ Squarefree (squarefreeSum n) ∧
      Squarefree (nonsquarefreeSum n) ∧ ∃ i j : ℕ, 0 < j ∧ n = 2^i * p^j

def isA082539 (p : ℕ) : Prop := p.Prime ∧ ∀ q : ℕ, q.Prime → q < p → ¬ q+1 ∣ p+1

def PrimeMajority : Prop := by
  classical
  exact ∀ m : ℕ, 7 < m →
    (representedPrimes (10^m)).card <
      2 * ((representedPrimes (10^m)).filter isA082539).card

theorem main : PrimeShape ∧ PrimeMajority := by
  sorry

end OMA.S_oeis_a300984
