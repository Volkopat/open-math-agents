import Mathlib

/-!
# A261653: Number of primes p < n such that  n-p-1 and n+p+1 are both prime or both practical.

Source: https://oeis.org/A261653
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A261653 (Zhi-Wei Sun, Aug 28 2015): a(n) > 0 for all n
> 6. Also, for any integer n > 2, there is a prime p < n such that n-(p-1) and n+(p-1) are both
prime or both practical.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 0, 1, 2, 2, 3, 2, 3, ...). `a n` is the number of
  primes p < n such that n - p - 1 and n + p + 1 are both prime or both practical, exactly as in
  the OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* For p < n the subtraction n - p - 1 is exact (its value 0, when p = n - 1, is neither prime nor
  practical), and n - (p - 1) is exact.
* Both sentences are formalized, as a conjunction.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a261653

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A261653 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (((n - p - 1).Prime ∧ (n + p + 1).Prime) ∨
  (Practical (n - p - 1) ∧ Practical (n + p + 1)))

/-- A261653: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A261653. -/
theorem main : (∀ n : ℕ, 6 < n → 0 < a n) ∧
    (∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (((n - (p - 1)).Prime ∧
    (n + (p - 1)).Prime) ∨
      (Practical (n - (p - 1)) ∧ Practical (n + (p - 1))))) := by
  sorry

end OMA.S_oeis_a261653
