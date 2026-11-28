import Mathlib

/-!
# A210480: Number of primes p<n with p-1 and p+1 both practical, and n-p prime or practical.

Source: https://oeis.org/A210480
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210480 (Zhi-Wei Sun, Jan 23 2013): a(n) > 0 for all n
> 3.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 2, ...). `a n` is the number of
  primes p < n with p - 1 and p + 1 both practical, and n - p prime or practical, exactly as in
  the OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* For a prime p < n the subtractions p - 1 and n - p are exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a210480

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A210480 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ Practical (p - 1) ∧ Practical (p + 1) ∧ ((n - p).Prime ∨ Practical (n - p))

/-- A210480: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A210480. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a210480
