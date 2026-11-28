import Mathlib

/-!
# A210452: Number of integers k<n with k-1 and k+1 both prime, and k and k*n both practical.

Source: https://oeis.org/A210452
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210452 (Zhi-Wei Sun, Jan 20 2013): a(n)>0 for all n>4.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 1, 2, ...). `a n` is the number of
  integers k < n with k - 1 and k + 1 both prime, and k and k*n both practical, exactly as in the
  OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* Natural-number subtraction is truncated: where the true value would be zero or negative the
  truncated value is 0, which is neither prime nor practical, so the condition is unchanged.
* Only the first sentence of the conjecture (the claim about this sequence) is formalized; the
  further claims in the comment are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a210452

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A210452 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  k < n ∧ (k - 1).Prime ∧ (k + 1).Prime ∧ Practical k ∧ Practical (k * n)

/-- A210452: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A210452. -/
theorem main : ∀ n : ℕ, 4 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a210452
