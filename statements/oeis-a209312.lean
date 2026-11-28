import Mathlib

/-!
# A209312: Number of practical numbers p<n with n-p and n+p both prime or both practical.

Source: https://oeis.org/A209312
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A209312 (Zhi-Wei Sun, Jan 19 2013): a(n)>0 for all n>2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4, ...). `a n` is the number of
  practical numbers p < n with n - p and n + p both prime or both practical, exactly as in the
  OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* n - p is an exact natural-number subtraction since p < n.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a209312

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A209312 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  Practical p ∧ p < n ∧ (((n - p).Prime ∧ (n + p).Prime) ∨ (Practical (n - p) ∧ Practical (n + p)))

/-- A209312: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A209312. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a209312
