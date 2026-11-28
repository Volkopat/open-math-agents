import Mathlib

/-!
# A209315: Number of ways to write 2n-1 = p+q with q practical, p and q-p both prime.

Source: https://oeis.org/A209315
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A209315 (Zhi-Wei Sun, Jan 19 2013): a(n)>0 for all n>8.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 1, 1, 0, 1, 2, 1, 2, ...). `a n` is the number of
  pairs (p, q) with 2n - 1 = p + q, q practical, and p and q - p both prime, exactly as in the
  OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* 2n - 1 = p + q is written as p + q + 1 = 2 * n to avoid subtraction.
* Natural-number subtraction is truncated: where the true value would be zero or negative the
  truncated value is 0, which is neither prime nor practical, so the condition is unchanged.
* Only the first sentence of the conjecture (the claim about this sequence) is formalized; the
  further claims in the comment are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a209315

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A209315 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q + 1 = 2 * n ∧ Practical q ∧ p.Prime ∧ (q - p).Prime

/-- A209315: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A209315. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a209315
