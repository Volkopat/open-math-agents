import Mathlib

/-!
# A209254: Number of ways to write 2n-1 = p+q with q practical, p and p^4+q^4 both prime.

Source: https://oeis.org/A209254
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A209254 (Zhi-Wei Sun, Jan 14 2013): a(n)>0 for all n>1.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, ...). `a n` is the number of
  pairs (p, q) with 2n - 1 = p + q, q practical, and p and p^4 + q^4 both prime, exactly as in the
  OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* 2n - 1 = p + q is written as p + q + 1 = 2 * n to avoid subtraction.
* Only the first sentence of the conjecture (the claim about this sequence) is formalized; the
  further claims in the comment are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a209254

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A209254 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q + 1 = 2 * n ∧ Practical q ∧ p.Prime ∧ (p ^ 4 + q ^ 4).Prime

/-- A209254: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A209254. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a209254
