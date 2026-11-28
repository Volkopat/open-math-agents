import Mathlib

/-!
# OEIS A071537: multiplicative dependence and the nonprimes

Source: https://oeis.org/A071537 (offset 1).
Credit: @bnb9001

For each positive integer n, a(n) is the least integer m >= n for which there
are integers k_n, ..., k_m, with k_n nonzero, such that
n^(k_n) * (n+1)^(k_(n+1)) * ... * m^(k_m) = 1.
Negative exponents are interpreted in the rational numbers.

Conjecture: this is a permutation of the nonprimes A018252.
Max Alekseyev gave a proof on October 22, 2008.
Here the positive nonprimes include 1, as in the source sequence.
The statement asserts precisely that a is a bijection from the positive
integers onto the positive nonprimes.
-/

namespace OMA.S_oeis_a071537

open scoped BigOperators

def ProductRelation (n m : ℕ) : Prop := n ≤ m ∧
  ∃ k : ℕ → ℤ, k n ≠ 0 ∧ ∏ i ∈ Finset.Icc n m, (i : ℚ) ^ k i = 1

/-- The least admissible endpoint in the OEIS definition. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ProductRelation n m}

theorem main : Set.BijOn a {n | 0 < n} {s | 0 < s ∧ ¬ s.Prime} := by sorry

end OMA.S_oeis_a071537
