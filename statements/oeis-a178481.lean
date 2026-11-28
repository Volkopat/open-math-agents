import Mathlib

/-!
# A178481: Number of steps of the map x -> A055566(x), starting at n, before reaching the end of the cycle.

Source: https://oeis.org/A178481
Credit: @avivorly

A178481(n) counts the steps of the map x ↦ (sum of the decimal digits of x^5) (A055566, as fixed by
R. J. Mathar's 2012 note in the entry), starting at n, before reaching a value already seen.

Generalization for the k-th powers and conjecture in the entry (Michel Lagneau, 2010): for each k ≥ 1,
iteration of taking the k-th powers of digit sums reaches a cycle. The entry's example for k = 17
iterates x ↦ (sum of the decimal digits of x^17): 3, 27, 117, 153, 189, 153, so it is stated here for
the map x ↦ (sum of the decimal digits of x^k), from every starting value: some two iterates coincide.
-/

namespace OMA.S_oeis_a178481

/-- The map x ↦ sum of the decimal digits of x^k. -/
def g (k x : ℕ) : ℕ := (Nat.digits 10 (x ^ k)).sum

theorem main : ∀ k : ℕ, 1 ≤ k → ∀ x : ℕ, ∃ i j : ℕ, i < j ∧ (g k)^[i] x = (g k)^[j] x := by
  sorry

end OMA.S_oeis_a178481
