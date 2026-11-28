import Mathlib

/-!
# A155828: Number of integers k in {1,2,3,..,n} such that kn+1 is a square

Source: https://oeis.org/A155828
Credit: @ivillar

John W. Layman's sequence (offset 1): a(n) is the number of integers k with 1 ≤ k ≤ n such that
k*n + 1 is a perfect square.

Conjecture (John W. Layman, Jan 28 2009): All terms a(n) are of the form 2^m - 1.
(Zhi-Wei Sun noted in the entry that it reduces to counting the square roots of 1 modulo n.)
-/

namespace OMA.S_oeis_a155828

/-- a(n): the number of k in {1, ..., n} such that k*n + 1 is a square. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => IsSquare (k * n + 1))).card

/-- Layman's conjecture: every term is one less than a power of 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, a n = 2 ^ m - 1 := by
  sorry

end OMA.S_oeis_a155828
