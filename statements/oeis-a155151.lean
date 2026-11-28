import Mathlib

/-!
# A155151: Triangle T(n, k) = 4*n*k + 2*n + 2*k + 2, read by rows.

Source: https://oeis.org/A155151
Credit: @bnb9001

The triangle has rows `n ≥ 1` and entries `1 ≤ k ≤ n` (it begins 10; 16, 26; 22, 36, 50; ...).

Conjecture (Vincenzo Librandi, 2012): let p be a prime number. If 2^p belongs to the sequence,
then 2^p - 1 is not a Mersenne prime. Michel Marcus notes that the conjecture is true.
-/

namespace OMA.S_oeis_a155151

/-- The entry of the triangle in row `n`, column `k`. -/
def T (n k : ℕ) : ℕ := 4 * n * k + 2 * n + 2 * k + 2

/-- If `p` is prime and `2 ^ p = T n k` for some `1 ≤ k ≤ n`, then `2 ^ p - 1` is not prime. -/
theorem main : ∀ p : ℕ, p.Prime → (∃ n k : ℕ, 1 ≤ k ∧ k ≤ n ∧ T n k = 2 ^ p) →
    ¬ (2 ^ p - 1).Prime := by
  sorry

end OMA.S_oeis_a155151
