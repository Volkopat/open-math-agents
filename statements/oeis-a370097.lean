import Mathlib

/-!
# OEIS A370097: a binomial-sum supercongruence

Source: https://oeis.org/A370097
Conjecture: Peter Bala, August 8, 2026.
Sequence: Seiichi Manyama, February 10, 2024.
Source text: OEIS Foundation, CC BY-SA 4.0.
Formalization credit: @natefelix1.

The sequence is the sum over 0 <= k <= n of
binomial(3*n,k) * binomial(3*n-k-1,n-k).
For n > 0 these binomial arguments are nonnegative. At n = 0,
the definition below gives a(0) = 1, agreeing with the source.
-/

namespace OMA.S_oeis_a370097

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (3 * n).choose k * (3 * n - k - 1).choose (n - k)

/-- Bala's supercongruence, for primes at least 3 and positive n and r. -/
theorem main :
    ∀ p : ℕ, p.Prime → 3 ≤ p →
      ∀ n r : ℕ, 0 < n → 0 < r →
        Nat.ModEq (p ^ (3 * r)) (a (n * p ^ r)) (a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a370097
