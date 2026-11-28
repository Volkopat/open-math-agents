import Mathlib

/-!
# OEIS A370102: a binomial-sum supercongruence

Source: https://oeis.org/A370102
Conjecture: Peter Bala, July 20, 2024.
Sequence: Seiichi Manyama, February 10, 2024.
Source text: OEIS Foundation, CC BY-SA 4.0.
Formalization credit: @natefelix1.

The defining sum runs over 0 <= k <= n. For n > 0 its binomial
arguments are nonnegative. At n = 0 this definition gives a(0) = 1,
agreeing with the source.
-/

namespace OMA.S_oeis_a370102

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (4 * n).choose k * (5 * n - k - 1).choose (n - k)

/-- The supercongruence conjecture for primes at least 5 and positive n and r. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      ∀ n r : ℕ, 0 < n → 0 < r →
        Nat.ModEq (p ^ (3 * r)) (a (n * p ^ r)) (a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a370102
