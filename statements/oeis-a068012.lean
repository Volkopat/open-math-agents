import Mathlib

/-!
# A068012: Number of subsets of {1,2,3,...,n} that sum to 0 mod 6

Source: https://oeis.org/A068012
Credit: @ivillar

Antti Karttunen's sequence (offset 0): a(n) is the number of subsets S of {1, ..., n} (including
the empty set) whose element sum is divisible by 6.

Conjecture (David A. Corneth, Sep 13 2025): a(n) = 2*a(n-1) for n > 2 and 3 does not divide n-1.
a(3*k+1) = 2*a(3*k) - 2^(k-1), k >= 1, 3*k + 1 = n.
(The entry adds that the conjecture holds for 1 <= n <= 2000 and states a consequence.)
The second identity is stated over ℤ.
-/

namespace OMA.S_oeis_a068012

/-- a(n): the number of subsets of {1, ..., n} whose sum is divisible by 6 (offset 0). -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter (fun S => (∑ i ∈ S, i) % 6 = 0)).card

/-- Corneth's conjecture: a(n) = 2*a(n-1) for n > 2 with 3 not dividing n-1, and
a(3k+1) = 2*a(3k) - 2^(k-1) for k ≥ 1. -/
theorem main :
    (∀ n : ℕ, 2 < n → ¬ 3 ∣ n - 1 → a n = 2 * a (n - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → (a (3 * k + 1) : ℤ) = 2 * a (3 * k) - 2 ^ (k - 1)) := by
  sorry

end OMA.S_oeis_a068012
