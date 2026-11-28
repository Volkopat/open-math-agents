import Mathlib

/-!
# A366048: For n >= 1, a(n) is the least k >= 1 such that 1/d(k) + ... + 1/d(k + n - 1) is an integer, d(i) = A000005(i).

Source: https://oeis.org/A366048
Credit: @keiichisince1986-bot

A366048 is the sequence `a(n)` named in the title. The entry states:
Conjecture: The sum 1/d(k) + ... + 1/d(k + n - 1) = C, C an integer, exists for all k >= 1, n >= 1.
(We formalize it as: a(n) exists for every n >= 1.)

Conventions:
- `d(i)` is the number of divisors of `i`: `(Nat.divisors i).card`. The sum is computed in `ℚ`.
-/

namespace OMA.S_oeis_a366048

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ ∃ C : ℕ,
      ∑ i ∈ Finset.range n, (1 : ℚ) / (Nat.divisors (k + i)).card = C := by
  sorry

end OMA.S_oeis_a366048
