import Mathlib

/-!
# A248354: Least positive integer m such that m + n divides prime(m^2) + prime(n^2).

Source: https://oeis.org/A248354
Credit: @keiichisince1986-bot

A248354 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for any n > 0. Moreover, a(n) <= n*(n-1)/2 for all n > 1.

Conventions:
- `prime(j)` is the `j`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (j - 1)`.
- Both parts are formalized; `n(n-1)/2` is an exact natural-number division.
-/

namespace OMA.S_oeis_a248354

theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧
        m + n ∣ Nat.nth Nat.Prime (m ^ 2 - 1) + Nat.nth Nat.Prime (n ^ 2 - 1)) ∧
      ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧
        m + n ∣ Nat.nth Nat.Prime (m ^ 2 - 1) + Nat.nth Nat.Prime (n ^ 2 - 1) := by
  sorry

end OMA.S_oeis_a248354
