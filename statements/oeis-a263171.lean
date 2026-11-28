import Mathlib

/-!
# A263171: Smallest prime starting a sequence of 4 consecutive odd primes such that the center of the symmetrical gaps is 2n.

Source: https://oeis.org/A263171
Credit: @keiichisince1986-bot

A263171 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for all n>0.

Conventions:
- Primes are indexed from `0` in Mathlib: `Nat.nth Nat.Prime i` is `prime(i + 1)`. Four consecutive odd primes are `Nat.nth Nat.Prime i, …, Nat.nth Nat.Prime (i + 3)` with `i ≥ 1`.
- Their gaps are symmetrical with center `2n` when the middle gap is `2n` and the first and last gaps are
  equal (for example `7, 11, 13, 17` for `n = 1`). Subtractions of increasing primes are exact.
-/

namespace OMA.S_oeis_a263171

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, 1 ≤ i ∧ Nat.nth Nat.Prime (i + 2) - Nat.nth Nat.Prime (i + 1) = 2 * n ∧
      Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i = Nat.nth Nat.Prime (i + 3) - Nat.nth Nat.Prime (i + 2) := by
  sorry

end OMA.S_oeis_a263171
